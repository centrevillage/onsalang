//! `onsa_cases --serve` (W4-18 U10c; X-16 (a), X-20 (ii)): the commands of
//! the gate's tools on texts read from the standard input, one request after
//! another in one process (`tools/batch.py` sends them), each answered as the
//! command answers on files of those names:
//!
//! ```text
//! request: <words>\t<n>\n, then n times <name>\t<bytes>\n<the bytes>
//! answer:  <exit code>\t<stdout bytes>\t<stderr bytes>\n<stdout><stderr>
//! ```
//!
//! The words are those of `onsa` (`check`, `fmt --check`, `diff --ast`, …):
//! read by `onsa_cli::Cli` and run by `onsa_cli::run_command` as `onsa` runs
//! them, the files read from the request ([`Texts`]); or `--fix-same-place`
//! and `--fmt`, the functions of those forms of `onsa_cases` (`--fmt` takes
//! one file). The names are the paths
//! the command shows (no tab, no newline). A request that cannot be read
//! ends the serving with an error: the tool sees the process end and runs
//! that input alone.

use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};

use clap::Parser;

/// A request: the words of the command and its files, each a name and bytes.
pub struct Request {
    pub words: String,
    pub files: Vec<(String, Vec<u8>)>,
}

/// What the command ends with: its exit code, standard output and standard error.
#[derive(Debug, PartialEq, Eq)]
pub struct Answer {
    pub code: u8,
    pub out: Vec<u8>,
    pub err: Vec<u8>,
}

/// Answer the requests of `input` on `output` until `input` ends; a request
/// that cannot be read is an error.
pub fn serve(input: &mut impl BufRead, output: &mut impl Write) -> std::io::Result<()> {
    while let Some(request) = read_request(input)? {
        write_answer(output, &answer(&request))?;
    }
    Ok(())
}

/// The next request of `input`, or None where it ends.
pub fn read_request(input: &mut impl BufRead) -> std::io::Result<Option<Request>> {
    let Some((words, n)) = head(input)? else { return Ok(None) };
    let mut files = Vec::new();
    for _ in 0..n {
        let (name, len) = head(input)?.ok_or_else(|| broken("the input ends inside it".into()))?;
        let mut bytes = vec![0; len];
        input.read_exact(&mut bytes)?;
        files.push((name, bytes));
    }
    Ok(Some(Request { words, files }))
}

/// A line `<text>\t<count>\n`, or None where the input ends.
fn head(input: &mut impl BufRead) -> std::io::Result<Option<(String, usize)>> {
    let mut line = String::new();
    if input.read_line(&mut line)? == 0 {
        return Ok(None);
    }
    let (text, count) = line
        .strip_suffix('\n')
        .and_then(|l| l.rsplit_once('\t'))
        .ok_or_else(|| broken(format!("the line `{}` is not `<text>\\t<count>`", line.escape_debug())))?;
    let count = count.parse().map_err(|_| broken(format!("`{}` is not a count", count.escape_debug())))?;
    Ok(Some((text.to_string(), count)))
}

fn broken(what: String) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, format!("a broken request: {what}"))
}

pub fn write_answer(output: &mut impl Write, a: &Answer) -> std::io::Result<()> {
    writeln!(output, "{}\t{}\t{}", a.code, a.out.len(), a.err.len())?;
    output.write_all(&a.out)?;
    output.write_all(&a.err)?;
    output.flush()
}

/// The answer to `request`.
pub fn answer(request: &Request) -> Answer {
    let texts = Texts(&request.files);
    let names = request.files.iter().map(|(name, _)| name.as_str());
    if request.words == "--fix-same-place" {
        let names: Vec<String> = names.map(String::from).collect();
        let read = |name: &str| crate::single_files::text_of(texts.bytes(Path::new(name)).map(<[u8]>::to_vec));
        let out = crate::single_files::fix_same_place(&names, read);
        return Answer { code: 0, out: out.into_bytes(), err: Vec::new() };
    }
    if request.words == "--fmt" {
        let [(name, _)] = request.files.as_slice() else {
            return Answer { code: 2, out: Vec::new(), err: b"onsa_cases --serve: --fmt takes one file\n".to_vec() };
        };
        return match crate::single_files::fmt(name, onsa_cli::Files::read(&texts, Path::new(name))) {
            Ok(out) => Answer { code: 0, out: out.into_bytes(), err: Vec::new() },
            Err((code, err)) => Answer { code, out: Vec::new(), err: err.into_bytes() },
        };
    }
    run_cli(std::iter::once("onsa").chain(request.words.split(' ')).chain(names), &texts)
}

/// What `onsa` with the arguments `args` (its name first) ends with, reading
/// `files`. `build` reads and writes files itself: it is not run.
fn run_cli<'a>(args: impl IntoIterator<Item = &'a str>, files: &(dyn onsa_cli::Files + Sync)) -> Answer {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let code = match onsa_cli::Cli::try_parse_from(args) {
        Ok(onsa_cli::Cli { command: onsa_cli::Command::Build { .. } }) => {
            err = b"onsa_cases --serve: `build` reads and writes files itself: not served\n".to_vec();
            2
        }
        Ok(cli) => onsa_cli::run_command(cli.command, &mut onsa_cli::Io::new(&mut out, &mut err, files)),
        // As `Cli::parse` prints and exits.
        Err(e) => {
            let text = e.render().to_string().into_bytes();
            if e.use_stderr() {
                err = text
            } else {
                out = text
            }
            u8::try_from(e.exit_code()).unwrap_or(2)
        }
    };
    Answer { code, out, err }
}

/// The files of a request: a name reads its bytes, as `onsa` reads the file
/// of that name, a `.onsa` file outside a package.
struct Texts<'a>(&'a [(String, Vec<u8>)]);

impl Texts<'_> {
    fn bytes(&self, path: &Path) -> std::io::Result<&[u8]> {
        let found = self.0.iter().find(|(name, _)| Path::new(name) == path);
        found.map(|(_, bytes)| bytes.as_slice()).ok_or_else(|| std::io::ErrorKind::NotFound.into())
    }
}

impl onsa_cli::Files for Texts<'_> {
    fn read(&self, path: &Path) -> std::io::Result<String> {
        // The error of `std::fs::read_to_string` on bytes that are not UTF-8.
        std::io::read_to_string(self.bytes(path)?)
    }

    fn canonical(&self, path: &Path) -> PathBuf {
        path.to_path_buf()
    }

    fn load(&self, path: Option<&Path>) -> Result<onsa_driver::Loaded, String> {
        let path = path.ok_or("onsa_cases --serve: the command needs the name of its file")?;
        let text = self.read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        onsa_driver::Loaded::from_input(onsa_driver::PackageInput::single_file(onsa_driver::slash_path(path), text))
    }

    fn replace(&self, _: &Path, _: &str) -> std::io::Result<()> {
        Err(std::io::Error::other("onsa_cases --serve writes no file"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(words: &str, files: &[(&str, &[u8])]) -> Vec<u8> {
        let mut r = format!("{words}\t{}\n", files.len()).into_bytes();
        for (name, bytes) in files {
            r.extend(format!("{name}\t{}\n", bytes.len()).bytes());
            r.extend(*bytes);
        }
        r
    }

    fn ask(words: &str, files: &[(&str, &[u8])]) -> Answer {
        let r = read_request(&mut request(words, files).as_slice()).expect("reads").expect("a request");
        answer(&r)
    }

    fn text(bytes: &[u8]) -> &str {
        std::str::from_utf8(bytes).expect("UTF-8")
    }

    /// The answers of `serve` on `input`, and its end.
    fn served(input: &[u8]) -> (Vec<Answer>, std::io::Result<()>) {
        let mut output = Vec::new();
        let end = serve(&mut &input[..], &mut output);
        let mut answers = Vec::new();
        let mut rest = output.as_slice();
        while let Some((code, n_out, n_err)) = rest.iter().position(|&b| b == b'\n').map(|i| {
            let head: Vec<usize> = text(&rest[..i]).split('\t').map(|n| n.parse().expect("a number")).collect();
            rest = &rest[i + 1..];
            (head[0], head[1], head[2])
        }) {
            let (out, tail) = rest.split_at(n_out);
            let (err, tail) = tail.split_at(n_err);
            answers.push(Answer { code: code as u8, out: out.to_vec(), err: err.to_vec() });
            rest = tail;
        }
        (answers, end)
    }

    const CLEAN: &[u8] = b"fn f(x: F32) -> F32 {\n  x\n}\n";
    const BAD: &[u8] = b"fn f(x: F32) -> F32 {\n  y\n}\n";
    const UNFORMATTED: &[u8] = b"fn f(x: F32) -> F32 {   x }\n";

    #[test]
    fn round_trip_of_requests_and_answers() {
        let mut input = request("check", &[("m.onsa", CLEAN)]);
        input.extend(request("diff --ast", &[("a.onsa", CLEAN), ("b.onsa", b"")]));
        let r = read_request(&mut input.as_slice()).expect("reads").expect("a request");
        assert_eq!((r.words.as_str(), r.files.len()), ("check", 1));
        assert_eq!((r.files[0].0.as_str(), r.files[0].1.as_slice()), ("m.onsa", CLEAN));
        let (answers, end) = served(&input);
        assert!(end.is_ok());
        assert_eq!(answers.len(), 2);
        assert_eq!(answers[0], Answer { code: 0, out: Vec::new(), err: Vec::new() });
        let mut written = Vec::new();
        write_answer(&mut written, &Answer { code: 1, out: b"ab".to_vec(), err: b"c\n".to_vec() }).expect("writes");
        assert_eq!(written, b"1\t2\t2\nabc\n");
    }

    #[test]
    fn each_command_answers_as_onsa_on_the_texts() {
        let a = ask("check", &[("m.onsa", BAD)]);
        assert_eq!(a.code, 1);
        assert!(text(&a.out).contains("m.onsa:2:3"), "{}", text(&a.out));
        assert_eq!(ask("check", &[("m.onsa", CLEAN)]).code, 0);
        let a = ask("fmt --check", &[("d/m.onsa", UNFORMATTED)]);
        assert_eq!((a.code, text(&a.out)), (1, "would reformat d/m.onsa\n"));
        assert_eq!(ask("fmt --check", &[("m.onsa", CLEAN)]).code, 0);
        assert_eq!(ask("fmt --check", &[("m.onsa", b"fn (")]).code, 2);
        let a = ask("diff --ast", &[("a.onsa", CLEAN), ("b.onsa", b"")]);
        assert_eq!((a.code, text(&a.out)), (1, "- fn f  (old:1)\n"));
        assert_eq!(ask("dump --levels", &[("m.onsa", CLEAN)]).code, 0);
        let a = ask("dump --cst", &[("m.onsa", CLEAN)]);
        assert_eq!(a.code, 0);
        assert!(!a.out.is_empty());
        let a = ask("--fix-same-place", &[("m.onsa", BAD), ("n.onsa", b"\xff")]);
        let items: serde_json::Value = serde_json::from_slice(&a.out).expect("JSON");
        assert_eq!(
            (a.code, items[0]["file"].as_str(), items[1]["unreadable"].as_str()),
            (0, Some("m.onsa"), Some("not UTF-8"))
        );
        // Read as `std::fs::read_to_string` reads a file that is not UTF-8.
        let a = ask("check", &[("m.onsa", b"\xff")]);
        assert_eq!((a.code, text(&a.err)), (2, "onsa: cannot read m.onsa: stream did not contain valid UTF-8\n"));
    }

    #[test]
    fn fmt_answers_as_onsa_cases_fmt() {
        // What `onsa fmt` would write, on the standard output, which `fmt --check` reads as formatted.
        let a = ask("--fmt", &[("d/m.onsa", UNFORMATTED)]);
        assert_eq!((a.code, a.err.is_empty()), (0, true));
        assert_ne!(a.out, UNFORMATTED);
        assert_eq!(ask("fmt --check", &[("d/m.onsa", &a.out)]).code, 0);
        assert_eq!(ask("--fmt", &[("m.onsa", CLEAN)]).out, CLEAN);
        // A syntax diagnostic on the standard error, as text, with the name of the file.
        let a = ask("--fmt", &[("d/m.onsa", b"fn (")]);
        assert_eq!((a.code, a.out.is_empty()), (2, true));
        assert!(text(&a.err).contains("d/m.onsa:1:"), "{}", text(&a.err));
        let a = ask("--fmt", &[("m.onsa", b"\xff")]);
        assert_eq!((a.code, text(&a.err)), (2, "onsa: cannot read m.onsa: stream did not contain valid UTF-8\n"));
        for files in [&[][..], &[("a.onsa", CLEAN), ("b.onsa", CLEAN)]] {
            let a = ask("--fmt", files);
            assert_eq!((a.code, text(&a.err)), (2, "onsa_cases --serve: --fmt takes one file\n"));
        }
    }

    #[test]
    fn what_onsa_refuses_and_what_is_not_served_answer_2() {
        let a = ask("frobnicate", &[("m.onsa", CLEAN)]);
        assert_eq!(a.code, 2);
        assert!(text(&a.err).contains("frobnicate"), "{}", text(&a.err));
        let a = ask("build", &[("m.onsa", CLEAN)]);
        assert_eq!((a.code, a.out.is_empty()), (2, true));
        assert_eq!(ask("fmt", &[("m.onsa", UNFORMATTED)]).code, 2);
        assert_eq!(ask("check", &[]).code, 2);
    }

    /// The files of a command whose reading panics: the panic of a stage.
    struct Panics;

    impl onsa_cli::Files for Panics {
        fn read(&self, _: &Path) -> std::io::Result<String> {
            panic!("the reading panics")
        }
        fn canonical(&self, path: &Path) -> PathBuf {
            path.to_path_buf()
        }
        fn load(&self, _: Option<&Path>) -> Result<onsa_driver::Loaded, String> {
            panic!("the loading panics")
        }
        fn replace(&self, _: &Path, _: &str) -> std::io::Result<()> {
            panic!("the writing panics")
        }
    }

    #[test]
    fn a_panic_is_an_internal_error_and_the_next_request_is_answered() {
        for args in [&["onsa", "check", "m.onsa"][..], &["onsa", "dump", "--levels", "m.onsa"]] {
            let a = run_cli(args.iter().copied(), &Panics);
            assert_eq!(a.code, 101);
            assert!(text(&a.err).starts_with("onsa: internal error:"), "{}", text(&a.err));
            assert!(text(&a.err).contains("panics"), "{}", text(&a.err));
        }
        assert_eq!(ask("check", &[("m.onsa", CLEAN)]).code, 0);
    }

    #[test]
    fn a_broken_request_ends_the_serving_after_the_answers_before_it() {
        let good = request("check", &[("m.onsa", CLEAN)]);
        for broken in
            [&b"check\n"[..], b"check\tx\n", b"check\t1\nm.onsa\t9\nfn", b"check\t1\nm.onsa 3\nabc", b"check\t1"]
        {
            let input = [good.as_slice(), broken].concat();
            let (answers, end) = served(&input);
            assert_eq!(answers.len(), 1, "{}", String::from_utf8_lossy(broken));
            assert!(end.is_err(), "{}", String::from_utf8_lossy(broken));
        }
    }
}
