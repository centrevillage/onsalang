//! What a module keeps of the parser's result ([`ParsedAst`]) through
//! `postcard`, the form of the std compiled into the binary (W5-19): what is
//! read back is what the parser made, and the same input writes the same
//! bytes (a build that can be repeated).

use onsa_diag::{FileId, SHARED_BASE};

use crate::ParsedAst;
use crate::cst_tests::{onsa_files, root_dir};

/// What the tests compare: every field of [`ParsedAst`].
fn shown(p: &ParsedAst) -> String {
    format!("{p:?}")
}

/// The bytes of `p`, read back whole: nothing of them is left unread.
fn read_back(p: &ParsedAst) -> (Vec<u8>, ParsedAst) {
    let bytes = postcard::to_stdvec(p).unwrap();
    let (back, rest): (ParsedAst, &[u8]) = postcard::take_from_bytes(&bytes).unwrap();
    assert!(rest.is_empty(), "{} bytes left unread", rest.len());
    (bytes, back)
}

/// The files of the std in the order of their ids (`SharedFiles::new`).
fn std_files() -> Vec<(FileId, String, String)> {
    let root = root_dir();
    let mut files = Vec::new();
    onsa_files(&root.join("std"), &root, &mut files);
    assert!(!files.is_empty(), "no file in the std");
    let file = |(i, (name, text)): (usize, (String, String))| (FileId(SHARED_BASE + i as u32), name, text);
    files.into_iter().enumerate().map(file).collect()
}

#[test]
fn the_parsed_std_reads_back_the_same_and_writes_the_same_bytes() {
    onsa_diag::stack::run(|| {
        for (file, name, text) in std_files() {
            let (parsed, _) = crate::parse(file, &text).split();
            assert!(parsed.diagnostics.is_empty(), "{name}: {:?}", parsed.diagnostics);
            let (bytes, back) = read_back(&parsed);
            assert_eq!(shown(&back), shown(&parsed), "{name}: not the same after reading back");
            let (again, _) = read_back(&crate::parse(file, &text).split().0);
            assert!(bytes == again, "{name}: two writes of one input differ");
        }
    });
}

/// The std has no diagnostic, and a file with errors holds what it has not:
/// the diagnostics with their candidates and notes, the unfinished nodes.
#[test]
fn a_file_with_errors_reads_back_the_same() {
    let sources =
        ["fn f(a: I32 {\n", "fn f() {\n    let x = 1;\n    x = ;\n}\n", "if x { y } else z\n", "x = 1 + * 2\n"];
    let (mut with_fix, mut with_note) = (false, false);
    for src in sources {
        let (parsed, _) = crate::parse(FileId(0), src).split();
        assert!(!parsed.diagnostics.is_empty(), "{src:?}: no diagnostic");
        with_fix |= parsed.diagnostics.iter().any(|d| !d.fixes.is_empty());
        with_note |= parsed.diagnostics.iter().any(|d| !d.notes.is_empty());
        let (_, back) = read_back(&parsed);
        assert_eq!(shown(&back), shown(&parsed), "{src:?}: not the same after reading back");
    }
    assert!(with_fix && with_note, "no source had a candidate ({with_fix}) or a note ({with_note})");
}
