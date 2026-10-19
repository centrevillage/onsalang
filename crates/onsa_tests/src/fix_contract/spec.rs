//! The `[[test.fix]]` entries of a case's fragment.

use serde::{Deserialize, Deserializer};

use onsa_diag::Code;

use crate::fragment::Mode;

/// A `[[test.fix]]` entry of a case's fragment: what one candidate leaves
/// after it, or what more it promises.
///
/// ```text
/// // [[test.fix]]
/// // at = "22:22"              # the original diagnostic ("src/a.onsa:22:22" in a package)
/// // code = "E0020"
/// // candidate = 1
/// // leaves = ["22:30 E0020"]  # after the candidate, in the touched units and in those clean before it (default: none)
/// // clean = true              # the check after it reports nothing at all (S-253)
/// // same_code = true          # the tokens but comments and the line breaks between them stay (S-247)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixSpec {
    pub at: String,
    pub code: String,
    pub candidate: u32,
    pub leaves: Vec<String>,
    pub clean: bool,
    pub same_code: bool,
    /// The line of the entry in the file ([`locate`]).
    pub line: usize,
    pub(super) at_offset: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSpec {
    at: String,
    code: String,
    candidate: u32,
    #[serde(default)]
    leaves: Vec<String>,
    #[serde(default)]
    clean: bool,
    #[serde(default)]
    same_code: bool,
}

/// Read `[[test.fix]]`, keeping where each entry starts.
pub fn de_specs<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<FixSpec>, D::Error> {
    let raw: Vec<toml::Spanned<RawSpec>> = Vec::deserialize(d)?;
    Ok(raw
        .into_iter()
        .map(|r| {
            let at_offset = r.span().start;
            let r = r.into_inner();
            FixSpec {
                at: r.at,
                code: r.code,
                candidate: r.candidate,
                leaves: r.leaves,
                clean: r.clean,
                same_code: r.same_code,
                line: 0,
                at_offset,
            }
        })
        .collect())
}

/// Turn the offsets of [`de_specs`] into lines of `toml_text` (which keeps the
/// lines of the file).
pub fn locate(specs: &mut [FixSpec], toml_text: &str) {
    for s in specs {
        s.line = toml_text[..s.at_offset.min(toml_text.len())].matches('\n').count() + 1;
    }
}

/// A place in a case: the file as the case's source map names it (`None`: the
/// one file of a single-file case), the line and the column (from 1).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Place {
    pub file: Option<String>,
    pub line: u32,
    pub col: u32,
}

impl Place {
    /// `<line>:<col>` or `<file>:<line>:<col>`.
    pub fn parse(s: &str) -> Result<Place, String> {
        let bad = || format!("`{s}` is not `<line>:<col>` or `<file>:<line>:<col>` (from 1)");
        let mut parts = s.rsplitn(3, ':');
        let col = parts.next().ok_or_else(bad)?;
        let line = parts.next().ok_or_else(bad)?;
        let file = parts.next();
        let num = |t: &str| -> Result<u32, String> {
            if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) || t.starts_with('0') {
                return Err(bad());
            }
            t.parse().map_err(|_| bad())
        };
        if file.is_some_and(|f| f.is_empty() || f.trim() != f) {
            return Err(bad());
        }
        Ok(Place { file: file.map(str::to_string), line: num(line)?, col: num(col)? })
    }

    pub(super) fn show(&self) -> String {
        match &self.file {
            Some(f) => format!("{f}:{}:{}", self.line, self.col),
            None => format!("{}:{}", self.line, self.col),
        }
    }
}

/// A `leaves` item: `<place> <code>`.
pub(super) fn parse_leaf(s: &str) -> Result<(Place, Code), String> {
    let (place, code) = s.split_once(' ').ok_or_else(|| format!("`{s}` is not `<line>:<col> <code>`"))?;
    let code = Code::parse(code).ok_or_else(|| format!("`{s}`: unknown code `{code}`"))?;
    Ok((Place::parse(place)?, code))
}

/// The checks of the entries that need no run (an error of the case).
pub fn check_specs(specs: &[FixSpec], mode: Mode) -> Result<(), String> {
    if let Some(s) = specs.first()
        && matches!(mode, Mode::None | Mode::Parse)
    {
        return Err(format!(
            "line {}: [[test.fix]] needs `mode = \"check\"` or `\"test\"` (not {mode:?}): the candidates are checked \
             again only there",
            s.line
        ));
    }
    for (i, s) in specs.iter().enumerate() {
        let at = |m: String| format!("line {}: [[test.fix]]: {m}", s.line);
        Place::parse(&s.at).map_err(|e| at(format!("at: {e}")))?;
        if Code::parse(&s.code).is_none() {
            return Err(at(format!("code: unknown code `{}`", s.code)));
        }
        if s.candidate == 0 {
            return Err(at("candidate: the candidates count from 1".into()));
        }
        let mut leaves = Vec::new();
        for l in &s.leaves {
            let leaf = parse_leaf(l).map_err(|e| at(format!("leaves: {e}")))?;
            if leaves.contains(&leaf) {
                return Err(at(format!("leaves: `{l}` is written twice")));
            }
            leaves.push(leaf);
        }
        if s.clean && !s.leaves.is_empty() {
            return Err(at("`clean` leaves nothing at all; it cannot have `leaves`".into()));
        }
        if s.leaves.is_empty() && !s.clean && !s.same_code {
            return Err(at(
                "the entry says only the default (nothing left in the touched units); write `leaves`, `clean` or \
                 `same_code`, or remove it"
                    .into(),
            ));
        }
        if let Some(o) = specs[..i].iter().find(|o| o.at == s.at && o.code == s.code && o.candidate == s.candidate) {
            return Err(at(format!("the same candidate as the entry on line {}", o.line)));
        }
    }
    Ok(())
}
