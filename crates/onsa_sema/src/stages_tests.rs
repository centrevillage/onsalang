//! Unit tests of the record of the failed stages ([`crate::stages`], W4-06):
//! a stage that does not run reports nothing, which the reduced output of a
//! unit does not show (§18.1), so these read the diagnostics before the
//! choice.

use onsa_diag::{Code, FileId, Stage};

use crate::{Analysis, DefId, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let modules = vec![Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.to_string(),
        parsed: onsa_syntax::parse(FileId(0), src),
    }];
    analyze(&Package::new("t", modules, Vec::new()))
}

fn def(a: &Analysis, name: &str) -> DefId {
    DefId(a.defs.iter().position(|d| d.name == name).unwrap_or_else(|| panic!("no def `{name}`")) as u32)
}

/// The codes and stages of the diagnostics on the line `line` (from 1).
fn on_line(a: &Analysis, src: &str, line: usize) -> Vec<(Code, Stage)> {
    let line_of = |at: u32| src[..at as usize].matches('\n').count() + 1;
    a.diagnostics.iter().filter(|d| line_of(d.span.start) == line).map(|d| (d.code, d.stage)).collect()
}

#[test]
fn the_members_of_an_item_whose_heading_failed_take_its_stage() {
    // The heading of the `impl` has an error (E0412): the whole `impl` is one unit, so `b`
    // takes the E0302 of `a`, and its body is not typed; `d`, another unit, is.
    let src = "pub struct P {\n  x: I32,\n}\n\n\
               impl P[I32] {\n  fn a(self) -> I32 {\n    nope\n  }\n\n  \
               fn b(self) -> Bool {\n    let c: Bool = 1\n    c\n  }\n}\n\n\
               fn d() -> Bool {\n  let e: Bool = 1\n  e\n}\n";
    let a = check(src);
    assert!(on_line(&a, src, 5).contains(&(Code::E0412, Stage::Types)), "{:?}", a.diagnostics);
    assert_eq!(on_line(&a, src, 7), [(Code::E0302, Stage::Names)]);
    assert_eq!(a.failures.of_def(def(&a, "b")), Some(Stage::Names));
    assert!(a.failures.skips(def(&a, "b"), Stage::Types));
    assert_eq!(on_line(&a, src, 11), []);
    assert_eq!(a.failures.of_def(def(&a, "d")), Some(Stage::Types));
    assert_eq!(on_line(&a, src, 17), [(Code::E0401, Stage::Types)]);
}

#[test]
fn a_stage_runs_after_an_error_of_its_own_stage_and_not_of_an_earlier_one() {
    // The signature of `f` has an error of the types stage (E0412): the types stage still
    // checks its body (the same stage, `<`), the modes do not.
    let src = "pub struct P {\n  x: I32,\n}\n\n\
               fn f(p: P[I32]) -> Bool {\n  let b: Bool = 1\n  b\n}\n";
    let a = check(src);
    let f = def(&a, "f");
    assert_eq!(a.failures.of_def(f), Some(Stage::Types));
    assert!(!a.failures.skips(f, Stage::Types));
    assert!(a.failures.skips(f, Stage::Modes) && a.failures.skips(f, Stage::Effects));
    assert!(!a.failures.skips(f, Stage::Names));
    assert_eq!(on_line(&a, src, 6), [(Code::E0401, Stage::Types)]);
}

#[test]
fn a_unit_whose_modes_failed_gets_no_rt_and_no_effects() {
    // R-74, S-64: a use after a field was taken out (E0704) in both, whose rest needs `Alloc` to
    // drop; before W4-06 the effects (E0601) and the rt rules (E0901) ran on them too.
    let src = "pub struct Pair {\n  a: Buf[F32],\n  b: Buf[F32],\n}\n\n\
               pub fn take_field(move s: Pair) -> Buf[F32] { let x = move s.a\n  if x.len() > s.b.len() { x } else { x } }\n\n\
               pub rt fn take_field_rt(move s: Pair) -> Buf[F32] { let x = move s.a\n  if x.len() > s.b.len() { x } else { x } }\n";
    let a = check(src);
    let codes: Vec<(Code, Stage)> = a.diagnostics.iter().map(|d| (d.code, d.stage)).collect();
    assert_eq!(codes, [(Code::E0704, Stage::Modes), (Code::E0704, Stage::Modes)]);
    assert!(a.failures.skips(def(&a, "take_field_rt"), Stage::Effects));
}

#[test]
fn a_unit_whose_signature_has_a_name_error_gets_no_types_in_its_body() {
    // S-78: the E0302 of the signature stops the unit before the types stage; before W4-06 the
    // body was typed and reported the E0401.
    let src = "fn f(q: Nope) -> Bool {\n  let b: Bool = 1\n  b\n}\n";
    let a = check(src);
    let codes: Vec<(Code, Stage)> = a.diagnostics.iter().map(|d| (d.code, d.stage)).collect();
    assert_eq!(codes, [(Code::E0302, Stage::Names)]);
    assert!(a.failures.skips(def(&a, "f"), Stage::Types));
}
