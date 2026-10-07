//! Unit tests for T3-13 (E0601).

use onsa_diag::{Code, FileId};

use crate::{Analysis, Module, Package, analyze};

fn check(src: &str) -> Analysis {
    let m =
        Module { path: "main".into(), file: FileId(0), text: src.into(), parsed: onsa_syntax::parse(FileId(0), src) };
    analyze(&Package { name: "t".into(), modules: vec![m], deps: Vec::new(), is_std: false })
}

fn codes(a: &Analysis) -> Vec<Code> {
    let mut v: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
    v.sort();
    v
}

#[test]
fn calling_an_alloc_fn_needs_alloc_in_the_row() {
    let src = "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub fn bad() -> U32 { mk(4).len() }\n";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0601]);
    let d = &a.diagnostics[0];
    assert_eq!(d.found.as_deref(), Some("bad() -> U32"));
    assert_eq!(d.fixes.len(), 1);
    assert_eq!(crate::fixed_region(src, d, 0), "bad() -> U32 uses {Alloc}");
    assert!(d.notes[0].message.contains("calls `mk`"));
}

#[test]
fn alloc_row_test_body_and_rt_are_fine_or_other_codes() {
    // With the row: fine.
    let a = check(
        "pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub fn ok() -> U32 uses {Alloc} { mk(4).len() }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // A test body gets `Alloc` from the runner (D-08).
    let a =
        check("pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\ntest \"t\" { assert mk(4).len() == 4 }\n");
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    // An rt function reports E0901, not E0601.
    let a =
        check("pub fn mk(n: U32) -> Buf[F32] uses {Alloc} { Buf.zeroed(n) }\npub rt fn r() -> U32 { mk(4).len() }\n");
    assert_eq!(codes(&a), vec![Code::E0901]);
}

#[test]
fn zeroed_interpolation_and_drops() {
    let a = check("pub fn z() -> U32 { let b: Buf[F32] = Buf.zeroed(4)\n b.len() }\n");
    assert_eq!(codes(&a), vec![Code::E0601]);
    let a = check("pub fn owns(move b: Buf[F32]) -> U32 { b.len() }\n");
    assert_eq!(codes(&a), vec![Code::E0601]);
    // Moving the value on is not a drop.
    let a = check(
        "pub fn take(move b: Buf[F32]) -> U32 uses {Alloc} { b.len() }\npub fn pass(move b: Buf[F32]) -> U32 uses {Alloc} { take(move b) }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
}
