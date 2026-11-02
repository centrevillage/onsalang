use super::*;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

mod scan;
use scan::{crate_sources, non_test_code, test_module_answers};

#[test]
fn names_are_distinct_and_details_fill_in_order() {
    let names: BTreeSet<&str> = Feature::ALL.iter().map(|f| f.name()).collect();
    assert_eq!(names.len(), Feature::ALL.len());
    assert_eq!(
        Feature::BulkInType.phrase(&["A", "B"]),
        "a flow with a bulk region (`A`) used inside another type (`B`)"
    );
    assert_eq!(Feature::Methods.list_phrase(), "the method `…` on `…`");
    assert_eq!(Feature::Methods.phrase(&["foo", "F32"]), "the method `foo` on `F32`");
    // another number of details than the phrase takes is an internal error
    for details in [&[][..], &["foo"][..], &["a", "b", "c"][..]] {
        let r = std::panic::catch_unwind(|| Feature::Methods.phrase(details));
        let bug = r.expect_err("a wrong number of details is a bug");
        assert!(bug.downcast_ref::<crate::internal::InternalBug>().is_some());
    }
    assert_eq!(Feature::Buf.message(&[]), "the C backend does not support `Buf` (heap buffers) in this version");
    let d = Feature::ValueMatch.diagnostic(Stage::Build, Span::empty(crate::FileId(0), 0), &[]);
    assert_eq!(d.code, Code::E0200);
    assert_eq!(d.notes.len(), 1);
    assert!(d.notes[0].span.is_none());
}

#[test]
fn explain_lists_every_feature_once() {
    let text = Code::E0200.explain().expect("E0200 has an explanation");
    assert!(!Feature::ALL.is_empty());
    for &f in Feature::ALL {
        let line = list_line(f);
        assert_eq!(text.lines().filter(|l| *l == line).count(), 1, "{line}");
    }
}

#[test]
fn the_scan_drops_comments_and_test_items_only() {
    let src = "#[cfg(test)] mod t;\nfn a() { let s = \"// {\"; let c = '{'; }\n\
               #[cfg(test)]\n#[allow(x)]\nfn b(x: [u8; 2]) {\n  if x { E0200 }\n}\n\
               /* E0200 */ const K: u32 = 1; // E0200\nfn d() { E0200 }\n";
    let (code, mods) = non_test_code(src);
    assert_eq!(mods, ["t"]);
    assert!(code.contains("fn a()") && code.contains("\"// {\"") && code.contains("const K"), "{code}");
    assert!(!code.contains("fn b") && !code.contains("mod t"), "{code}");
    assert_eq!(code.matches("E0200").count(), 1, "{code}");
    assert!(code.contains("fn d() { E0200 }"), "{code}");
}

/// Every E0200 is made here, and every feature is reported somewhere
/// (D-15): the other crates name a [`Feature`], never the code.
#[test]
fn every_e0200_comes_from_the_list_and_every_feature_is_reported() {
    let this = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut used = BTreeSet::new();
    let mut scanned = 0;
    for (f, _, code, test) in &crate_sources(Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()) {
        if f.starts_with(&this) || *test {
            continue;
        }
        scanned += 1;
        // the code, a name of it (`use onsa_diag::Code as C; C::E0200`)
        // or a text that claims it: only this list makes an E0200
        assert!(!code.contains("E0200"), "{} names E0200 itself: name a `Feature`", f.display());
        for (i, _) in code.match_indices("Feature::") {
            let rest = &code[i + "Feature::".len()..];
            let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
            used.insert(name);
        }
    }
    assert!(scanned > 50, "the scan found {scanned} source files only");
    let unused: Vec<&str> = Feature::ALL.iter().map(|f| f.name()).filter(|n| !used.contains(*n)).collect();
    assert!(unused.is_empty(), "features of the list that nothing reports: {unused:?}");
}

/// The answer of `onsa_cases --test-items` (RF-21): a line per file with a
/// test module, the lines from the attribute to the closing brace.
#[test]
fn the_answer_names_the_lines_of_the_test_modules() {
    let src = |p: &str, text: &str, test| (PathBuf::from(p), text.to_string(), String::new(), test);
    let text = "fn a() {}\n#[cfg(test)]\n#[allow(x)]\nmod t {\n    fn b() { \"}\"; }\n}\n#[cfg(test)]\nfn c() {}\n";
    let sources =
        [src("/r/a.rs", text, false), src("/r/b/tests.rs", "fn d() {}\n", true), src("/r/c.rs", "fn e() {}\n", false)];
    assert_eq!(test_module_answers(Path::new("/r"), &sources), ["a.rs 2 3 4 5 6", "b/tests.rs *"]);
}
