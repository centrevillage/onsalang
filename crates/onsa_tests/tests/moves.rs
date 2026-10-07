//! Copy bookkeeping (T4-9, spec §12.7): `Poly.new` builds every `voice.State`
//! in place (no copy of 48 bytes or more), while returning one of two locals
//! must copy.

use std::path::Path;

use onsa_core::MoveKind;

fn lower(mut loaded: onsa_driver::Loaded) -> onsa_core::Module {
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)))
}

#[test]
fn poly_new_builds_states_in_place() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let module = lower(onsa_driver::load(&[root.join("tests/spec/examples/voice.onsa")]).unwrap());
    let big: Vec<_> = module.moves.iter().filter(|m| m.fn_name.ends_with("Poly.new") && m.bytes >= 48).collect();
    assert!(big.is_empty(), "unexpected copies in Poly.new: {big:?}");
}

#[test]
fn returning_one_of_two_locals_copies() {
    let input = onsa_driver::PackageInput {
        manifest: None,
        files: vec![onsa_driver::SourceFile {
            path: "pick.onsa".into(),
            text: r#"
pub flow v(x: Sig[F32]) -> Sig[F32] {
  delay(x, 16, 0.0)
}

pub fn pick(c: Bool) -> v.State {
  let a = v.init(v.Config {}, 48000.0)
  let b = v.init(v.Config {}, 48000.0)
  if c { a } else { b }
}

pub fn keep() -> v.State {
  let a = v.init(v.Config {}, 48000.0)
  a
}
"#
            .into(),
        }],
        root: None,
    };
    let module = lower(onsa_driver::Loaded::from_input(input));
    let pick: Vec<_> = module.moves.iter().filter(|m| m.fn_name.ends_with("pick")).collect();
    assert_eq!(pick.len(), 1, "{pick:?}");
    assert_eq!(pick[0].kind, MoveKind::Branch);
    assert!(pick[0].bytes >= 48, "{:?}", pick[0]);
    let keep: Vec<_> = module.moves.iter().filter(|m| m.fn_name.ends_with("keep")).collect();
    assert!(keep.is_empty(), "NRVO: {keep:?}");
}
