//! The fields of a state that the stage of an expression decides when `at` is in it (spec §11.3, §11.6, §12.4; S-1161,
//! S-1166, S-1196; W7-09 U2s/t).
//!
//! What the spec fixes, and so what is checked:
//! - §11.3: an expression of the parameter kinds alone (constants, `init` and `block` inputs, their `let`s) is made at the
//!   stage its values decide, "`at` で付けたクロックによらず" (S-1196, S-1161 (2)). So `x + (n at sample) / m` (`n`, `m` of
//!   `block`) has a part of `block` that a faster stage reads, which is a hidden field `_out._hoist_0` (§11.3: "高い段で使う、
//!   遅い段の部分式の値は、状態の隠れたフィールドに置く"; §11.6: the name `_out._hoist_N`), and a `let` of such a value
//!   read at `sample` has a field of its own ("`sample` から参照される `block` のクロックの `let`", §12.4);
//! - §11.3: a condition with `at sample` is decided at `sample` (S-1166, S-1196), so the part of `block` in its branch is not
//!   made before (no hidden field for it), and an `if` with `at` in its condition is a `sample` expression as a whole
//!   (no field for the part), where the same `if` with no `at` has the fields of the part and of the guard (the control);
//! - §11.3, §11.9: a ratio read at `sample` over the parameter kinds (`(p at (sample / 4)) * 2.0` with `p` of `block`) is not a
//!   field of a tick (U2r2's fields), and `onsa check` passes it.
//!
//! Not asked: the number and the order of the fields beyond the names above, the sizes and the offsets, and the fields of
//! the inputs (`n`, `m`) that a stage no more reads.

use crate::test_support;

use test_support::*;

const SOURCE: &str = "\
pub flow in_a_division(x: I32 at sample, n: I32 at block, m: I32 at block) -> I32 at sample {
  x + (n at sample) / m
}

pub flow in_a_let(x: I32 at sample, n: I32 at block, m: I32 at block) -> I32 at sample {
  let q = (n at sample) / m
  x + q
}

pub flow plain_guard(x: F32 at sample, d: I32 at block) -> F32 at sample {
  if d != 0 { x * F32.round_from(100 / (d - 1)) } else { x }
}

pub flow guard_at_sample(x: F32 at sample, d: I32 at block) -> F32 at sample {
  if (d != 0) at sample { x * F32.round_from(100 / (d - 1)) } else { x }
}

pub flow guard_by_a_name(x: F32 at sample, d: I32 at block) -> F32 at sample {
  let g = (d != 0) at sample
  if g { x * F32.round_from(100 / (d - 1)) } else { x }
}

pub flow whole_if(x: F32 at sample, d: I32 at block) -> F32 at sample {
  let y = if (d != 0) at sample { 100 / (d - 1) } else { 0 }
  x + F32.round_from(y)
}

pub flow block_guard_at_block(x: F32 at sample, d: I32 at block) -> F32 at sample {
  if (d != 0) at block { x * F32.round_from(100 / (d - 1)) } else { x }
}
";

const RATIO: &str = "\
pub flow ratio_of_a_computation(x: F32 at sample, p: F32 at block) -> F32 at sample {
  x * (((p at (sample / 4)) * 2.0) at sample)
}

pub flow ratio_by_a_name(x: F32 at sample, p: F32 at block) -> F32 at sample {
  let m = p at (sample / 4)
  x * ((m * 2.0) at sample)
}
";

fn interface_of(source: &str) -> String {
    let d = Dir::pkg("at_stage");
    d.write("m.onsa", source);
    let out = run(d.root(), &["interface", "m.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("internal error"), "{}", out.stderr);
    out.stdout
}

/// The field lines (trimmed) of the `State` of the flow `name`: the indented lines after its `State` line, up to the next
/// item.
fn fields(text: &str, name: &str) -> Vec<String> {
    let head = format!("pub struct {name}.State");
    let mut lines = text.lines().skip_while(|l| !l.trim_start().starts_with(&head));
    assert!(lines.next().is_some(), "no State of `{name}`:\n{text}");
    lines.take_while(|l| l.starts_with("    ")).map(|l| l.trim().to_string()).collect()
}

fn hoisted(fields: &[String]) -> Vec<&String> {
    fields.iter().filter(|f| f.contains("._hoist_")).collect()
}

/// §11.3 (S-1161 (2), S-1196): `(n at sample) / m` is a part of `block` that `sample` reads: a hidden field.
#[test]
fn a_division_of_block_values_made_sample_with_at_is_a_hoisted_field() {
    let text = interface_of(SOURCE);
    let f = fields(&text, "in_a_division");
    assert!(f.iter().any(|l| l.starts_with("_out._hoist_0:")), "{f:?}");
}

/// §11.3, §12.4: the `let` of such a value, read by `sample`, has a field of its own.
#[test]
fn a_let_of_block_values_made_sample_with_at_has_a_field_of_its_own() {
    let text = interface_of(SOURCE);
    let f = fields(&text, "in_a_let");
    assert!(f.iter().any(|l| l.starts_with("q:")), "{f:?}");
}

/// §11.3 (S-1166, S-1196): the part in a branch under a condition of `sample` is made where it is reached, so it has no hidden field
/// (the part is `F32.round_from(100 / (d - 1))`, 4 bytes; the control with no `at` has it). Whether the condition `d != 0` itself is a
/// field (a part of `block` that `sample` reads, 1 byte) is not asked.
#[test]
fn a_condition_with_at_sample_has_no_hoisted_field_for_its_branch() {
    let text = interface_of(SOURCE);
    let control = fields(&text, "plain_guard");
    assert!(
        hoisted(&control).iter().any(|f| f.contains(": 4 bytes")),
        "the control has the field of the part: {control:?}"
    );
    for flow in ["guard_at_sample", "guard_by_a_name", "whole_if"] {
        let f = fields(&text, flow);
        assert!(
            !hoisted(&f).iter().any(|f| f.contains(": 4 bytes")),
            "`{flow}` has a hoisted field of the part: {f:?}"
        );
    }
}

/// §11.3: `at block` on a condition of `block` does not change it: the fields are the ones of the plain guard.
#[test]
fn a_condition_of_block_with_at_block_has_the_fields_of_the_plain_guard() {
    let text = interface_of(SOURCE);
    let plain = fields(&text, "plain_guard");
    let at = fields(&text, "block_guard_at_block");
    assert_eq!(hoisted(&plain).len(), hoisted(&at).len(), "{plain:?} {at:?}");
}

/// §11.3 (S-1196): a ratio read at `sample` over `block` values is accepted by `check` (no E0200 of the fields of a tick),
/// as a computation and by the name of a `let`.
#[test]
fn a_ratio_read_at_sample_over_block_values_passes_check() {
    let d = Dir::pkg("at_stage_ratio");
    d.write("m.onsa", RATIO);
    let out = run(d.root(), &["check", "m.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("E0200") && !out.stderr.contains("E0200"), "{}{}", out.stdout, out.stderr);
}
