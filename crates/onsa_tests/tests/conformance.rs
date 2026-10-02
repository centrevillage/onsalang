//! Conformance (T4-7, spec §13.4): every flow of every `tests/conformance/*.onsa`
//! is run through the interpreter and through the generated C with the same
//! stimuli (impulse, silence, deterministic noise per `Sig` input; two blocks
//! of 2048 frames so `ctl` runs twice; `@param` defaults). Flows that reach a
//! transcendental primitive are compared within 2 ULP (S-14); the others must
//! match bit for bit. Skipped without a host `cc`.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use onsa_core::prim::Prim;
use onsa_core::walk::walk_block;
use onsa_core::{ExprKind, FlowMeta, FnId, Module, Ty, TypeDefKind};
use onsa_interp::{ArrayData, Interp, Proj, SpanRef, Value, slot};
use onsa_tests::c::emit_c;

const FRAMES: u32 = 4096;
const BLOCK: u32 = 2048;
const STIMULI: u32 = 3;

/// The same generator in Rust and in the C driver: 24-bit LCG output scaled
/// to [-0.5, 0.5), exact in `f32`.
fn stimulus(kind: u32, input_index: u32) -> Vec<f32> {
    let mut v = vec![0.0f32; FRAMES as usize];
    match kind {
        0 => v[0] = 1.0,
        1 => {}
        _ => {
            let mut x: u32 = 12345 + input_index * 7919;
            for s in v.iter_mut() {
                x = x.wrapping_mul(1664525).wrapping_add(1013904223);
                *s = ((x >> 8) as f32) / 16777216.0 - 0.5;
            }
        }
    }
    v
}

fn reaches_transcendental(m: &Module, meta: &FlowMeta) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<FnId> = vec![meta.fns.init, meta.fns.ctl, meta.fns.tick, meta.fns.process];
    let mut found = false;
    while let Some(f) = stack.pop() {
        if !seen.insert(f) {
            continue;
        }
        if let Some(b) = &m.fn_(f).body {
            walk_block(b, &mut |e| match &e.kind {
                ExprKind::Call { fn_, .. } => stack.push(*fn_),
                ExprKind::Prim { prim: Prim::Math(mf, _), .. } if !mf.is_exact() => found = true,
                _ => {}
            });
        }
    }
    found
}

fn param_defaults(meta: &FlowMeta) -> Vec<f32> {
    meta.params.iter().map(|(_, _, pm)| pm.as_ref().and_then(|p| p.default).unwrap_or(0.0) as f32).collect()
}

/// `(output name, channel count)`: 1 for a scalar / struct field, N for planar.
fn output_shape(meta: &FlowMeta) -> Vec<(String, u32)> {
    meta.outputs.iter().map(|(n, _, planar)| (n.clone(), planar.unwrap_or(1))).collect()
}

fn interp_run(module: &Module, meta: &FlowMeta) -> Vec<Vec<f32>> {
    let interp = Interp::new(module);
    let fns = meta.fns.clone();
    let params = Value::Struct(param_defaults(meta).into_iter().map(Value::F32).collect());
    let shape = output_shape(meta);
    let mut all = Vec::new();
    for k in 0..STIMULI {
        let state = slot(interp.call(fns.init, vec![Value::Struct(Vec::new()), Value::F32(48000.0)]).unwrap());
        let inputs: Vec<_> =
            (0..meta.sig_inputs.len()).map(|i| slot(Value::Array(ArrayData::F32(stimulus(k, i as u32))))).collect();
        let outputs: Vec<Vec<_>> = shape
            .iter()
            .map(|(_, ch)| (0..*ch).map(|_| slot(Value::Array(ArrayData::F32(vec![0.0; FRAMES as usize])))).collect())
            .collect();
        for b in 0..FRAMES / BLOCK {
            let span = |s: &onsa_interp::Slot| {
                Value::Span(SpanRef { root: s.clone(), projs: Vec::<Proj>::new(), start: b * BLOCK, len: BLOCK })
            };
            let mut args = vec![params.clone()];
            for i in &inputs {
                args.push(span(i));
            }
            for (o, (_, ch)) in outputs.iter().zip(&shape) {
                if *ch == 1 && !matches!(meta.outputs.iter().find(|(n, _, _)| n == &shape[0].0), Some((_, _, Some(_))))
                {
                    args.push(span(&o[0]));
                } else {
                    args.push(Value::Array(ArrayData::Any(o.iter().map(span).collect())));
                }
            }
            interp
                .call_inout(fns.process, &state, args)
                .unwrap_or_else(|p| panic!("{}: interpreter panic: {}", meta.name, p.message));
        }
        for o in &outputs {
            for ch in o {
                let v = ch.borrow();
                match &*v {
                    Value::Array(ArrayData::F32(xs)) => all.push(xs.clone()),
                    other => panic!("unexpected output {other:?}"),
                }
            }
        }
    }
    all
}

/// The C driver: same stimuli, `@param` defaults by bit pattern, two blocks.
fn c_driver(meta: &FlowMeta, sym: &str, upper: &str, bulk_size: u32) -> String {
    let mut d = String::new();
    let _ = writeln!(d, "#include \"{sym}.h\"\n#include <stdio.h>\n#include <string.h>");
    let n_in = meta.sig_inputs.len();
    let shape = output_shape(meta);
    for i in 0..n_in {
        let _ = writeln!(d, "static float in{i}[{FRAMES}];");
    }
    for (o, (_, ch)) in shape.iter().enumerate() {
        let _ = writeln!(d, "static float out{o}[{ch}][{FRAMES}];");
    }
    let _ = writeln!(d, "static unsigned char mem[{upper}_SIZE] __attribute__((aligned({upper}_ALIGN)));");
    if bulk_size > 0 {
        let _ = writeln!(d, "static unsigned char bulk[{upper}_BULK_SIZE] __attribute__((aligned(16)));");
    }
    let _ = writeln!(d, "int main(void) {{");
    let _ = writeln!(d, "  {sym}_params p;");
    let _ = writeln!(d, "  memset(&p, 0, sizeof p);");
    for ((name, _, _), v) in meta.params.iter().zip(param_defaults(meta)) {
        let _ = writeln!(d, "  p.{name} = onsa_from_bits_f32(0x{:08x}u);", v.to_bits());
    }
    let _ = writeln!(d, "  for (uint32_t k = 0; k < {STIMULI}; k++) {{");
    let _ = writeln!(d, "    {sym}* s = ({sym}*)mem;");
    let _ = writeln!(d, "    {sym}_init(s, {}, 48000.0f);", if bulk_size > 0 { "bulk" } else { "NULL" });
    for i in 0..n_in {
        let _ = writeln!(d, "    memset(in{i}, 0, sizeof in{i});");
        let _ = writeln!(d, "    if (k == 0) in{i}[0] = 1.0f;");
        let _ = writeln!(
            d,
            "    if (k == 2) {{ uint32_t x = 12345u + {i}u * 7919u; for (uint32_t n = 0; n < {FRAMES}; n++) {{ x = x * 1664525u + 1013904223u; in{i}[n] = (float)(x >> 8) / 16777216.0f - 0.5f; }} }}"
        );
    }
    for (o, _) in shape.iter().enumerate() {
        let _ = writeln!(d, "    memset(out{o}, 0, sizeof out{o});");
    }
    let _ = writeln!(d, "    for (uint32_t b = 0; b < {}; b++) {{", FRAMES / BLOCK);
    for (o, (_, ch)) in shape.iter().enumerate() {
        if *ch > 1 {
            let chans: Vec<String> = (0..*ch).map(|c| format!("out{o}[{c}] + b * {BLOCK}")).collect();
            let _ = writeln!(d, "      float* out{o}_ch[{ch}] = {{ {} }};", chans.join(", "));
        }
    }
    let mut args = vec!["s".to_string(), "&p".to_string()];
    for i in 0..n_in {
        args.push(format!("in{i} + b * {BLOCK}"));
    }
    for (o, (_, ch)) in shape.iter().enumerate() {
        if *ch > 1 {
            args.push(format!("out{o}_ch"));
        } else {
            args.push(format!("out{o}[0] + b * {BLOCK}"));
        }
    }
    let _ = writeln!(d, "      if ({sym}_process({}, {BLOCK}) != 0) return 3;", args.join(", "));
    let _ = writeln!(d, "    }}");
    for (o, (_, ch)) in shape.iter().enumerate() {
        let _ =
            writeln!(d, "    for (uint32_t c = 0; c < {ch}; c++) fwrite(out{o}[c], sizeof(float), {FRAMES}, stdout);");
    }
    let _ = writeln!(d, "  }}\n  return 0;\n}}");
    d
}

fn c_run(root: &Path, src: &str, meta: &FlowMeta, bulk: Option<u32>) -> Vec<f32> {
    let unit = emit_c(root, src, bulk, false);
    let short = meta.name.rsplit('.').next().unwrap();
    let sym = format!("onsa_{short}");
    let upper = sym.to_ascii_uppercase();
    let layout = onsa_core::flow_layout(&lower(root, src), meta.fns.state, bulk);
    let dir = std::env::temp_dir().join(format!("onsa_conf_{}_{short}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("onsa.h"), &unit.runtime_header).unwrap();
    for (h, t) in &unit.headers {
        std::fs::write(dir.join(h), t).unwrap();
    }
    let c = dir.join("unit.c");
    std::fs::write(&c, &unit.source).unwrap();
    let d = dir.join("driver.c");
    std::fs::write(&d, c_driver(meta, &sym, &upper, layout.bulk_size)).unwrap();
    let exe = dir.join("run");
    let out = Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-ffp-contract=off", "-fno-fast-math"])
        .arg("-I")
        .arg(&dir)
        .arg(&c)
        .arg(&d)
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(out.status.success(), "{}: cc failed:\n{}", meta.name, String::from_utf8_lossy(&out.stderr));
    let run = Command::new(&exe).output().unwrap();
    assert!(run.status.success(), "{}: driver failed with {}", meta.name, run.status);
    let _ = std::fs::remove_dir_all(&dir);
    run.stdout.chunks_exact(4).map(|b| f32::from_le_bytes([b[0], b[1], b[2], b[3]])).collect()
}

fn lower(root: &Path, src: &str) -> Module {
    let path = root.join(src);
    let mut loaded = onsa_driver::load(std::slice::from_ref(&path)).unwrap();
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    assert!(analyzed.diagnostics.is_empty(), "{src}: {}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    onsa_driver::lower_core(&analyzed).unwrap_or_else(|d| panic!("{src}: {}", onsa_diag::to_text(&loaded.sources, &d)))
}

fn ulp_diff(a: f32, b: f32) -> u32 {
    if a.to_bits() == b.to_bits() {
        return 0;
    }
    (a.to_bits() as i64 - b.to_bits() as i64).unsigned_abs() as u32
}

#[test]
fn c_matches_the_interpreter() {
    if Command::new("cc").arg("--version").output().is_err() {
        eprintln!("no `cc` on the PATH; skipping");
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files: Vec<PathBuf> = std::fs::read_dir(root.join("tests/conformance"))
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "onsa"))
        .collect();
    files.sort();
    assert!(!files.is_empty());
    let mut report = String::new();
    let mut failures = Vec::new();
    for file in &files {
        let src = file.strip_prefix(&root).unwrap().to_string_lossy().into_owned();
        let bulk = Some(4096);
        let module = {
            let path = root.join(&src);
            let mut loaded = onsa_driver::load(std::slice::from_ref(&path)).unwrap();
            let analyzed = onsa_driver::analyze_loaded(&mut loaded);
            assert!(
                analyzed.diagnostics.is_empty(),
                "{src}: {}",
                onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics)
            );
            let opts = onsa_core::LowerOptions { bulk_threshold: bulk, ..Default::default() };
            onsa_driver::lower_core_with(&analyzed, &opts).unwrap()
        };
        for meta in &module.flows {
            // Flows with `Init` inputs need a config the harness does not build.
            let config_fields = match &module.ty(meta.fns.config).kind {
                TypeDefKind::Struct { fields } => fields.len(),
                _ => 0,
            };
            if config_fields > 0 {
                continue;
            }
            if meta.outputs.iter().any(|(_, t, _)| *t != Ty::Float(onsa_core::FloatKind::F32)) {
                continue;
            }
            let exact = !reaches_transcendental(&module, meta);
            let i = interp_run(&module, meta);
            let c = c_run(&root, &src, meta, bulk);
            let flat: Vec<f32> = i.concat();
            assert_eq!(c.len(), flat.len(), "{}: sample count", meta.name);
            let mut worst = 0;
            let mut mismatches = 0;
            for (k, (a, b)) in c.iter().zip(&flat).enumerate() {
                let d = ulp_diff(*a, *b);
                if d > 0 {
                    mismatches += 1;
                    worst = worst.max(d);
                    if exact {
                        failures.push(format!("{}: sample {k} differs: C {a:?} vs interpreter {b:?}", meta.name));
                        break;
                    }
                }
            }
            if worst > 2 {
                failures.push(format!("{}: worst difference {worst} ULP exceeds the precision target", meta.name));
            }
            let _ = writeln!(
                report,
                "{}: {} samples, {} differ, max {worst} ULP ({})",
                meta.name,
                c.len(),
                mismatches,
                if exact { "bit-exact required" } else { "2 ULP tolerance" }
            );
        }
    }
    eprintln!("{report}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
