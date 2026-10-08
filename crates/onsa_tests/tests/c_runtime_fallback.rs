//! The portable integer checks of the internal runtime (`ONSA_HAS_BUILTIN_OVERFLOW 0`, spec §3.4, R-10):
//! the path a compiler without the overflow builtins takes, which no other check compiles (W2-09, the
//! carry-over 3 of W2-05/b).
//!
//! A small C program includes `onsa__runtime.h` as the backend writes it and compares `onsa_cadd_N`,
//! `onsa_csub_N`, `onsa_cmul_N` and `onsa_cdiv_N` of every integer type, on the values at and near the
//! limits, with the exact result (computed here, §3.4): in range, the value; out of range, `false`. The
//! program is built with the builtins (the control) and without, with gcc-15 and clang, under the
//! warnings of §13.4 with `-Werror`, and must print `ok <count>` with the count of the comparisons. It
//! ends by an exit code, never by a signal. Fails without `gcc-15` and `clang` on the PATH (Q-07).

use std::process::Command;

use onsa_tests::c;

const TYPES: &[(&str, &str, bool, u32)] = &[
    ("i8", "int8_t", true, 8),
    ("i16", "int16_t", true, 16),
    ("i32", "int32_t", true, 32),
    ("i64", "int64_t", true, 64),
    ("u8", "uint8_t", false, 8),
    ("u16", "uint16_t", false, 16),
    ("u32", "uint32_t", false, 32),
    ("u64", "uint64_t", false, 64),
];

/// The values of a type tried as operands: the limits, their neighbours, 0, ±1, ±2 and the halves.
fn values(signed: bool, bits: u32) -> Vec<i128> {
    let (lo, hi) = if signed { (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1) } else { (0, (1i128 << bits) - 1) };
    let mut v = vec![lo, lo + 1, lo + 2, hi, hi - 1, hi - 2, 0, 1, 2, hi / 2, hi / 2 + 1, lo / 2, lo / 2 - 1, -1, -2];
    v.retain(|x| *x >= lo && *x <= hi);
    v.sort();
    v.dedup();
    v
}

/// A C literal of `v` in the type `ct`.
fn lit(v: i128, ct: &str) -> String {
    if v < 0 { format!("(({ct})(-{}LL - 1))", -(v + 1)) } else { format!("(({ct}){v}ULL)") }
}

fn program() -> (String, usize) {
    let mut p = String::from(
        "#define ONSA_PANIC_TRAP\n#include \"onsa__runtime.h\"\n#include <stdio.h>\n\
         static int onsa_bad = 0;\n\
         static void onsa_check(const char* what, int got_ok, int same, int want_ok) {\n  \
         if (got_ok != want_ok || (want_ok && !same)) { printf(\"bad %s\\n\", what); onsa_bad++; }\n}\n\
         int main(void) {\n",
    );
    let mut count = 0;
    for (n, ct, signed, bits) in TYPES {
        let (lo, hi) =
            if *signed { (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1) } else { (0, (1i128 << bits) - 1) };
        let vs = values(*signed, *bits);
        for a in &vs {
            for b in &vs {
                for op in ["cadd", "csub", "cmul", "cdiv"] {
                    // The exact result (§3.4: division truncates toward zero); `None` when 128 bits do not hold it.
                    let exact = match op {
                        "cadd" => a.checked_add(*b),
                        "csub" => a.checked_sub(*b),
                        "cmul" => a.checked_mul(*b),
                        _ if *b == 0 => continue,
                        _ => a.checked_div(*b),
                    };
                    let want = exact.filter(|x| *x >= lo && *x <= hi);
                    let (la, lb) = (lit(*a, ct), lit(*b, ct));
                    let (want_ok, same) = match want {
                        Some(x) => (1, format!("r == {}", lit(x, ct))),
                        None => (0, "1".to_string()),
                    };
                    p.push_str(&format!(
                        "  {{ {ct} r = 0; int ok = onsa_{op}_{n}({la}, {lb}, &r); \
                         onsa_check(\"{op}_{n} {a} {b}\", ok, {same}, {want_ok}); }}\n"
                    ));
                    count += 1;
                }
            }
        }
    }
    p.push_str(&format!("  if (onsa_bad) return 1;\n  printf(\"ok {count}\\n\");\n  return 0;\n}}\n"));
    (p, count)
}

#[test]
fn the_portable_integer_checks_give_the_exact_results() {
    for cc in ["gcc-15", "clang"] {
        c::require(cc).unwrap_or_else(|e| panic!("{e}"));
    }
    let dir = c::scratch_dir("onsa_test", "runtime_fallback");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("onsa.h"), onsa_backend_c::PUBLIC_HEADER).unwrap();
    std::fs::write(dir.join(onsa_backend_c::INTERNAL_HEADER_NAME), onsa_backend_c::internal_header()).unwrap();
    let (source, count) = program();
    assert!(count > 1000, "{count} comparisons");
    std::fs::write(dir.join("fallback.c"), source).unwrap();
    for cc in ["gcc-15", "clang"] {
        for (define, label) in
            [("-DONSA_HAS_BUILTIN_OVERFLOW=0", "portable"), ("-DONSA_HAS_BUILTIN_OVERFLOW=1", "builtins")]
        {
            for level in ["-O0", "-O2"] {
                let exe = dir.join(format!("fallback_{label}"));
                let o = Command::new(cc)
                    .args(c::CFLAGS)
                    .args([level, define, "-I."])
                    .arg("fallback.c")
                    .arg("-o")
                    .arg(&exe)
                    .current_dir(&dir)
                    .output()
                    .unwrap();
                assert!(o.status.success(), "{cc} {level} {label}:\n{}", c::head(&String::from_utf8_lossy(&o.stderr)));
                let r = Command::new(&exe).output().unwrap();
                let out = String::from_utf8_lossy(&r.stdout);
                assert!(
                    r.status.code() == Some(0) && out.trim() == format!("ok {count}"),
                    "{cc} {level} {label}: {}\n{}",
                    r.status,
                    c::head(&out)
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
