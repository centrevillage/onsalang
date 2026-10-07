#![allow(unreachable_code)]
// Independent cross-check of tests/vectors against native Rust (W2-01). NOT a norm: nothing here goes into the data.
//
// Build (by tools/vectors/xcheck.py): rustc --edition 2021 -O -o xcheck xcheck.rs
// Run: ./xcheck FILE.tsv...     exit code 0: no mismatch, 1: mismatches, 2: bad input
//
// Each row is recomputed with Rust's own operators. Where Rust's meaning differs from the spec on purpose
// (see KNOWN DIVERGENCES below) the row is computed from the spec's definition in Rust's terms, and the number
// of rows where Rust's own answer differs is reported.
//
// KNOWN DIVERGENCES (counted and printed)
//   D1  `MIN % -1`, `MIN.rem_euclid(-1)` panic in Rust and `checked_rem` / `checked_rem_euclid` return None; the spec says 0 / Some(0) (3.4).
//   D2  `f32::min` / `f32::max` (and C's fmin / fmax) ignore a NaN operand; the spec propagates it (3.4, 13.4).
//   D3  `to_bits()` of a NaN returns the hardware's NaN bits; the spec says the positive quiet NaN (3.4, S-106).
//   D4  Rust has no panicking float -> integer conversion; `trunc_<T>` is decided from the range and NaN (3.3),
//       and `trunc_<T>_sat` is compared with Rust's saturating `as`.
use std::collections::BTreeMap;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static D1: AtomicUsize = AtomicUsize::new(0);
static D2: AtomicUsize = AtomicUsize::new(0);
static D3: AtomicUsize = AtomicUsize::new(0);

trait Val: Copy {
    fn parse(s: &str) -> Self;
    fn show(self) -> String;
}
macro_rules! int_val { ($($t:ty),*) => {$(
    impl Val for $t {
        fn parse(s: &str) -> Self { s.parse::<$t>().unwrap_or_else(|_| panic!("bad int {s}")) }
        fn show(self) -> String { self.to_string() }
    }
)*}}
int_val!(i8, i16, i32, i64, u8, u16, u32, u64);
impl Val for f32 {
    fn parse(s: &str) -> Self { f32::from_bits(u32::from_str_radix(&s[2..], 16).unwrap()) }
    fn show(self) -> String { if self.is_nan() { "nan".into() } else { format!("0x{:08x}", self.to_bits()) } }
}
impl Val for f64 {
    fn parse(s: &str) -> Self { f64::from_bits(u64::from_str_radix(&s[2..], 16).unwrap()) }
    fn show(self) -> String { if self.is_nan() { "nan".into() } else { format!("0x{:016x}", self.to_bits()) } }
}
fn show_opt<T: Val>(o: Option<T>) -> String { match o { Some(v) => format!("some:{}", v.show()), None => "none".into() } }
fn show_res<T: Val>(o: Option<T>) -> String { match o { Some(v) => v.show(), None => "panic".into() } }
fn b(x: bool) -> String { if x { "true".into() } else { "false".into() } }

trait Signed: Val { fn neg_c(self) -> Option<Self>; fn abs_c(self) -> Option<Self>; }
macro_rules! signed { ($($t:ty),*) => {$( impl Signed for $t { fn neg_c(self)->Option<Self>{self.checked_neg()} fn abs_c(self)->Option<Self>{self.checked_abs()} } )*}}
signed!(i8, i16, i32, i64);
macro_rules! unsigned_impl { ($($t:ty),*) => {$( impl Signed for $t { fn neg_c(self)->Option<Self>{panic!("neg on unsigned")} fn abs_c(self)->Option<Self>{panic!("abs on unsigned")} } )*}}
unsigned_impl!(u8, u16, u32, u64);
fn signed_dispatch<T: Signed>(op: &str, a: T) -> String {
    match op {
        "neg" => show_res(a.neg_c()),
        "abs" => show_res(a.abs_c()),
        "checked_neg" => show_opt(a.neg_c()),
        _ => panic!("unknown integer operation {op}"),
    }
}

macro_rules! int_eval { ($t:ident, $op:expr, $args:expr) => {{
    let a: $t = Val::parse($args[0]);
    let n = <$t>::BITS;
    let bb = || -> $t { Val::parse($args[1]) };
    let sh = || -> u32 { $args[1].parse::<u32>().unwrap() };
    match $op {
        "add" => show_res(a.checked_add(bb())),
        "sub" => show_res(a.checked_sub(bb())),
        "mul" => show_res(a.checked_mul(bb())),
        "div" => show_res(a.checked_div(bb())),
        "rem" => { let y = bb(); if y == 0 { "panic".into() } else {
            if a.checked_rem(y).is_none() { D1.fetch_add(1, Relaxed); }
            a.wrapping_rem(y).show() } }
        "wadd" => a.wrapping_add(bb()).show(),
        "wsub" => a.wrapping_sub(bb()).show(),
        "wmul" => a.wrapping_mul(bb()).show(),
        "sadd" => a.saturating_add(bb()).show(),
        "ssub" => a.saturating_sub(bb()).show(),
        "smul" => a.saturating_mul(bb()).show(),
        "div_euclid" => show_res(a.checked_div_euclid(bb())),
        "rem_euclid" => { let y = bb(); if y == 0 { "panic".into() } else {
            if a.checked_rem_euclid(y).is_none() { D1.fetch_add(1, Relaxed); }
            a.wrapping_rem_euclid(y).show() } }
        "and" => (a & bb()).show(), "or" => (a | bb()).show(), "xor" => (a ^ bb()).show(),
        "not" => (!a).show(),
        "eq" => b(a == bb()), "ne" => b(a != bb()), "lt" => b(a < bb()), "le" => b(a <= bb()), "gt" => b(a > bb()), "ge" => b(a >= bb()),
        "min" => { let y = bb(); (if y < a { y } else { a }).show() }
        "max" => { let y = bb(); (if a < y { y } else { a }).show() }
        "shl" => { let k = sh(); if k >= n { "panic".into() } else { a.wrapping_shl(k).show() } }
        "shr" => { let k = sh(); if k >= n { "panic".into() } else { a.wrapping_shr(k).show() } }
        "checked_add" => show_opt(a.checked_add(bb())),
        "checked_sub" => show_opt(a.checked_sub(bb())),
        "checked_mul" => show_opt(a.checked_mul(bb())),
        "checked_div" => show_opt(a.checked_div(bb())),
        "checked_rem" => { let y = bb(); if y != 0 && a.checked_rem(y).is_none() { D1.fetch_add(1, Relaxed); }
            show_opt(if y == 0 { None } else { Some(a.wrapping_rem(y)) }) }
        "checked_div_euclid" => show_opt(a.checked_div_euclid(bb())),
        "checked_rem_euclid" => { let y = bb(); if y != 0 && a.checked_rem_euclid(y).is_none() { D1.fetch_add(1, Relaxed); }
            show_opt(if y == 0 { None } else { Some(a.wrapping_rem_euclid(y)) }) }
        "checked_shl" => show_opt(a.checked_shl(sh())),
        "checked_shr" => show_opt(a.checked_shr(sh())),
        _ => signed_dispatch::<$t>($op, a),
    }
}}}

macro_rules! float_eval { ($t:ident, $bits:ident, $op:expr, $args:expr) => {{
    let a: $t = Val::parse($args[0]);
    let bb = || -> $t { Val::parse($args[1]) };
    let cc = || -> $t { Val::parse($args[2]) };
    match $op {
        "add" => (a + bb()).show(), "sub" => (a - bb()).show(), "mul" => (a * bb()).show(), "div" => (a / bb()).show(),
        "rem" => (a % bb()).show(),
        "eq" => b(a == bb()), "ne" => b(a != bb()), "lt" => b(a < bb()), "le" => b(a <= bb()), "gt" => b(a > bb()), "ge" => b(a >= bb()),
        "min" | "max" => {
            let y = bb();
            let native = if $op == "min" { a.min(y) } else { a.max(y) };
            let r = if a.is_nan() || y.is_nan() { <$t>::NAN }
                else if a == y { // zeros: -0.0 < 0.0
                    if $op == "min" { if a.is_sign_negative() { a } else { y } } else if a.is_sign_negative() { y } else { a }
                } else if ($op == "min") == (a < y) { a } else { y };
            if r.is_nan() && !native.is_nan() { D2.fetch_add(1, Relaxed); }
            r.show()
        }
        "neg" => (-a).show(),
        "sqrt" => a.sqrt().show(),
        "floor" => a.floor().show(), "ceil" => a.ceil().show(), "trunc" => a.trunc().show(),
        "round" => a.round_ties_even().show(),
        "abs" => a.abs().show(),
        "is_nan" => b(a.is_nan()), "is_finite" => b(a.is_finite()),
        // 3 operands: each operation is its own statement; Rust never contracts
        "expr_muladd" => { let m = a * bb(); (m + cc()).show() }
        "expr_mulsub" => { let m = a * bb(); (m - cc()).show() }
        "expr_add3_l" => { let s = a + bb(); (s + cc()).show() }
        "expr_add3_r" => { let s = bb() + cc(); (a + s).show() }
        "expr_interp" => { let (y, f) = (bb(), cc()); let om = 1.0 - f; let l = om * a; let r = f * y; (l + r).show() }
        _ => panic!("unknown float operation {}", $op),
    }
}}}
fn trunc_to<D: TryFrom<i128> + Val>(x: f64, sat: bool, lo: i128, hi: i128) -> String {
    if x.is_nan() { return if sat { D::try_from(0i128).ok().unwrap().show() } else { "panic".into() }; }
    let t = x.trunc();
    let ti = t as i128; // saturating: independent of the target range
    if lo <= ti && ti <= hi { return D::try_from(ti).ok().unwrap().show(); }
    if sat { return D::try_from(if ti < lo { lo } else { hi }).ok().unwrap().show(); }
    "panic".into()
}

macro_rules! conv_from_int { ($s:ident, $op:expr, $arg:expr, [$($d:ident),*], [$($f:ident),*]) => {{
    let x: $s = Val::parse($arg);
    $(
        if $op == concat!(stringify!($s), ".narrow_", stringify!($d)) { return show_opt($d::try_from(x).ok()); }
        if $op == concat!(stringify!($s), ".as_", stringify!($d)) { return ($d::try_from(x).unwrap()).show(); }
    )*
    $(
        if $op == concat!(stringify!($s), ".round_", stringify!($f)) { return (x as $f).show(); }
        if $op == concat!(stringify!($s), ".as_", stringify!($f)) { let y = x as $f; assert_eq!(y as i128, x as i128); return y.show(); }
    )*
    panic!("unknown conversion {}", $op)
}}}
macro_rules! conv_from_float { ($s:ident, $op:expr, $arg:expr, [$($d:ident),*], [$($f:ident),*]) => {{
    let x: $s = Val::parse($arg);
    $(
        if $op == concat!(stringify!($s), ".trunc_", stringify!($d)) { return trunc_to::<$d>(x as f64, false, $d::MIN as i128, $d::MAX as i128); }
        if $op == concat!(stringify!($s), ".trunc_", stringify!($d), "_sat") { return (x as $d).show(); } // Rust's saturating `as`
    )*
    $(
        if $op == concat!(stringify!($s), ".round_", stringify!($f)) || $op == concat!(stringify!($s), ".as_", stringify!($f)) { return (x as $f).show(); }
    )*
    panic!("unknown conversion {}", $op)
}}}

fn vdelay32(name: &str, args: &[&str]) -> String {
    let d: f32 = Val::parse(args[0]);
    let top: u32 = args[1].parse().unwrap();
    let m = top as f32;
    let dc = if d >= 1.0 { if d <= m { d } else { m } } else { 1.0 };
    let k = dc as u32; // saturating, and 1 <= dc <= MAX
    if name == "vdelay_k" { k.to_string() } else { (dc - k as f32).show() }
}
fn vdelay64(name: &str, args: &[&str]) -> String {
    let d: f64 = Val::parse(args[0]);
    let top: u32 = args[1].parse().unwrap();
    let m = top as f64;
    let dc = if d >= 1.0 { if d <= m { d } else { m } } else { 1.0 };
    let k = dc as u32;
    if name == "vdelay_k" { k.to_string() } else { (dc - k as f64).show() }
}

fn consts(ty: &str, name: &str) -> String {
    macro_rules! int { ($t:ident) => { match name {
        "ZERO" => (0 as $t).show(), "ONE" => (1 as $t).show(), "MIN" => $t::MIN.show(), "MAX" => $t::MAX.show(),
        "BITS" => $t::BITS.to_string(), _ => panic!("unknown constant {ty}.{name}") } } }
    match ty {
        "i8" => int!(i8), "i16" => int!(i16), "i32" => int!(i32), "i64" => int!(i64),
        "u8" => int!(u8), "u16" => int!(u16), "u32" => int!(u32), "u64" => int!(u64),
        "f32" => match name { "ZERO" => 0f32.show(), "ONE" => 1f32.show(), "MAX" => f32::MAX.show(), "EPSILON" => f32::EPSILON.show(),
            "INFINITY" => f32::INFINITY.show(), "NAN" => f32::NAN.show(), _ => panic!("unknown constant") },
        "f64" => match name { "ZERO" => 0f64.show(), "ONE" => 1f64.show(), "MAX" => f64::MAX.show(), "EPSILON" => f64::EPSILON.show(),
            "INFINITY" => f64::INFINITY.show(), "NAN" => f64::NAN.show(), _ => panic!("unknown constant") },
        _ => panic!(),
    }
}

fn eval(op: &str, args: &[&str]) -> String {
    let (ty, name) = op.split_once('.').unwrap();
    if name.chars().next().unwrap().is_ascii_uppercase() { return consts(ty, name); }
    if name.starts_with("vdelay_") { return if ty == "f32" { vdelay32(name, args) } else { vdelay64(name, args) }; }
    if name == "from_bits" {
        return if ty == "f32" { f32::from_bits(u32::parse(args[0])).show() } else { f64::from_bits(u64::parse(args[0])).show() };
    }
    if name == "to_bits" {
        // D3: the hardware's NaN bits are not the normal NaN in general; count the NaN rows where they differ
        let (nan, native, normal) = if ty == "f32" { let a = f32::parse(args[0]); (a.is_nan(), a.to_bits() as u64, 0x7FC00000u64) }
            else { let a = f64::parse(args[0]); (a.is_nan(), a.to_bits(), 0x7FF8000000000000u64) };
        if nan { if native != normal { D3.fetch_add(1, Relaxed); } return normal.to_string(); }
        return native.to_string();
    }
    if name.starts_with("as_") || name.starts_with("narrow_") || name.starts_with("trunc_") || name.starts_with("round_") {
        let f = args[0];
        return match ty {
            "i8" => conv_from_int!(i8, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "i16" => conv_from_int!(i16, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "i32" => conv_from_int!(i32, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "i64" => conv_from_int!(i64, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "u8" => conv_from_int!(u8, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "u16" => conv_from_int!(u16, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "u32" => conv_from_int!(u32, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "u64" => conv_from_int!(u64, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "f32" => conv_from_float!(f32, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            "f64" => conv_from_float!(f64, op, f, [i8, i16, i32, i64, u8, u16, u32, u64], [f32, f64]),
            _ => panic!("unknown type {ty}"),
        };
    }
    match ty {
        "i8" => int_eval!(i8, name, args), "i16" => int_eval!(i16, name, args),
        "i32" => int_eval!(i32, name, args), "i64" => int_eval!(i64, name, args),
        "u8" => int_eval!(u8, name, args), "u16" => int_eval!(u16, name, args),
        "u32" => int_eval!(u32, name, args), "u64" => int_eval!(u64, name, args),
        "f32" => float_eval!(f32, u32, name, args), "f64" => float_eval!(f64, u64, name, args),
        _ => panic!("unknown type {ty}"),
    }
}

fn main() {
    let files: Vec<String> = std::env::args().skip(1).collect();
    if files.is_empty() { eprintln!("usage: xcheck FILE.tsv..."); std::process::exit(2); }
    let mut stats: BTreeMap<String, (usize, usize, Vec<String>)> = BTreeMap::new();
    let mut held = 0usize;
    for p in &files {
        let text = fs::read_to_string(p).unwrap_or_else(|e| { eprintln!("{p}: {e}"); std::process::exit(2) });
        let (mut op, mut tier) = (String::new(), String::new());
        for (ln, line) in text.lines().enumerate() {
            if line.starts_with('#') || line.is_empty() { continue; }
            if let Some(h) = line.strip_prefix("@ ") {
                let mut it = h.split(' ');
                op = it.next().unwrap().to_string();
                tier = it.next().unwrap().to_string();
                continue;
            }
            let mut cols = line.split('\t');
            let a = cols.next().unwrap();
            let args: Vec<&str> = if a == "()" { vec![] } else { a.split(' ').collect() };
            let expect = cols.next().unwrap_or_else(|| { eprintln!("{p}:{}: no tab", ln + 1); std::process::exit(2) });
            if expect == "?" { held += 1; continue; }
            let got = eval(&op, &args);
            let ok = if expect.starts_with("panic:") { got == "panic" } else { got == expect };
            let e = stats.entry(format!("{op} {tier}")).or_insert((0, 0, vec![]));
            e.0 += 1;
            if !ok {
                e.1 += 1;
                if e.2.len() < 3 { e.2.push(format!("{p}:{} args=[{}] expect={} got={}", ln + 1, args.join(" "), expect, got)); }
            }
        }
    }
    let (mut rows, mut bad) = (0, 0);
    for (k, (n, m, ex)) in &stats {
        rows += n; bad += m;
        if *m > 0 { println!("MISMATCH {k}: {m}/{n}"); for e in ex { println!("    {e}"); } }
    }
    println!("rows {rows} mismatches {bad} held {held} sections {} D1 {} D2 {} D3 {}", stats.len(), D1.load(Relaxed), D2.load(Relaxed), D3.load(Relaxed));
    std::process::exit(if bad > 0 { 1 } else { 0 });
}
