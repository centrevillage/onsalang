//! Unit tests of the signatures: the order of the declarations (the
//! aliases, the constants and the cycles, §4.4), the members of an `impl`
//! and of a flow, and the generics and their bounds.

use std::collections::{BTreeSet, HashSet};

use onsa_diag::{Code, FileId};

use crate::analyze;
use crate::def::DefKind;
use crate::tests::{check, codes, def, pkg};
use crate::ty::{Len, Ty};

/// A chain of 20 000 aliases (R-298) is lowered in the order of the
/// declarations, sinks first, each once: no lowering recurses through the
/// chain, so the check ends with no diagnostic (an alias adds nothing to the
/// depth, §4.4), on the stack of a command (`rules/common.md` 3.2: it ended by
/// a signal before W4-05 U2).
#[test]
fn a_chain_of_twenty_thousand_aliases_ends() {
    let mut src: String = (0..20_000).map(|i| format!("type A{i} = A{}\n", i + 1)).collect();
    src.push_str("type A20000 = F32\npub fn f(x: A0) -> A0 { x }\n");
    let run = move || codes(&check(&src));
    assert_eq!(onsa_diag::stack::spawn("t", run).unwrap().join().unwrap(), Vec::<Code>::new());
}

/// The same chain under an `impl` of its head (E0307, whose members are of
/// `S`, S-748) written before it: its constant is lowered after the chain
/// (the edge to its heading), and `A0.M` reads the member through the heads
/// of the aliases (R-299), with no recursion.
#[test]
fn an_impl_of_the_head_of_a_chain_of_twenty_thousand_aliases_ends() {
    let mut src = String::from("pub struct S { x: I32 }\nimpl A0 {\n  pub const N: [F32; S.M] = [0.0; 2]\n}\n");
    src.extend((0..20_000).map(|i| format!("type A{i} = A{}\n", i + 1)));
    src.push_str("type A20000 = S\nimpl S {\n  pub const M: U32 = 2\n}\npub type Row = [F32; A0.M]\n");
    let run = move || codes(&check(&src));
    assert_eq!(onsa_diag::stack::spawn("t", run).unwrap().join().unwrap(), vec![Code::E0307]);
}

/// A constant after a function of its name (§6.2, R-307): the E0304 is at
/// the constant, the later, and its E0320 (§2.3) at the same name is not the
/// one of the unit (§18.1: E0304, the smaller code). The parser reports the
/// E0320 too, so a case cannot mark it (`impl_member_clash_const_fn.onsa`).
#[test]
fn a_constant_after_a_function_of_its_name_is_the_e0304_alone() {
    let src = "pub struct P { x: I32 }\nimpl P {\n  pub fn a(self) -> I32 { 1 }\n  pub const a: I32 = 2\n}\n";
    let a = check(src);
    assert_eq!(codes(&a), vec![Code::E0304]);
    assert_eq!(a.diagnostics[0].span.start as usize, src.find("a: I32").unwrap());
}

#[test]
fn generics_and_bounds() {
    let a = check(
        "pub fn clamp[T: PartialOrd](x: T, lo: T, hi: T) -> T { x }\npub struct Ring[T, const N: U32] { data: [T; N], head: U32 }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let clamp = a.def(def(&a, "clamp")).as_fn().unwrap();
    assert_eq!(clamp.generics.len(), 1);
    assert!(matches!(a.types.get(clamp.params[0].ty), Ty::Param(0)));
    let ring = a.def(def(&a, "Ring")).as_struct().unwrap();
    assert_eq!(ring.generics.len(), 2);
    match &ring.fields {
        crate::def::Fields::Named(fs) => assert!(matches!(a.types.get(fs[0].ty), Ty::Array(_, Len::Param(1)))),
        _ => panic!(),
    }
    let a = check("pub fn f[T: Iter](x: T) -> T { x }\n");
    assert_eq!(codes(&a), vec![Code::E0200]);
    let a = check("pub fn f[const N: I32]() {}\n");
    assert_eq!(codes(&a), vec![Code::E0200]);
}

#[test]
fn flow_namespace_items() {
    let a = check(
        "pub flow voice(@param(min: 0.0, max: 1.0, default: 0.5) gain: F32 at block, time: F32 at init) -> F32 at sample { 1.0 }\n\
         pub flow echo(x: F32 at sample, t: F32 at block) -> F32 at sample { x }\n\
         pub struct Poly { voices: [voice.State; 4], p: voice.Params }\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let voice = a.def(def(&a, "voice")).as_flow().unwrap();
    let names: Vec<&str> = voice.members.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        vec![
            "State",
            "Config",
            "Params",
            "Out",
            "SIZE",
            "BULK_SIZE",
            "init",
            "reset",
            "process",
            "render",
            "params_default"
        ]
    );
    let echo = a.def(def(&a, "echo")).as_flow().unwrap();
    let names: Vec<&str> = echo.members.iter().map(|(n, _)| n.as_str()).collect();
    assert!(names.contains(&"process_inplace") && !names.contains(&"params_default"));
    let render = echo.members.iter().find(|(n, _)| n == "render").map(|(_, d)| a.def(*d).as_fn().unwrap()).unwrap();
    assert!(render.effects.alloc);
    assert_eq!(
        render.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
        vec!["cfg", "params", "x", "sample_rate"]
    );
    let process = voice.members.iter().find(|(n, _)| n == "process").map(|(_, d)| a.def(*d).as_fn().unwrap()).unwrap();
    assert_eq!(process.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), vec!["s", "params", "out"]);
    assert!(process.rt);
    assert_eq!(voice.inputs[0].param.as_ref().unwrap().default, Some(0.5));
}

#[test]
fn impl_registers_associated_items() {
    let a = check(
        "pub struct P { x: F32 }\nimpl P {\n  pub fn new(x: F32) -> P { P { x: x } }\n  pub rt fn norm(self) -> F32 { self.x }\n  const ZERO: F32 = 0.0\n}\n",
    );
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let p = def(&a, "P");
    let assoc = &a.modules.assoc[&p];
    assert_eq!(assoc.len(), 3);
    let norm = a.def(assoc["norm"]).as_fn().unwrap();
    assert_eq!(norm.self_mode, Some(onsa_syntax::ast::Mode::Borrow));
    assert!(norm.rt);
    assert!(matches!(a.def(assoc["ZERO"]).kind, DefKind::Const(_)));
}

/// A length reads a constant of the type `U32` alone (§4.5, E0401), the
/// constant of the module or a member of an `impl`, of its type written or
/// through an alias, written before or after what reads it: the constants
/// are lowered in the order of the declarations (W4-05 U2/i3, B-1).
#[test]
fn a_length_reads_the_type_of_a_constant_wherever_it_is_declared() {
    let readers = [
        "type A = [F32; R]",
        "const C: [U8; R] = [0, 0, 0]",
        "struct Q { a: [F32; R] }",
        "fn f(a: [F32; R]) -> I32 { 0 }",
    ];
    for reader in readers {
        for member in [false, true] {
            for ty in ["U32", "I32", "J"] {
                for after in [false, true] {
                    let (decl, name) = match member {
                        false => (format!("const K: {ty} = 3"), "K"),
                        true => (format!("struct S {{ x: I32 }}\nimpl S {{ const K: {ty} = 3 }}"), "S.K"),
                    };
                    let reader = reader.replace('R', name);
                    let (a, b) = if after { (decl, reader) } else { (reader, decl) };
                    let src = format!("type J = I32\n{a}\n{b}\n");
                    let want = if ty == "U32" { vec![] } else { vec![Code::E0401] };
                    assert_eq!(codes(&check(&src)), want, "{src}");
                }
            }
        }
    }
}

/// A type of a generated program; `W` is a form of its parts at the `#`.
#[derive(Clone)]
enum G {
    I,
    P(usize),
    Al(usize),
    D(usize, Vec<G>),
    W(&'static str, Vec<G>),
}

impl G {
    fn show(&self) -> String {
        match self {
            G::I => "I32".into(),
            G::P(i) => format!("T{i}"),
            G::Al(i) => format!("A{i}"),
            G::D(d, args) if args.is_empty() => format!("D{d}"),
            G::D(d, args) => format!("D{d}[{}]", args.iter().map(G::show).collect::<Vec<_>>().join(", ")),
            G::W(f, ts) => ts.iter().fold(f.to_string(), |s, t| s.replacen('#', &t.show(), 1)),
        }
    }

    fn subst(&self, env: &[G]) -> G {
        match self {
            G::P(i) => env[*i].clone(),
            G::D(d, args) => G::D(*d, args.iter().map(|a| a.subst(env)).collect()),
            G::W(f, ts) => G::W(f, ts.iter().map(|a| a.subst(env)).collect()),
            t => t.clone(),
        }
    }

    /// The declarations and aliases held as values (§4.4), or anywhere.
    fn held(&self, anywhere: bool, out: &mut Vec<G>) {
        match self {
            G::D(_, args) if anywhere => args.iter().for_each(|a| a.held(true, out)),
            G::D(..) | G::Al(_) => out.push(self.clone()),
            G::W(f, ts) if anywhere || f.starts_with(['O', '(', '[']) => ts.iter().for_each(|t| t.held(anywhere, out)),
            _ => {}
        }
    }
}

/// The random programs of [`G`]: declarations of their `arity` and `m`
/// aliases.
struct Gen {
    seed: u64,
    m: usize,
    arity: Vec<usize>,
}

impl Gen {
    fn rng(&mut self, n: usize) -> usize {
        self.seed = self.seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.seed >> 33) as usize % n
    }

    /// A type `depth` deep in a declaration of `np` parameters.
    fn ty(&mut self, depth: u32, np: usize) -> G {
        let (c, m) = (self.rng(100), self.m);
        match c {
            _ if depth >= 3 && np > 0 && c < 40 => G::P(self.rng(np)),
            _ if depth >= 3 && m > 0 && c < 70 => G::Al(self.rng(m)),
            _ if depth >= 3 || c < 8 => G::I,
            _ if c < 20 && np > 0 => G::P(self.rng(np)),
            _ if c < 38 && m > 0 => G::Al(self.rng(m)),
            _ if c < 60 => {
                let d = self.rng(self.arity.len());
                G::D(d, (0..self.arity[d]).map(|_| self.ty(depth + 1, np)).collect())
            }
            _ => {
                let forms = ["Array[#]", "Option[#]", "(#, #)", "[#; 2]", "fn(#) -> I32"];
                let f = forms[self.rng(forms.len())];
                G::W(f, (0..f.matches('#').count()).map(|_| self.ty(depth + 1, np)).collect())
            }
        }
    }
}

/// The E0311 of random programs of generic structs and enums and aliases
/// against an oracle that expands the arguments: a declaration is in a cycle
/// when it holds itself as a value, through its arguments read, and an alias
/// also when it names itself anywhere (§4.4, §18.1; W4-05 U2/b).
#[test]
fn the_cycles_of_random_generic_declarations_are_those_the_arguments_expand_to() {
    let (mut g, mut cycles) = (Gen { seed: 0x5eed, m: 0, arity: Vec::new() }, 0);
    for _ in 0..80 {
        let n = 1 + g.rng(4);
        g.m = g.rng(4);
        g.arity = (0..n).map(|_| [0, 0, 1, 1, 2][g.rng(5)]).collect();
        let decls: Vec<(bool, Vec<G>)> =
            (0..n).map(|d| (g.rng(2) == 0, (0..1 + g.rng(3)).map(|_| g.ty(0, g.arity[d])).collect())).collect();
        let aliases: Vec<G> = (0..g.m).map(|_| g.ty(0, 0)).collect();
        // The lines, shuffled: (declaration or alias, its index, its text).
        let mut lines: Vec<(bool, usize, String)> = Vec::new();
        for (d, (is_struct, fs)) in decls.iter().enumerate() {
            let gs = G::D(d, (0..g.arity[d]).map(G::P).collect()).show();
            let (kw, field) = if *is_struct { ("struct", "f#: #") } else { ("enum", "V#(#)") };
            let fs: Vec<String> =
                (fs.iter().enumerate()).map(|(j, f)| G::W(field, vec![G::P(j), f.clone()]).show()).collect();
            lines.push((true, d, format!("{kw} {gs} {{ {} }}", fs.join(", "))));
        }
        lines.extend(aliases.iter().enumerate().map(|(i, t)| (false, i, format!("type A{i} = {}", t.show()))));
        for i in (1..lines.len()).rev() {
            lines.swap(i, g.rng(i + 1));
        }
        // The oracle: whether `start` reaches a declaration of its own name.
        let reaches = |start: G, anywhere: bool| {
            let name = |g: &G| g.show().split('[').next().map(str::to_string);
            let (mut seen, mut queue) = (HashSet::new(), std::collections::VecDeque::from([start.clone()]));
            while let Some(cur) = queue.pop_front() {
                let shown = cur.show();
                if seen.len() > 3000 || shown.len() > 400 || !seen.insert(shown) {
                    continue;
                }
                let (body, env) = match &cur {
                    G::Al(i) => (vec![aliases[*i].clone()], Vec::new()),
                    G::D(d, args) => (decls[*d].1.clone(), args.clone()),
                    _ => unreachable!(),
                };
                let mut out = Vec::new();
                body.iter().for_each(|f| f.subst(&env).held(anywhere, &mut out));
                out.retain(|g| !anywhere || matches!(g, G::Al(_)));
                if out.iter().any(|g| name(g) == name(&start)) {
                    return true;
                }
                queue.extend(out);
            }
            false
        };
        let want: BTreeSet<usize> = (lines.iter().enumerate())
            .filter(|(_, (decl, i, _))| match decl {
                true => reaches(G::D(*i, vec![G::I; g.arity[*i]]), false),
                false => reaches(G::Al(*i), false) || reaches(G::Al(*i), true),
            })
            .map(|(k, _)| k + 1)
            .collect();
        let src: String = lines.iter().map(|l| format!("{}\n", l.2)).collect();
        let a = check(&src);
        let line = |s: onsa_diag::Span| src[..s.start as usize].matches('\n').count() + 1;
        let mut got = BTreeSet::new();
        for d in &a.diagnostics {
            assert_eq!(d.code, Code::E0311, "{src}{:?}", a.diagnostics);
            got.insert(line(d.span));
            got.extend(d.notes.iter().filter_map(|n| n.span).map(line));
        }
        assert_eq!(got, want, "{src}");
        cycles += !want.is_empty() as u32;
    }
    assert!((10..80).contains(&cycles), "{cycles} of 80 with a cycle");
}

/// What the order of the declarations reports (§4.4, §18.1; W4-05 U2/i3):
/// a constant at the position of a type is an E0308 and no edge; a cycle in
/// one module stays an E0311 when an alias joins it to a cycle the E0310 of
/// the imports reports; the arguments of a type whose parameters are an
/// E0304 are not read; the E0310 names no other name of its own `use` (R-315).
#[test]
fn the_order_of_the_declarations_reports_each_cycle_once() {
    for src in ["const K: A = 1\ntype A = K\n", "const K: S = 1\nstruct S { k: K }\n"] {
        assert!(codes(&check(src)).contains(&Code::E0308) && !codes(&check(src)).contains(&Code::E0311), "{src}");
    }
    for (head, w) in
        [("W[T, T] { a: T }", "W[S, I32]"), ("W[Option] { a: Option }", "W[S]"), ("W[S] { a: S }", "W[I32]")]
    {
        let src = format!("struct {head}\nstruct S {{ w: {w} }}\n");
        assert_eq!(codes(&check(&src)), vec![Code::E0304], "{src}");
    }
    let a = analyze(&pkg(&[
        ("a", "use b.{B}\npub type X = (B, Array[X])\npub struct A { x: X }\n"),
        ("b", "use a.{A}\npub struct B { a: A }\n"),
    ]));
    assert_eq!(codes(&a), vec![Code::E0310, Code::E0311]);
    let a = analyze(&pkg(&[
        ("a", "use b.{g, h}\n\npub fn f() -> I32 { g() + h() }\n"),
        ("b", "use a.{f}\nuse a\n\npub fn g() -> I32 { f() }\npub fn h() -> I32 { a.f() }\n"),
    ]));
    let [d] = &a.diagnostics[..] else { panic!("{:?}", a.diagnostics) };
    let at: Vec<FileId> = d.notes.iter().filter_map(|n| n.span).map(|s| s.file).collect();
    assert_eq!((d.code, at), (Code::E0310, vec![FileId(1), FileId(1)]));
}
