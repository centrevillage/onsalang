//! The record of the names of a body (W4-04 U2a, U2b): the bindings and
//! their numbers, the anonymous functions and their captures, the sites of
//! the bindings of `match`, `for` and a choice, the origins, the scopes, the
//! holes of a string, a body the walk stops in, the chains of names, the
//! paths of patterns and struct literals, and a flow body. The last test
//! holds the record against the tables of the types stage until the types
//! stage reads it (W4-04 U3b removes it).

use onsa_diag::FileId;
use onsa_syntax::ast::{ExprKind, Mode, PatKind};

use super::{BindingId, BindingKind, BodyNames, Origin, PatRes, PathRes, ScopeId, StructRes};
use crate::body::{LocalId, Target};
use crate::resolve::Entity;
use crate::{Analysis, DefId, Module, Package, analyze};

fn analysis(src: &str) -> (Analysis, Module) {
    let module = || Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.into(),
        parsed: onsa_syntax::parse(FileId(0), src),
    };
    (analyze(&Package::new("t", vec![module()], Vec::new())), module())
}

fn def(a: &Analysis, name: &str) -> DefId {
    DefId(a.defs.iter().position(|d| d.name == name).unwrap_or_else(|| panic!("no def {name}")) as u32)
}

fn names<'a>(a: &'a Analysis, name: &str) -> &'a BodyNames {
    &a.names[&def(a, name)]
}

fn binding_names(n: &BodyNames) -> Vec<&str> {
    n.bindings.iter().map(|b| b.name.as_str()).collect()
}

/// The binding named `name` (the first one).
fn binding(n: &BodyNames, name: &str) -> BindingId {
    BindingId(n.bindings.iter().position(|b| b.name == name).unwrap_or_else(|| panic!("no binding {name}")) as u32)
}

#[test]
fn locals_are_numbered_in_source_order_as_the_types_stage_numbers_them() {
    let src = "pub fn f(a: I32, _: I32, b: I32) -> I32 {\n  let c = a + b\n  var d = c\n  d = d + 1\n  d\n}\n";
    let (a, _) = analysis(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let n = names(&a, "f");
    assert!(n.complete);
    assert_eq!(binding_names(n), ["a", "b", "c", "d"]);
    let kinds: Vec<BindingKind> = n.bindings.iter().map(|b| b.kind).collect();
    assert_eq!(
        kinds,
        [BindingKind::Param(Mode::Borrow), BindingKind::Param(Mode::Borrow), BindingKind::Let, BindingKind::Var]
    );
    assert_eq!(n.bindings[0].origin, Origin::Param(0));
    assert_eq!(n.bindings[1].origin, Origin::Param(2));
    assert!(matches!(n.bindings[2].origin, Origin::Let(_)));
    assert!(matches!(n.bindings[3].origin, Origin::Var(_)));
    // The target of `d = d + 1` is no read.
    let reads: Vec<u32> = n.bindings.iter().map(|b| b.reads).collect();
    assert_eq!(reads, [1, 1, 1, 2]);
    // A parameter and a `var` have no pattern; the `let` has its own.
    assert!(n.bindings[0].sites.is_empty() && n.bindings[3].sites.is_empty());
    assert_eq!(n.pats.get(&n.bindings[2].sites[0]), Some(&PatRes::Bind(BindingId(2))));
    // The numbers are those of the locals of the types stage, and each path to
    // a local is the one its target names.
    let body = &a.bodies[&def(&a, "f")];
    let locals: Vec<&str> = body.locals.iter().map(|l| l.name.as_str()).collect();
    assert_eq!(locals, binding_names(n));
    assert_eq!(n.paths.len(), 6);
    for (e, r) in &n.paths {
        let PathRes::Local(b) = r else { panic!("{r:?}") };
        assert!(matches!(body.targets.get(e), Some(Target::Local(l)) if *l == LocalId(b.0)), "{e:?}");
    }
}

#[test]
fn anonymous_functions_capture_what_they_and_those_inside_them_read() {
    let src = "pub fn apply(f: fn(U32) -> U32) -> U32 { f(1) }\npub fn g(k: U32, m: U32) -> U32 {\n  apply(fn(i) { apply(fn(j) { j + k }) + i + m })\n}\n";
    let (a, _) = analysis(src);
    let n = names(&a, "g");
    assert_eq!(binding_names(n), ["k", "m", "i", "j"]);
    let mut closures: Vec<_> = n.captures.iter().collect();
    assert_eq!(closures.len(), 2);
    closures.sort_by_key(|(e, _)| e.0);
    // The outer one reads `k` through the inner one, before `m`.
    let (k, m) = (binding(n, "k"), binding(n, "m"));
    let caps: Vec<&Vec<BindingId>> = closures.iter().map(|(_, c)| *c).collect();
    assert!(caps.contains(&&vec![k, m]) && caps.contains(&&vec![k]), "{caps:?}");
    let outer = closures.iter().find(|(_, c)| c.len() == 2).unwrap().0;
    let i = &n.bindings[binding(n, "i").0 as usize];
    assert_eq!(i.kind, BindingKind::ClosureParam(Mode::Borrow));
    assert_eq!(i.origin, Origin::Closure { closure: *outer, param: 0 });
    assert_eq!(n.bindings[k.0 as usize].reads, 1);
}

#[test]
fn the_branches_of_a_choice_bind_one_binding_with_a_site_each() {
    let src = "pub fn n(q: ((I32, I32), I32)) -> I32 {\n  match q {\n    ((x, 0) | (0, x), 1) | ((x, 1) | (1, x), 2) => x,\n    (y, _) => 0,\n  }\n}\npub fn s() -> I32 {\n  var t = 0\n  for i in 0..<4 {\n    t = t + i\n  }\n  let (u, u) = (1, 2)\n  t\n}\n";
    let (a, module) = analysis(src);
    let ast = &module.parsed.ast;
    let n = names(&a, "n");
    assert_eq!(binding_names(n), ["q", "x", "y"]);
    let x = &n.bindings[1];
    assert_eq!(x.kind, BindingKind::MatchBind);
    assert_eq!(x.sites.len(), 4);
    for p in &x.sites {
        assert!(matches!(&ast.pat(*p).kind, PatKind::Bind(id) if id.name == "x"));
        assert_eq!(n.pats.get(p), Some(&PatRes::Bind(BindingId(1))));
    }
    let Origin::Arm { scrutinee, arm: 0 } = x.origin else { panic!("{:?}", x.origin) };
    assert!(matches!(&ast.expr(scrutinee).kind, ExprKind::Path(p) if p.segments[0].name == "q"));
    assert!(matches!(n.bindings[2].origin, Origin::Arm { arm: 1, .. }));
    // The two arms are sibling scopes under the block of the body.
    let (sx, sy) = (n.bindings[1].scope, n.bindings[2].scope);
    assert_ne!(sx, sy);
    assert_eq!(n.scopes[sx.0 as usize].parent, n.scopes[sy.0 as usize].parent);

    let s = names(&a, "s");
    assert_eq!(binding_names(s), ["t", "i", "u", "u"]);
    let i = &s.bindings[1];
    assert_eq!(i.kind, BindingKind::For { moved: false });
    assert!(matches!(i.origin, Origin::For(_)));
    assert_eq!(i.sites.len(), 1);
    // `t` is read twice (`t + i` and the result), assigned once.
    assert_eq!((s.bindings[0].reads, i.reads), (2, 1));
    // Two bindings of one name in one pattern are two bindings (E0304).
    assert_ne!(s.bindings[2].sites, s.bindings[3].sites);
}

#[test]
fn self_and_the_holes_of_a_string_are_bindings_of_the_scopes_of_the_body() {
    let src = "pub struct P { x: I32 }\nimpl P {\n  pub fn m(self, n: I32) -> Str {\n    let y = self.x + n\n    \"{y} and {n}\"\n  }\n}\n";
    let (a, _) = analysis(src);
    let n = names(&a, "m");
    assert!(n.complete);
    assert_eq!(binding_names(n), ["self", "n", "y"]);
    let me = &n.bindings[0];
    assert_eq!((me.kind, me.origin), (BindingKind::SelfParam(Mode::Borrow), Origin::SelfParam));
    assert!(me.sites.is_empty());
    assert_eq!(n.bindings[1].origin, Origin::Param(0));
    // The parameters are in the first scope; the `let` in the block under it.
    assert_eq!((me.scope, n.scopes[0].parent), (ScopeId(0), None));
    let y = &n.bindings[2];
    assert_eq!(n.scopes[y.scope.0 as usize].parent, Some(ScopeId(0)));
    assert_eq!(n.scopes[y.scope.0 as usize].bindings, [BindingId(2)]);
    let mut holes: Vec<_> = n.interp.iter().map(|((_, k), r)| (*k, r.clone())).collect();
    holes.sort_by_key(|(k, _)| *k);
    assert_eq!(holes, [(0, vec![(0, PathRes::Local(BindingId(2)))]), (2, vec![(0, PathRes::Local(BindingId(1)))])]);
    assert_eq!((me.reads, n.bindings[1].reads, y.reads), (1, 2, 1));
}

#[test]
fn a_type_argument_in_an_expression_stops_the_walk_of_its_body() {
    let src = "pub struct Q[T] { v: T }\npub fn id(x: I32) -> I32 { x }\npub fn t() -> I32 {\n  let a = 1\n  let b = id::[I32](a)\n  let c = 2\n  c\n}\npub fn s() -> I32 {\n  let k = 1\n  let q = Q::[I32] { v: k }\n  0\n}\npub fn r() -> I32 {\n  let k = 1\n  let q = Q { v: k }\n  0\n}\nconst K: I32 = 1\ntest \"w\" {\n  let w = K\n  assert w == 1\n}\n";
    let (a, _) = analysis(src);
    let t = names(&a, "t");
    assert!(!t.complete);
    assert_eq!(binding_names(t), ["a"]);
    assert_eq!(t.bindings[0].reads, 0);
    let s = names(&a, "s");
    assert!(!s.complete);
    assert_eq!(s.bindings[0].reads, 0);
    let r = names(&a, "r");
    assert!(r.complete);
    assert_eq!(r.bindings[0].reads, 1);
    let structs: Vec<&StructRes> = r.structs.values().collect();
    assert_eq!(structs, [&StructRes { def: def(&a, "Q"), owner: None }]);
    // A `const` and a test have a record too.
    assert!(names(&a, "K").complete && names(&a, "K").bindings.is_empty());
    let w = names(&a, "test \"w\"");
    assert!(w.complete);
    assert_eq!((binding_names(w), w.bindings[0].reads), (vec!["w"], 1));
}

/// The expression whose text is `text` (the first one).
fn node(m: &Module, text: &str) -> onsa_syntax::ast::ExprId {
    let ast = &m.parsed.ast;
    let k = (ast.exprs.iter())
        .position(|e| m.text.get(e.span.start as usize..e.span.end as usize) == Some(text))
        .unwrap_or_else(|| panic!("no expression `{text}`"));
    onsa_syntax::ast::ExprId(k as u32)
}

fn entity_of(a: &Analysis, name: &str) -> Entity {
    Entity::Def(def(a, name))
}

#[test]
fn chains_record_the_namespaces_they_pass_and_the_item_they_end_at() {
    let main = "use util\npub enum Shape { Circle(F32), Dot }\npub struct P { x: I32 }\nimpl P {\n  pub fn new() -> P { P { x: 1 } }\n}\ntype Q = P\nconst K: I32 = 1\npub fn g[const N: U32]() -> U32 {\n  let a = util.f(N)\n  let s = Shape.Circle(F32.PI)\n  let p = P.new()\n  let q = Q.new()\n  let o = Some(K)\n  let b = F32.from_bits(a)\n  let t = \"{K} {util.C}\"\n  let y = p.x\n  a\n}\npub fn h[T](x: T) -> T {\n  let z = T.ZERO\n  x\n}\n";
    let util = "pub fn f(n: U32) -> U32 { n }\npub const C: I32 = 2\n";
    let module = |segs: &[&str], file: u32, src: &str| Module {
        segments: segs.iter().map(|s| s.to_string()).collect(),
        file: FileId(file),
        text: src.into(),
        parsed: onsa_syntax::parse(FileId(file), src),
    };
    let m = module(&["main"], 0, main);
    let mut a = analyze(&Package::new("t", vec![module(&["main"], 0, main), module(&["util"], 1, util)], Vec::new()));
    let f32 = a.types.float(crate::ty::FloatKind::F32);
    let n = names(&a, "g");
    assert!(n.complete);
    let at = |text: &str| n.paths.get(&node(&m, text)).cloned();
    let util_mod = Entity::Module(a.module_of_file(FileId(1)).unwrap());
    let item = |entity| Some(PathRes::Item { entity, owner: None });
    assert_eq!(at("util"), Some(PathRes::Namespace(util_mod)));
    assert_eq!(at("util.f"), item(entity_of(&a, "f")));
    assert_eq!(at("N"), Some(PathRes::ConstParam(0)));
    assert_eq!(at("Shape"), Some(PathRes::Namespace(entity_of(&a, "Shape"))));
    assert_eq!(at("Shape.Circle"), item(Entity::Variant(def(&a, "Shape"), 0)));
    assert_eq!(at("F32"), Some(PathRes::Namespace(Entity::Builtin(crate::resolve::Builtin::Scalar(f32)))));
    assert_eq!(at("F32.PI"), Some(PathRes::BuiltinAssoc { ty: f32, name: "PI".into() }));
    assert_eq!(at("F32.from_bits"), Some(PathRes::BuiltinAssoc { ty: f32, name: "from_bits".into() }));
    assert_eq!(at("P.new"), item(Entity::Member(def(&a, "new"))));
    assert_eq!(at("Some"), item(Entity::Builtin(crate::resolve::Builtin::Some)));
    assert_eq!(at("K"), item(entity_of(&a, "K")));
    // A field of a value is the types stage's; an alias is resolved from U6.
    assert!(matches!(at("p"), Some(PathRes::Local(_))) && at("p.x").is_none());
    assert_eq!((at("Q"), at("Q.new")), (None, None));
    // The holes of a string: the namespaces they pass and their ends.
    let mut holes: Vec<_> = n.interp.iter().map(|((_, k), r)| (*k, r.clone())).collect();
    holes.sort_by_key(|(k, _)| *k);
    let c = PathRes::Item { entity: entity_of(&a, "C"), owner: None };
    assert_eq!(
        holes,
        [(0, vec![(0, item(entity_of(&a, "K")).unwrap())]), (2, vec![(0, PathRes::Namespace(util_mod)), (1, c)])]
    );
    // A type parameter is the head; what follows it is not resolved.
    let h = names(&a, "h");
    assert_eq!(h.paths.get(&node(&m, "T")), Some(&PathRes::TypeParam(0)));
    assert!(!h.paths.contains_key(&node(&m, "T.ZERO")));
    // The struct of a literal in the body of a method.
    let new: Vec<&StructRes> = names(&a, "new").structs.values().collect();
    assert_eq!(new, [&StructRes { def: def(&a, "P"), owner: None }]);
}

#[test]
fn the_paths_of_patterns_name_their_items() {
    let src = "pub enum Shape { Circle(F32), Dot }\npub struct P { x: I32 }\npub fn pm(s: Shape, o: Option[I32], p: P) -> I32 {\n  let P { x: x } = p\n  let a = match s {\n    Shape.Circle(r) => 1,\n    Shape.Dot => 2,\n  }\n  match o {\n    Some(v) => v + x + a,\n    None => 0,\n  }\n}\n";
    let (a, module) = analysis(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let n = names(&a, "pm");
    let ast = &module.parsed.ast;
    let mut ctors: Vec<(String, Entity)> = (n.pats.iter())
        .filter_map(|(p, r)| match r {
            PatRes::Ctor { entity, owner: None } => {
                let span = ast.pat(*p).span;
                Some((src[span.start as usize..span.end as usize].to_string(), *entity))
            }
            _ => None,
        })
        .collect();
    ctors.sort_by(|x, y| x.0.cmp(&y.0));
    use crate::resolve::Builtin;
    let shape = def(&a, "Shape");
    let want = [
        ("None", Entity::Builtin(Builtin::None)),
        ("P { x: x }", Entity::Def(def(&a, "P"))),
        ("Shape.Circle(r)", Entity::Variant(shape, 0)),
        ("Shape.Dot", Entity::Variant(shape, 1)),
        ("Some(v)", Entity::Builtin(Builtin::Some)),
    ];
    assert_eq!(ctors, want.map(|(t, e)| (t.to_string(), e)));
}

#[test]
fn a_flow_body_binds_its_inputs_then_its_lets_and_walks_no_assignment() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {\n  let y = prev~(^z) + x\n  let z = y * 0.5\n  let w = par i in 0 ..< 2 { x }\n  z + sample_rate()\n}\npub flow g(x: F32 at sample) -> F32 at sample {\n  let y = x\n  y = y + 1.0\n  y\n}\n";
    let (a, module) = analysis(src);
    let n = names(&a, "f");
    assert!(n.complete);
    assert_eq!(binding_names(n), ["x", "y", "z", "w", "i"]);
    let kinds: Vec<BindingKind> = n.bindings.iter().map(|b| b.kind).collect();
    use BindingKind::{FlowInput, FlowLet, ParVar};
    assert_eq!(kinds, [FlowInput, FlowLet, FlowLet, FlowLet, ParVar]);
    assert_eq!(n.bindings[0].origin, Origin::FlowInput(0));
    assert!(matches!(n.bindings[2].origin, Origin::Let(_)) && matches!(n.bindings[4].origin, Origin::Par(_)));
    // The names of the types stage, in its order (the `let`s before the body).
    let locals: Vec<&str> = a.flows[&def(&a, "f")].body.locals.iter().map(|l| l.name.as_str()).collect();
    assert_eq!(locals, binding_names(n));
    use crate::flow_names::{Delay, FlowBuiltin};
    let at = |text: &str| n.paths.get(&node(&module, text)).cloned();
    assert_eq!(at("prev"), Some(PathRes::FlowBuiltin(FlowBuiltin::Delay(Delay::Prev))));
    assert_eq!(at("sample_rate"), Some(PathRes::FlowBuiltin(FlowBuiltin::SampleRate)));
    assert_eq!(at("^z"), Some(PathRes::Local(BindingId(2))));
    // `y = y + 1.0` is not walked (E0806 is the flow stage's until W7-04).
    let g = names(&a, "g");
    assert_eq!((binding_names(g), g.bindings[1].reads), (vec!["x", "y"], 1));
    // A builtin name of a flow is none in a function body.
    let (b, _) = analysis("pub fn k() -> F32 {\n  sample_rate()\n}\n");
    assert!(names(&b, "k").paths.is_empty());
}

// ------------------------------------------------ against the types stage

/// The record of a name and the target the types stage gives it are the
/// same item (of an associated constant of a builtin type, the types stage
/// keeps the type of the constant).
fn same(types: &mut crate::ty::Types, t: &Target, r: &PathRes) -> bool {
    use crate::resolve::Entity::{Builtin, Def, Member, Variant};
    match (t, r) {
        (Target::Local(l), PathRes::Local(b)) => l.0 == b.0,
        (Target::ConstParam(i), PathRes::ConstParam(j)) => i == j,
        (Target::Fn { def, .. } | Target::Const(def), PathRes::Item { entity: Def(d) | Member(d), .. }) => def == d,
        (Target::Variant { def, index }, PathRes::Item { entity: Variant(d, i), .. }) => (def, index) == (d, i),
        (Target::Prelude(b), PathRes::Item { entity: Builtin(c), .. }) => b == c,
        (Target::BuiltinConst { ty, name }, PathRes::BuiltinAssoc { ty: t, name: n }) => {
            name == n && crate::builtin::assoc_const(types, *t, n) == Some(*ty)
        }
        (Target::BuiltinMethod { recv, name, .. }, PathRes::BuiltinAssoc { ty, name: n }) => (recv, name) == (ty, n),
        _ => false,
    }
}

/// The differences of the record of each body of `src` from the tables of
/// the types stage: the bindings (names, kinds), the patterns that bind, the
/// targets of every form, the captures, the constructors of the patterns and
/// the structs of the literals. A capture the types stage misses is no
/// difference when an anonymous function inside reads it (R-283).
fn differences(src: &str, counts: &mut [u32; 4], out: &mut Vec<String>) {
    use onsa_syntax::ast::{ExprId, ExprKind};
    let (mut a, module) = analysis(src);
    let ast = &module.parsed.ast;
    let m = a.module_of_file(FileId(0)).expect("the module");
    // The types, apart, to ask for the type of a constant.
    let mut types = std::mem::take(&mut a.types);
    let a = a;
    let mut diff = |what: String| out.push(what);
    let body_of = |id: &DefId| a.bodies.get(id).or_else(|| a.flows.get(id).map(|f| &f.body));
    let typed = a.bodies.keys().chain(a.flows.keys());
    for id in typed.filter(|id| !a.names.contains_key(id)) {
        diff(format!("{}: no record", a.def(*id).name));
    }
    let mut all_complete = a.failed.is_empty();
    for (id, n) in &a.names {
        let name = &a.def(*id).name;
        let Some(b) = body_of(id) else {
            diff(format!("{name}: a record of no body"));
            continue;
        };
        counts[0] += 1;
        let full = b.complete && n.complete;
        all_complete &= full;
        // The bindings: those of the types stage, in its order (in a
        // complete body, all of them).
        let k = b.locals.len().min(n.bindings.len());
        let kinds = (b.locals.iter().zip(&n.bindings)).all(|(l, x)| {
            use crate::body::LocalKind as L;
            l.name == x.name
                && match (l.kind, x.kind) {
                    (L::Param(p), BindingKind::Param(q))
                    | (L::SelfParam(p), BindingKind::SelfParam(q))
                    | (L::ClosureParam(p), BindingKind::ClosureParam(q)) => p == q,
                    (L::Param(p), BindingKind::FlowInput) => p == Mode::Borrow,
                    (L::Let, BindingKind::Let | BindingKind::FlowLet | BindingKind::ParVar) => true,
                    (L::For { moved: p }, BindingKind::For { moved: q }) => p == q,
                    (l, x) => matches!((l, x), (L::Var, BindingKind::Var) | (L::MatchBind, BindingKind::MatchBind)),
                }
        });
        if !kinds || (full && b.locals.len() != n.bindings.len()) {
            diff(format!("{name}: bindings {:?} {:?}", &b.locals[..k], &n.bindings[..k]));
            continue;
        }
        for (p, l) in &b.pat_locals {
            match n.pats.get(p) {
                Some(PatRes::Bind(x)) if x.0 == l.0 && n.bindings[x.0 as usize].sites.contains(p) => {}
                None if !n.complete => {}
                other => diff(format!("{name}: pattern {p:?} {l:?} {other:?}")),
            }
        }
        // The targets: of a call at its callee, of a name at its node.
        let callee_of = |e: &ExprId| match &ast.expr(*e).kind {
            ExprKind::Call { callee, .. } => Some(*callee),
            _ => None,
        };
        let mut calls = std::collections::HashMap::new();
        for (e, t) in &b.targets {
            counts[1] += 1;
            let (at, t) = match (callee_of(e), t) {
                // A function value (`f(x)`, `v.(x)`): its callee is a name of its own.
                (Some(_), Target::Value) => continue,
                (Some(c), t) => {
                    calls.insert(c, t);
                    (c, t)
                }
                (None, t) => (*e, t),
            };
            match (n.paths.get(&at), t) {
                (Some(r), t) if same(&mut types, t, r) => {}
                // A method of a value (not of a namespace, `F32.from_bits`).
                (None, Target::Method { .. } | Target::BuiltinMethod { .. })
                    if !matches!(&ast.expr(at).kind, ExprKind::Field { base, .. }
                        if matches!(n.paths.get(base), Some(PathRes::Namespace(_)))) => {}
                (None, _) if !n.complete => {}
                (r, t) => diff(format!("{name}: target {e:?} {t:?} {r:?}")),
            }
        }
        for (e, r) in n.paths.iter().filter(|_| full) {
            let t = b.targets.get(e).or_else(|| calls.get(e).copied());
            match (r, t) {
                (PathRes::Namespace(_) | PathRes::FlowBuiltin(_), None) => {}
                (_, Some(t)) if same(&mut types, t, r) => {}
                // An instance of a flow (`f~(x)`) has no target, nor has a
                // def this version does not support or a syntax error cut
                // (its uses are errors with no diagnostic, S-260).
                (PathRes::Item { entity: Entity::Def(d), .. }, None)
                    if matches!(a.def(*d).kind, crate::DefKind::Flow(_) | crate::DefKind::Unsupported)
                        || a.failed.contains_key(d) => {}
                (r, t) => diff(format!("{name}: record {e:?} {r:?} {t:?}")),
            }
        }
        if full {
            let inside = |outer: onsa_diag::Span, s: onsa_diag::Span| outer.start <= s.start && s.end <= outer.end;
            let keys = |c: &mut dyn Iterator<Item = &ExprId>| {
                let mut k: Vec<u32> = c.map(|e| e.0).collect();
                k.sort();
                k
            };
            let (theirs, mine) = (keys(&mut b.captures.keys()), keys(&mut n.captures.keys()));
            if theirs != mine {
                diff(format!("{name}: anonymous functions {theirs:?} {mine:?}"));
            }
            for (c, mine) in &n.captures {
                let span = ast.expr(*c).span;
                let mut want: Vec<u32> = (b.captures.iter())
                    .filter(|(d, _)| inside(span, ast.expr(**d).span))
                    .flat_map(|(_, ls)| ls.iter().map(|l| l.0))
                    .filter(|&l| !inside(span, n.bindings[l as usize].span))
                    .collect();
                let mut got: Vec<u32> = mine.iter().map(|x| x.0).collect();
                let theirs: Vec<u32> = b.captures[c].iter().map(|l| l.0).collect();
                want.sort();
                want.dedup();
                got.sort();
                if want != got || !theirs.iter().all(|l| got.contains(l)) {
                    diff(format!("{name}: captures {c:?} {theirs:?} {mine:?}"));
                }
            }
        }
    }
    // The paths of patterns and struct literals, as the types stage resolves
    // them; in a module whose bodies are all complete, every one it resolves.
    let records = |each: &dyn Fn(&BodyNames) -> Vec<(u32, Entity)>| {
        a.names.values().flat_map(each).collect::<std::collections::HashMap<_, _>>()
    };
    let ctors = records(&|n| {
        (n.pats.iter())
            .filter_map(|(p, r)| match r {
                PatRes::Ctor { entity, .. } => Some((p.0, *entity)),
                PatRes::Bind(_) => None,
            })
            .collect()
    });
    let structs = records(&|n| n.structs.iter().map(|(e, s)| (e.0, Entity::Def(s.def))).collect());
    let pattern_paths = (ast.pats.iter().enumerate()).filter_map(|(k, p)| match &p.kind {
        PatKind::Path(path) | PatKind::TupleStruct { path, .. } | PatKind::Struct { path, .. } => {
            Some((k, path, false))
        }
        _ => None,
    });
    let struct_paths = (ast.exprs.iter().enumerate()).filter_map(|(k, e)| match &e.kind {
        ExprKind::Struct { path, type_args, .. } if type_args.is_empty() => Some((k, path, true)),
        _ => None,
    });
    for (k, path, literal) in pattern_paths.chain(struct_paths) {
        let mine = if literal { &structs } else { &ctors }.get(&(k as u32));
        counts[2 + literal as usize] += mine.is_some() as u32;
        let theirs = a.resolve_path(m, path).ok().map(|e| match e {
            Entity::Member(d) if literal => Entity::Def(d),
            e => e,
        });
        match (mine, theirs) {
            (Some(x), Some(y)) if *x == y => {}
            (None, _) if !all_complete => {}
            // A module or a value at the end of the path of a struct
            // literal (the types stage reports it).
            (None, Some(Entity::Module(_) | Entity::Variant(..) | Entity::Builtin(_))) if literal => {}
            (mine, theirs) => out.push(format!("path {k} {literal} {mine:?} {theirs:?}")),
        }
    }
}

/// The cases of `tests/spec` that are one file, every `step`-th of them in
/// the order of their paths.
fn spec_cases(step: usize) -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    let mut dirs = vec![std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec")];
    while let Some(d) = dirs.pop() {
        for e in std::fs::read_dir(&d).expect("tests/spec") {
            let p = e.expect("an entry").path();
            if p.is_dir() {
                dirs.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                files.push(p);
            }
        }
    }
    files.sort();
    files.into_iter().step_by(step).collect()
}

/// The record says what the tables of the types stage say, on every tenth
/// case of `tests/spec` (about 150), until the types stage reads the record
/// (W4-04 U3b).
#[test]
fn the_record_agrees_with_the_types_stage_on_the_spec_cases() {
    onsa_diag::stack::run(|| {
        let files = spec_cases(10);
        let mut counts = [0; 4];
        let mut out = Vec::new();
        for f in &files {
            let src = std::fs::read_to_string(f).expect("a case");
            let start = out.len();
            differences(&src, &mut counts, &mut out);
            for d in &mut out[start..] {
                *d = format!("{}: {d}", f.display());
            }
        }
        assert!(out.is_empty(), "{} differences:\n{}", out.len(), out[..out.len().min(20)].join("\n"));
        // Each kind of the record was compared (none is passed by nothing run).
        let [bodies, targets, ctors, structs] = counts;
        assert!(files.len() >= 140 && bodies >= 500 && targets >= 2000 && ctors >= 20 && structs >= 20, "{counts:?}");
    });
}
