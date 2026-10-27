//! The record of the names of a body (W4-04 U2a, U2b): the bindings and
//! their numbers, the anonymous functions and their captures, the sites of
//! the bindings of `match`, `for` and a choice, the origins, the scopes, the
//! holes of a string, a body the walk stops in, the chains of names, the
//! paths of patterns and struct literals, a flow body, the local E0304 and
//! the builtin names of a flow written where they are not called (S-720).

use onsa_diag::FileId;
use onsa_syntax::ast::{ExprKind, Mode, PatKind};

use super::{BindingId, BindingKind, BodyNames, Origin, PatRes, PathRes, ScopeId, StructRes};
use crate::body::{LocalId, Target};
use crate::resolve::Entity;
use crate::{Analysis, DefId, Module, Package, analyze};

/// The analysis of `src`, one module with no syntax error (a case of a test
/// here is read whole).
fn analysis(src: &str) -> (Analysis, Module) {
    let module = || Module {
        segments: vec!["main".into()],
        file: FileId(0),
        text: src.into(),
        parsed: onsa_syntax::parse(FileId(0), src),
    };
    let m = module();
    assert!(m.parsed.diagnostics.is_empty(), "a syntax error: {:?}", m.parsed.diagnostics);
    (analyze(&Package::new("t", vec![module()], Vec::new())), m)
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
    let src = "pub fn n(q: ((I32, I32), I32)) -> I32 {\n  match q {\n    ((x, 0) | (0, x), 1) | ((x, 1) | (1, x), 2) => x,\n    (y, _) => 0,\n  }\n}\npub fn s() -> I32 {\n  var t = 0\n  for i in 0..<4 {\n    t = t + i\n  }\n  t\n}\n";
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
    assert_eq!(binding_names(s), ["t", "i"]);
    let i = &s.bindings[1];
    assert_eq!(i.kind, BindingKind::For { moved: false });
    assert!(matches!(i.origin, Origin::For(_)));
    assert_eq!(i.sites.len(), 1);
    // `t` is read twice (`t + i` and the result), assigned once.
    assert_eq!((s.bindings[0].reads, i.reads), (2, 1));
}

/// The codes and lines of the diagnostics of `src`.
fn reported(a: &Analysis, module: &Module) -> Vec<(onsa_diag::Code, u32)> {
    let line = |at: u32| module.text[..at as usize].matches('\n').count() as u32 + 1;
    a.diagnostics.iter().map(|d| (d.code, line(d.span.start))).collect()
}

#[test]
fn a_branch_of_a_choice_that_binds_other_names_is_one_e0314_in_the_order_of_the_text() {
    // At the start of the branch, before an error in it and after one in an
    // earlier branch; once for a `let` and a `for`, whose names are checked
    // ahead of the value (R-289); the outer choice before the inner one; a
    // `let` of a flow at its `let` (§18.1, S-318).
    let src = "pub fn ua(t: (I32, I32)) -> I32 {\n  match t {\n    (x, 0) | (0, Nope) => 0,\n    _ => 1,\n  }\n}\n\
               pub fn ub(t: (I32, I32)) -> I32 {\n  match t {\n    (x, Nope) | (0, y) => 0,\n    _ => 1,\n  }\n}\n\
               pub fn uc(o: Option[I32]) -> I32 {\n  let Some(a) | None = nope\n  0\n}\n\
               pub fn ud(xs: [Option[I32]; 2]) -> I32 {\n  for Some(a) | None in nope {\n  }\n  0\n}\n\
               pub fn ue(o: Option[Option[I32]]) -> I32 {\n  match o {\n    Some(Some(x)) |\n      Some(Some(y) | None) => 0,\n    _ => 1,\n  }\n}\n\
               pub flow uf(a: F32 at sample) -> F32 at sample {\n  let b = nope\n  let (c, _) | (_, d) = (a, a)\n  b\n}\n\
               pub flow ug(a: F32 at sample) -> F32 at sample {\n  let (c, _) | (_, d) = (a, a)\n  let e = nope\n  a\n}\n\
               pub fn uio() -> I32 {\n  0\n}\n\
               pub flow uh(a: F32 at sample) -> F32 at sample {\n  let (c, _) | uio = (a, a)\n  a\n}\n\
               pub fn ui(o: Option[I32]) -> I32 {\n  match o {\n    Some(x) | Non => x,\n    _ => 0,\n  }\n}\n";
    let (a, module) = analysis(src);
    use onsa_diag::Code::{E0302, E0304, E0314};
    // From the start of the branch, an error that ends with it is first by
    // its code (E0304, E0302 before E0314), in a `let` of a flow too.
    let want = [
        (E0314, 3),
        (E0302, 9),
        (E0314, 14),
        (E0314, 18),
        (E0314, 25),
        (E0302, 30),
        (E0314, 35),
        (E0304, 43),
        (E0302, 48),
    ];
    assert_eq!(reported(&a, &module), want);
}

#[test]
fn a_local_bound_twice_is_the_e0304_of_the_names_stage_where_its_second_binding_is() {
    // Before a type error of the unit (§18.1); in one branch of a choice
    // (R-284); a `let` of a flow at its `let`, after the errors before it.
    let src = "pub fn f() -> I32 {\n  let c: Bool = 1\n  let x = 1\n  let x = 2\n  x\n}\n\
               pub fn g(p: (I32, I32)) -> I32 {\n  match p {\n    (x, x) | (x, x) => x,\n  }\n}\n\
               pub fn h(p: (I32, I32)) -> I32 {\n  match p {\n    (x, 0) | (0, x) => x,\n    (y, _) => y,\n  }\n}\n\
               pub flow k(a: F32 at sample) -> F32 at sample {\n  let b = nope\n  let b = a\n  b\n}\n\
               pub flow l(a: F32 at sample) -> F32 at sample {\n  let b = a\n  let a = b\n  a\n}\n";
    let (a, module) = analysis(src);
    use onsa_diag::Code::{E0302, E0304};
    assert_eq!(reported(&a, &module), [(E0304, 4), (E0304, 9), (E0302, 19), (E0304, 25)]);
    let g = names(&a, "g");
    assert_eq!(binding_names(g), ["p", "x"]);
    assert!(g.reported && !g.complete);
    assert!(names(&a, "h").complete);
}

#[test]
fn a_builtin_name_of_a_flow_is_e0308_but_as_the_callee_of_its_call() {
    let src = "pub flow f(x: F32 at sample) -> F32 at sample {\n  let y = prev~(x)\n  let r = sample_rate()\n  y * r\n}\n\
               pub flow g(x: F32 at sample) -> F32 at sample {\n  let y = prev * x\n  y\n}\n\
               pub flow h(x: F32 at sample) -> F32 at sample {\n  let y = sample_rate.sqrt()\n  y\n}\n\
               pub flow k(x: F32 at sample) -> F32 at sample {\n  let y = prev~(^prev)\n  y\n}\n\
               pub fn m() -> F32 {\n  sample_rate()\n}\n";
    let (a, module) = analysis(src);
    use onsa_diag::Code::{E0302, E0308};
    assert_eq!(reported(&a, &module), [(E0308, 7), (E0308, 11), (E0308, 15), (E0302, 19)]);
    let f = names(&a, "f");
    assert!(f.complete);
    let callees = f.paths.values().filter(|r| matches!(r, PathRes::FlowBuiltin(_))).count();
    assert_eq!(callees, 2);
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
fn a_hole_of_a_string_is_resolved_and_reported_as_a_chain_of_an_expression() {
    // §2.4: the E0302 of `nope` and the E0308 of a builtin name of a flow are
    // of the names stage; a name held as an error stops the body with no
    // diagnostic (S-692, R-270), and a resolved hole has its records.
    let src = "fn dup() -> I32 { 1 }\nfn dup() -> I32 { 2 }\npub fn f() -> Str {\n  \"{nope}\"\n}\n\
               pub flow g(x: F32 at sample) -> F32 at sample {\n  let s = \"{sample_rate}\"\n  x\n}\n\
               pub fn h() -> Str {\n  \"{dup}\"\n}\nconst K: I32 = 1\n\
               pub fn k(t: (I32, I32)) -> Str {\n  \"{K} {t.1}\"\n}\n";
    let (a, module) = analysis(src);
    use onsa_diag::Code::{E0302, E0304, E0308, E0601};
    // `k`, checked to its end, makes a `Str` with no `uses {Alloc}` (§12).
    assert_eq!(reported(&a, &module), [(E0304, 2), (E0302, 4), (E0308, 7), (E0601, 14)]);
    let h = names(&a, "h");
    assert!(!h.complete && !h.reported && h.interp.is_empty());
    let k = names(&a, "k");
    let mut holes: Vec<_> = k.interp.iter().map(|((_, i), r)| (*i, r.clone())).collect();
    holes.sort_by_key(|(i, _)| *i);
    let t = PathRes::Local(binding(k, "t"));
    assert_eq!(holes, [(0, vec![(0, PathRes::Item { entity: entity_of(&a, "K"), owner: None })]), (2, vec![(0, t)])]);
    let body = &a.bodies[&def(&a, "k")];
    assert!(k.complete && body.complete);
    // The targets of the holes are the holes' (`unread_users` reads them).
    let targets: Vec<_> = body.hole_targets.values().filter(|t| matches!(t, crate::Target::Const(_))).collect();
    assert_eq!((targets.len(), body.targets.len()), (1, 0));
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
    assert_eq!(structs, [&StructRes { entity: entity_of(&a, "Q"), owner: None }]);
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
    assert_eq!(at("F32.PI"), Some(PathRes::BuiltinAssoc { ty: f32, name: "PI".into(), owner: None }));
    assert_eq!(at("F32.from_bits"), Some(PathRes::BuiltinAssoc { ty: f32, name: "from_bits".into(), owner: None }));
    assert_eq!(at("P.new"), item(Entity::Member(def(&a, "new"))));
    assert_eq!(at("Some"), item(Entity::Builtin(crate::resolve::Builtin::Some)));
    assert_eq!(at("K"), item(entity_of(&a, "K")));
    // A field of a value is the types stage's; an alias stands for its type,
    // the owner of its members (§4.4).
    assert!(matches!(at("p"), Some(PathRes::Local(_))) && at("p.x").is_none());
    let p_ty = a.types.find(&crate::ty::Ty::Named(def(&a, "P"), Vec::new()));
    let new = Some(PathRes::Item { entity: Entity::Member(def(&a, "new")), owner: p_ty });
    assert_eq!((at("Q"), at("Q.new")), (Some(PathRes::Namespace(entity_of(&a, "Q"))), new));
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
    assert_eq!(new, [&StructRes { entity: entity_of(&a, "P"), owner: None }]);
}

#[test]
fn the_parameters_of_a_heading_are_by_their_index_and_a_builtin_type_has_its_own_items() {
    let src = "pub fn g[T, const N: U32, U, const M: U32](x: T, y: U) -> U32 {\n  let a = M\n  let b = N\n  let c = U.ZERO\n  a + b\n}\npub flow f(x: F32 at sample) -> F32 at sample {\n  let t = sample_tick()\n  x\n}\n";
    let (mut a, m) = analysis(src);
    let n = names(&a, "g");
    let at = |n: &BodyNames, text: &str| n.paths.get(&node(&m, text)).cloned();
    assert_eq!((at(n, "M"), at(n, "N")), (Some(PathRes::ConstParam(3)), Some(PathRes::ConstParam(1))));
    assert_eq!(at(n, "U"), Some(PathRes::TypeParam(2)));
    use crate::flow_names::FlowBuiltin;
    assert_eq!(at(names(&a, "f"), "sample_tick"), Some(PathRes::FlowBuiltin(FlowBuiltin::SampleTick)));
    // The associated constants of a builtin type are of the types that own them.
    use crate::builtin::has_assoc_const;
    use crate::ty::{FloatKind, IntKind};
    let t = &mut a.types;
    let (i32, f32, bool) = (t.int(IntKind::I32), t.float(FloatKind::F32), t.bool());
    let t = &a.types;
    assert!(has_assoc_const(t, i32, "MAX") && has_assoc_const(t, f32, "PI"));
    assert!(!has_assoc_const(t, i32, "PI") && !has_assoc_const(t, bool, "MAX"));
    assert!(!has_assoc_const(t, f32, "from_bits") && !has_assoc_const(t, f32, "zeroed"));
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

/// `Self` in the body of an `impl` and an alias stand for their type, the
/// owner of what the path names (§2.2, §4.4, S-595, S-91): `Self` of
/// `impl[T] G[T]` is `G[T]`.
#[test]
fn self_and_an_alias_name_their_type_as_the_owner_of_what_follows() {
    let src = "pub struct G[T] { v: T }\nimpl[T] G[T] {\n  pub fn wrap(v: T) -> Self { Self { v: v } }\n  pub fn get(self) -> T {\n    let Self { v: x } = self\n    let f = fn(w: T) -> G[T] { Self.wrap(w) }\n    x\n  }\n}\ntype GI = G[I32]\npub fn k() -> GI { GI { v: 1 } }\n";
    let (a, module) = analysis(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let g_t = a.types.find(&crate::ty::Ty::Named(def(&a, "G"), vec![a.types.find(&crate::ty::Ty::Param(0)).unwrap()]));
    let g_i32 = a.types.find(&crate::ty::Ty::Named(
        def(&a, "G"),
        vec![a.types.find(&crate::ty::Ty::Int(crate::ty::IntKind::I32)).unwrap()],
    ));
    let g = Entity::Def(def(&a, "G"));
    let one = |n: &BodyNames| n.structs.values().cloned().collect::<Vec<_>>();
    assert_eq!(one(names(&a, "wrap")), [StructRes { entity: g, owner: g_t }]);
    assert_eq!(one(names(&a, "k")), [StructRes { entity: g, owner: g_i32 }]);
    let get = names(&a, "get");
    let ctors: Vec<_> = get.pats.values().filter(|r| matches!(r, PatRes::Ctor { .. })).cloned().collect();
    assert_eq!(ctors, [PatRes::Ctor { entity: g, owner: g_t }]);
    let at = |text: &str| get.paths.get(&node(&module, text)).cloned();
    let wrap = PathRes::Item { entity: Entity::Member(def(&a, "wrap")), owner: g_t };
    assert_eq!((at("Self"), at("Self.wrap")), (Some(PathRes::Namespace(g)), Some(wrap)));
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
    // The walk stops at `y = y + 1.0` (E0806 is the flow stage's until W7-04).
    let g = names(&a, "g");
    assert_eq!((binding_names(g), g.bindings[1].reads, g.complete), (vec!["x", "y"], 0, false));
    // A builtin name of a flow is none in a function body.
    let (b, _) = analysis("pub fn k() -> F32 {\n  sample_rate()\n}\n");
    assert!(names(&b, "k").paths.is_empty());
}

#[test]
fn a_name_held_as_an_error_stops_the_check_of_its_body_with_no_diagnostic() {
    // `dup` is declared twice (E0304): where it is used, the walk and the
    // check stop, and the end of the check (the type of `None`) is not run.
    let src = "fn dup() -> I32 { 1 }\nfn dup() -> I32 { 2 }\npub fn f() -> I32 {\n  let v = None\n  dup()\n}\n";
    let (a, _) = analysis(src);
    let codes: Vec<_> = a.diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(codes, [onsa_diag::Code::E0304], "{:?}", a.diagnostics);
    let f = def(&a, "f");
    assert!(!a.names[&f].complete && !a.names[&f].reported);
    assert!(!a.bodies[&f].complete);
}

#[test]
fn an_error_of_the_names_stage_in_a_type_of_the_body_comes_before_one_of_the_types_stage() {
    // §18.1: the E0302 of `Nope` stops the body; the E0401 of `"s"`, before
    // it, is of a later stage.
    let src = "pub fn f() -> I32 {\n  let a: I32 = \"s\"\n  let b: Nope = 1\n  0\n}\n";
    let (a, _) = analysis(src);
    let codes: Vec<_> = a.diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(codes, [onsa_diag::Code::E0302], "{:?}", a.diagnostics);
    let n = names(&a, "f");
    assert!(n.reported && !n.complete);
}
