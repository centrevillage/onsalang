//! The verifier (W8-02): each of its checks broken alone, in a Core made by
//! hand, is rejected as a value (never a panic) with the number of its rule
//! (`design/04-core.md`) and the position of the node that breaks it.
//!
//! W8-14: the verifier matches the kinds of the types of a module one level
//! deep without interning: a struct literal, a variant, a field, the view of
//! a `Span` and an argument of a call of another type are rejected, each
//! with the type it has and the one it is in.

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::prim::{MathFn, Prim, Shape, sig};
use crate::{Rule, VerifyError, verify};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// The position of the node that breaks a rule.
fn at() -> Span {
    Span::new(FileId(0), 7, 9)
}

fn lit(ty: CTy, l: Lit) -> Expr {
    Expr::new(ty, sp(), ExprKind::Lit(l))
}

fn one() -> Expr {
    lit(Types::U32, Lit::Int(1))
}

fn f(name: &str, params: Vec<Param>, ret: CTy, locals: Vec<Local>, stmts: Vec<Stmt>, value: Expr) -> FnDef {
    let body = Some(Block { stmts, value: Some(Box::new(value)) });
    let (span, sret) = (sp(), false);
    FnDef {
        name: name.into(),
        params,
        ret,
        sret,
        rt: false,
        locals,
        body,
        span,
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    }
}

/// A module of the struct `S { a: U32 }` and the enum `E { A(U32) }`.
fn base() -> Module {
    let mut m = Module::default();
    m.types.push(TypeDef { name: "S".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), Types::U32)] } });
    m.types
        .push(TypeDef { name: "E".into(), kind: TypeDefKind::Enum { variants: vec![("A".into(), vec![Types::U32])] } });
    m
}

/// `m` with the function `g` of `value`, returned (by `sret` when it is an aggregate).
fn with_g(mut m: Module, value: Expr) -> Module {
    let sret = m.tys.is_aggregate(value.ty);
    m.fns.push(f("g", vec![], value.ty, vec![], vec![], value));
    m.fns.last_mut().expect("g").sret = sret;
    m
}

/// `m` with the function `g` of the statement `e` and no value.
fn with_stmt(mut m: Module, e: Expr) -> Module {
    let stmts = vec![Stmt { span: sp(), kind: StmtKind::Expr(e) }];
    m.fns.push(f("g", vec![], Types::UNIT, vec![], stmts, lit(Types::UNIT, Lit::Unit)));
    m
}

/// `m`, its facts filled, is rejected by `rule` with `message`.
fn rejected(m: &Module, rule: Rule, message: &str) -> VerifyError {
    let mut m = m.clone();
    m.fill_all_facts();
    rejected_as_is(&m, rule, message)
}

/// `m`, as it is (a table whose facts cannot be filled), is rejected by `rule` with `message`.
fn rejected_as_is(m: &Module, rule: Rule, message: &str) -> VerifyError {
    let err = verify(m).expect_err(message);
    assert!(err.message.contains(message) && err.rule == rule, "{rule}: {err}");
    err
}

/// A type at the index `i` of another table (only a table makes one).
fn foreign(i: usize) -> CTy {
    let mut other = Types::default();
    (0..).map(|n| other.intern(TyKind::Array(Types::U32, n))).find(|t| t.index() == i).expect("a type")
}

#[test]
fn a_struct_literal_or_a_variant_of_another_type_is_rejected() {
    let one = || vec![(0, lit(Types::U32, Lit::Int(1)))];
    let m = base();
    rejected(
        &with_g(m, Expr::new(Types::BOOL, sp(), ExprKind::Struct { ty: TypeId(0), fields: one() })),
        Rule::V01,
        "struct literal: type mismatch `S` vs `Bool`",
    );
    let mut m = base();
    m.types.push(TypeDef { name: "T".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), Types::U32)] } });
    let t = m.tys.intern(TyKind::Struct(TypeId(2)));
    rejected(
        &with_g(m, Expr::new(t, sp(), ExprKind::Struct { ty: TypeId(0), fields: one() })),
        Rule::V01,
        "struct literal: type mismatch `S` vs `T`",
    );
    let variant = ExprKind::Variant { ty: TypeId(1), tag: 0, fields: vec![lit(Types::U32, Lit::Int(1))] };
    rejected(&with_g(base(), Expr::new(Types::BOOL, sp(), variant)), Rule::V01, "variant: type mismatch `E` vs `Bool`");
}

/// V-01 (W8-03): a struct literal gives each field once, in the order of
/// evaluation (written `b` then `a` is one): a field given twice or left out
/// is rejected, and a number past the declaration is V-20.
#[test]
fn a_struct_literal_gives_each_field_exactly_once() {
    let mut m = base();
    let fields = vec![("a".into(), Types::U32), ("b".into(), Types::U32)];
    m.types.push(TypeDef { name: "P".into(), kind: TypeDefKind::Struct { fields } });
    let p = m.tys.intern(TyKind::Struct(TypeId(2)));
    let of = |fields: &[u32]| {
        let fields = fields.iter().map(|&k| (k, lit(Types::U32, Lit::Int(1)))).collect();
        let mut m = with_g(m.clone(), Expr::new(p, sp(), ExprKind::Struct { ty: TypeId(2), fields }));
        m.fill_all_facts();
        m
    };
    assert!(verify(&of(&[1, 0])).is_ok(), "{:?}", verify(&of(&[1, 0])));
    rejected(&of(&[0, 0]), Rule::V01, "struct literal field 0 given twice");
    rejected(&of(&[1, 1]), Rule::V01, "struct literal field 1 given twice");
    rejected(&of(&[1]), Rule::V01, "struct literal field count");
    rejected(&of(&[0, 1, 1]), Rule::V01, "struct literal field count");
    rejected(&of(&[0, 2]), Rule::V20, "struct literal field 2 out of range");
}

#[test]
fn a_field_a_view_or_an_argument_of_another_type_is_rejected() {
    let mut m = base();
    let s = m.tys.intern(TyKind::Struct(TypeId(0)));
    let fields = vec![(0, lit(Types::BOOL, Lit::Bool(true)))];
    rejected(
        &with_g(m, Expr::new(s, sp(), ExprKind::Struct { ty: TypeId(0), fields })),
        Rule::V01,
        "struct field: type mismatch `Bool` vs `U32`",
    );
    // `Span[U8]` of a `[U32; 2]`.
    let mut m = base();
    let arr = m.tys.intern(TyKind::Array(Types::U32, 2));
    let view8 = m.tys.intern(TyKind::Span(Types::int(IntKind::U8)));
    let two = Expr::new(arr, sp(), ExprKind::Array(vec![lit(Types::U32, Lit::Int(1)), lit(Types::U32, Lit::Int(2))]));
    let a = Expr::new(arr, sp(), ExprKind::Local(LocalId(0)));
    let view = Expr::new(view8, sp(), ExprKind::SpanOf(Box::new(a)));
    let let_ = Stmt { span: sp(), kind: StmtKind::Let(LocalId(0), two) };
    m.fns.push(f("g", vec![], view8, vec![Local::value("a", arr)], vec![let_], view));
    rejected(&m, Rule::V01, "span: type mismatch `Span[U32]` vs `Span[U8]`");
    // A `Bool` for the `U32` of `callee`.
    let mut m = base();
    let x = Param { local: LocalId(0), mode: Mode::Borrow, ty: Types::U32 };
    let read = Expr::new(Types::U32, sp(), ExprKind::Local(LocalId(0)));
    m.fns.push(f("callee", vec![x], Types::U32, vec![Local::value("x", Types::U32)], vec![], read));
    let args = vec![Arg { mode: Mode::Borrow, expr: lit(Types::BOOL, Lit::Bool(true)) }];
    rejected(
        &with_g(m, Expr::new(Types::U32, sp(), ExprKind::Call { fn_: FnId(0), args })),
        Rule::V01,
        "argument: type mismatch `Bool` vs `U32`",
    );
}

/// An error is at the node that breaks the rule: a part's own, or past its
/// parts the parent's.
#[test]
fn an_error_has_the_position_of_its_node() {
    let big = Expr::new(Types::int(IntKind::U8), at(), ExprKind::Lit(Lit::Int(999)));
    let neg = ExprKind::Unary(UnOp::Neg, Box::new(big));
    let err =
        rejected(&with_g(base(), Expr::new(Types::int(IntKind::U8), sp(), neg)), Rule::V01, "out of range for U8");
    assert_eq!(err.span, Some(at()), "{err}");
    let t = lit(Types::BOOL, Lit::Bool(true));
    let add =
        ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Checked, lhs: Box::new(t.clone()), rhs: Box::new(t) };
    let err = rejected(&with_g(base(), Expr::new(Types::BOOL, at(), add)), Rule::V01, "arithmetic on a non-numeric");
    assert_eq!(err.span, Some(at()), "{err}");
}

/// The checks of the forms that are not types (V-01 for a test, V-03 to
/// V-08, V-14), each with its number.
#[test]
fn each_rule_of_a_form_is_rejected_with_its_number() {
    let x = || Param { local: LocalId(0), mode: Mode::Inout, ty: Types::U32 };
    let xs = || vec![Local::value("x", Types::U32)];
    let unit = || lit(Types::UNIT, Lit::Unit);
    let mut m = base();
    m.fns.push(f("t", vec![x()], Types::UNIT, xs(), vec![], unit()));
    m.fns[0].test = Some(TestMark { module: "m".into(), name: "t".into() });
    rejected(&m, Rule::V01, "a test function with parameters or a value");
    let cast = ExprKind::Cast(Box::new(lit(Types::BOOL, Lit::Bool(true))));
    rejected(&with_g(base(), Expr::new(Types::U32, sp(), cast)), Rule::V03, "`Bool` as `U32` is no widening");
    // `callee(inout x: U32)` given a literal; a primitive too.
    let mut m = base();
    m.fns.push(f("callee", vec![x()], Types::UNIT, xs(), vec![], unit()));
    let args = || vec![Arg { mode: Mode::Inout, expr: one() }];
    let call = ExprKind::Call { fn_: FnId(0), args: args() };
    rejected(&with_stmt(m.clone(), Expr::new(Types::UNIT, sp(), call)), Rule::V05, "inout argument is not a place");
    let prim = ExprKind::Prim { prim: Prim::BufZeroed, args: args() };
    rejected(&with_stmt(base(), Expr::new(Types::UNIT, sp(), prim)), Rule::V05, "inout primitive argument");
    // An `rt` function calling a non-`rt` one, and allocating.
    let rt = |mut m: Module| {
        m.fns.last_mut().expect("g").rt = true;
        m
    };
    let mut m = base();
    let b = Param { local: LocalId(0), mode: Mode::Borrow, ty: Types::U32 };
    m.fns.push(f("callee", vec![b], Types::UNIT, xs(), vec![], unit()));
    let call = ExprKind::Call { fn_: FnId(0), args: vec![Arg { mode: Mode::Borrow, expr: one() }] };
    rejected(&rt(with_stmt(m, Expr::new(Types::UNIT, sp(), call))), Rule::V06, "rt function calls non-rt `callee`");
    let zeroed = ExprKind::Prim { prim: Prim::BufZeroed, args: vec![Arg { mode: Mode::Borrow, expr: one() }] };
    rejected(&rt(with_stmt(base(), Expr::new(Types::UNIT, sp(), zeroed))), Rule::V06, "non-rt primitive `buf.zeroed`");
    let mut m = base();
    let stmts = vec![Stmt { span: sp(), kind: StmtKind::Break }];
    m.fns.push(f("g", vec![], Types::UNIT, vec![], stmts, unit()));
    rejected(&m, Rule::V07, "break / continue outside a loop");
    // A `Switch` of a tag twice, and of no arm.
    let mut m = base();
    let e = m.tys.intern(TyKind::Enum(TypeId(1)));
    let a = Expr::new(e, sp(), ExprKind::Variant { ty: TypeId(1), tag: 0, fields: vec![one()] });
    let arm = || (0, Block { stmts: vec![], value: Some(Box::new(one())) });
    let switch = |arms| ExprKind::Switch { scrutinee: Box::new(a.clone()), arms, default: None };
    rejected(&with_g(m.clone(), Expr::new(Types::U32, sp(), switch(vec![arm(), arm()]))), Rule::V08, "or duplicated");
    rejected(&with_g(m, Expr::new(Types::U32, sp(), switch(vec![]))), Rule::V08, "does not cover every variant");
    // `sret` on a function of a scalar.
    let mut m = with_g(base(), one());
    m.fns[0].sret = true;
    rejected(&m, Rule::V14, "sret flag does not match the return type");
}

/// V-20 in a function: each id out of range, and a struct literal or a
/// field read of an opaque type.
#[test]
fn an_id_out_of_range_in_an_item_is_rejected() {
    let unit = |kind| Expr::new(Types::UNIT, at(), kind);
    let err = rejected(&with_stmt(base(), Expr::new(foreign(500), at(), ExprKind::Zeroed)), Rule::V20, "ty 500 out of");
    assert_eq!((err.span, err.fn_name.as_str()), (Some(at()), "g"), "{err}");
    let local = Expr::new(Types::U32, at(), ExprKind::Local(LocalId(9)));
    rejected(&with_stmt(base(), local.clone()), Rule::V20, "local out of range");
    let mut m = base();
    m.consts.push(ConstDef { name: "K".into(), ty: Types::U32, init: local });
    rejected(&m, Rule::V20, "local used outside a function");
    rejected(&with_stmt(base(), unit(ExprKind::Const(ConstId(9)))), Rule::V20, "const 9 out of range");
    let call = ExprKind::Call { fn_: FnId(9), args: vec![] };
    rejected(&with_stmt(base(), unit(call)), Rule::V20, "call to an unknown fn");
    let panic = ExprKind::Panic { msg: MsgId(9), origin: PanicOrigin::Panic, shown: vec![] };
    rejected(&with_stmt(base(), unit(panic)), Rule::V20, "panic message out of range");
    let s = unit(ExprKind::Struct { ty: TypeId(9), fields: vec![] });
    rejected(&with_stmt(base(), s), Rule::V20, "type 9 out of range");
    let v = unit(ExprKind::Variant { ty: TypeId(9), tag: 0, fields: vec![] });
    rejected(&with_stmt(base(), v), Rule::V20, "type 9 out of range");
    // The numbers of a field, an element, a variant and a payload.
    let mut m = base();
    let (s, e) = (m.tys.intern(TyKind::Struct(TypeId(0))), m.tys.intern(TyKind::Enum(TypeId(1))));
    let pair = m.tys.intern(TyKind::Tuple(Box::new([Types::U32])));
    let of = |ty, kind| Box::new(Expr::new(ty, sp(), kind));
    let field = |base, index| Expr::new(Types::U32, at(), ExprKind::Field { base, index });
    rejected(&with_g(m.clone(), field(of(s, ExprKind::Zeroed), 3)), Rule::V20, "field index out of range");
    rejected(&with_g(m.clone(), field(of(pair, ExprKind::Zeroed), 2)), Rule::V20, "tuple index out of range");
    let v = Expr::new(e, at(), ExprKind::Variant { ty: TypeId(1), tag: 5, fields: vec![] });
    rejected(&with_g(m.clone(), v), Rule::V20, "variant tag out of range");
    for (tag, index, message) in [(5, 0, "payload tag out of range"), (0, 3, "payload index out of range")] {
        let p = ExprKind::Payload { base: of(e, ExprKind::Zeroed), tag, index };
        rejected(&with_g(m.clone(), Expr::new(Types::U32, at(), p)), Rule::V20, message);
    }
    // An opaque type: neither a literal nor a field read of it.
    m.types.push(TypeDef { name: "O".into(), kind: TypeDefKind::Opaque });
    let o = m.tys.intern(TyKind::Struct(TypeId(2)));
    let lit_o = Expr::new(o, at(), ExprKind::Struct { ty: TypeId(2), fields: vec![] });
    rejected(&with_stmt(m.clone(), lit_o), Rule::V20, "struct literal of an opaque type");
    rejected(&with_g(m, field(of(o, ExprKind::Zeroed), 0)), Rule::V20, "field access on an opaque type");
}

/// V-20 in the tables, before any item: the parts of a type before it, the
/// definitions of struct and enum types, every id of a table, the facts.
#[test]
fn the_tables_of_a_module_are_checked_before_its_items() {
    // A part out of the table, and a part in it but not before its type.
    let mut m = base();
    m.tys.intern(TyKind::Array(foreign(200), 1));
    rejected_as_is(&m, Rule::V20, "has the part 200 not before it");
    let mut m = base();
    let n = m.tys.kinds().len();
    m.tys.intern(TyKind::Tuple(Box::new([Types::U32, foreign(n + 1)])));
    m.tys.intern(TyKind::Array(Types::U32, 7));
    let err = rejected_as_is(&m, Rule::V20, &format!("ty {n} has the part {} not before it", n + 1));
    assert_eq!((err.fn_name.as_str(), err.span), ("the type table", None), "{err}");
    // The dump of it marks the part, so that a table with a cycle dumps too.
    let t = m.tys.ids().nth(n).expect("the tuple");
    assert_eq!(crate::dump::type_name(&m, t), format!("(U32, <bad ty {}>)", n + 1));
    // A type that is its own part: rejected, and its dump ends.
    let mut m = base();
    let own = m.tys.intern(TyKind::Array(foreign(n), 1));
    rejected_as_is(&m, Rule::V20, &format!("ty {n} has the part {n} not before it"));
    assert_eq!(crate::dump::type_name(&m, own), format!("[<bad ty {n}>; 1]"));
    for k in [TyKind::Struct(TypeId(1)), TyKind::Enum(TypeId(0)), TyKind::Struct(TypeId(9))] {
        let mut m = base();
        m.tys.intern(k);
        rejected_as_is(&m, Rule::V20, "is of no definition of its kind");
    }
    let mut m = base();
    m.types.push(TypeDef { name: "T".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), foreign(300))] } });
    assert_eq!(rejected_as_is(&m, Rule::V20, "ty 300 out of range").fn_name, "T");
    let mut m = base();
    m.consts.push(ConstDef { name: "K".into(), ty: foreign(300), init: one() });
    rejected_as_is(&m, Rule::V20, "ty 300 out of range");
    // A function: the type of a local, the local of a parameter, a hoisted local.
    let mut m = with_g(base(), one());
    m.fns[0].locals.push(Local::value("x", foreign(300)));
    rejected_as_is(&m, Rule::V20, "ty 300 out of range");
    let mut m = with_g(base(), one());
    m.fns[0].params.push(Param { local: LocalId(0), mode: Mode::Borrow, ty: Types::U32 });
    rejected(&m, Rule::V20, "parameter local out of range");
    let mut m = with_g(base(), one());
    m.fns[0].hoisted.push(LocalId(4));
    rejected(&m, Rule::V20, "hoisted local 4 out of range");
    // The copies, the facts.
    let mut m = with_g(base(), one());
    m.moves.push(MoveSite { fn_: FnId(9), span: sp(), ty: Types::U32, bytes: 4, kind: MoveKind::Copy });
    rejected(&m, Rule::V20, "a copy of fn 9 out of range");
    let err = rejected_as_is(&with_g(base(), one()), Rule::V20, "the facts do not cover the type table");
    assert_eq!(err.fn_name, "the facts");
    // The functions and the types of a flow.
    let m = crate::tests::core("pub flow f(x: F32 at sample) -> F32 at sample {\n  x\n}\n");
    let mut tick = m.clone();
    tick.flows[0].fns.tick = FnId(999);
    rejected_as_is(&tick, Rule::V20, "fn 999 out of range");
    let mut state = m;
    state.flows[0].fns.state = TypeId(999);
    rejected_as_is(&state, Rule::V20, "type 999 out of range");
}

/// Another position than the one of `sp()` and of `at()`.
fn other() -> Span {
    Span::new(FileId(0), 20, 25)
}

#[test]
fn a_rule_is_shown_by_its_number() {
    use Rule::*;
    let all =
        [V01, V02, V03, V04, V05, V06, V07, V08, V09, V10, V11, V12, V13, V14, V15, V16, V17, V18, V20, V22, V25, V28];
    let shown: Vec<String> = all.iter().map(|r| r.to_string()).collect();
    let numbers = (1..=18).chain([20, 22, 25, 28]);
    assert_eq!(shown, numbers.map(|i| format!("V-{i:02}")).collect::<Vec<_>>());
}

/// The position of an error in a statement, past a statement at the node
/// around it, and in the initializer of a `const`.
#[test]
fn an_error_of_a_statement_or_a_const_has_its_position() {
    let let_ = Stmt { span: at(), kind: StmtKind::Let(LocalId(0), lit(Types::BOOL, Lit::Bool(true))) };
    let mut m = base();
    let a = vec![Local::value("a", Types::U32)];
    m.fns.push(f("g", vec![], Types::UNIT, a, vec![let_], lit(Types::UNIT, Lit::Unit)));
    assert_eq!(rejected(&m, Rule::V01, "let: type mismatch").span, Some(at()));
    let stmt = Stmt { span: other(), kind: StmtKind::Expr(lit(Types::UNIT, Lit::Unit)) };
    let b = Block { stmts: vec![stmt], value: Some(Box::new(lit(Types::BOOL, Lit::Bool(true)))) };
    let e = Expr::new(Types::U32, at(), ExprKind::Block(b));
    assert_eq!(rejected(&with_g(base(), e), Rule::V01, "block: type mismatch").span, Some(at()));
    let mut m = base();
    let init = Expr::new(Types::BOOL, at(), ExprKind::Lit(Lit::Bool(true)));
    m.consts.push(ConstDef { name: "K".into(), ty: Types::U32, init });
    assert_eq!(rejected(&m, Rule::V01, "const initializer: type mismatch").span, Some(at()));
}

/// A tag of a non-enum and a field read of an enum are of the types (V-01).
#[test]
fn a_tag_or_a_field_of_the_wrong_kind_is_rejected() {
    let tag = ExprKind::Tag(Box::new(Expr::new(Types::U32, sp(), ExprKind::Zeroed)));
    rejected(&with_g(base(), Expr::new(Types::U32, at(), tag)), Rule::V01, "tag of a non-enum");
    let mut m = base();
    let e = m.tys.intern(TyKind::Enum(TypeId(1)));
    let field = ExprKind::Field { base: Box::new(Expr::new(e, sp(), ExprKind::Zeroed)), index: 0 };
    rejected(&with_g(m, Expr::new(Types::U32, at(), field)), Rule::V01, "field access on `E`");
}

/// The terms of the tables of a function, one past the end of each table,
/// and the arm of a `Switch` past its variants.
#[test]
fn each_term_of_the_tables_is_checked() {
    // A function with no body: its result, its parameter.
    let unit = || lit(Types::UNIT, Lit::Unit);
    let x = |ty| Param { local: LocalId(0), mode: Mode::Borrow, ty };
    let xs = || vec![Local::value("x", Types::U32)];
    for (params, ret) in [(vec![], foreign(300)), (vec![x(foreign(300))], Types::UNIT)] {
        let mut m = base();
        m.fns.push(FnDef { body: None, ..f("g", params, ret, xs(), vec![], unit()) });
        rejected(&m, Rule::V20, "ty 300 out of range");
    }
    // The type of a parameter is a table's (V-20), not a mismatch (V-01).
    let mut m = base();
    m.fns.push(f("g", vec![x(foreign(300))], Types::UNIT, xs(), vec![], unit()));
    rejected(&m, Rule::V20, "ty 300 out of range");
    // One past the end: a field, a payload, a copy, a fn, a message.
    let mut m = base();
    let n = m.tys.kinds().len();
    m.types.push(TypeDef { name: "T".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), foreign(n))] } });
    rejected_as_is(&m, Rule::V20, &format!("ty {n} out of range"));
    let mut m = base();
    m.types
        .push(TypeDef { name: "T".into(), kind: TypeDefKind::Enum { variants: vec![("A".into(), vec![foreign(n)])] } });
    rejected_as_is(&m, Rule::V20, &format!("ty {n} out of range"));
    let copy = |fn_, ty| MoveSite { fn_, span: sp(), ty, bytes: 4, kind: MoveKind::Copy };
    let mut m = with_g(base(), one());
    m.moves.push(copy(FnId(0), foreign(n)));
    rejected_as_is(&m, Rule::V20, &format!("ty {n} out of range"));
    let mut m = with_g(base(), one());
    m.moves.push(copy(FnId(1), Types::U32));
    rejected(&m, Rule::V20, "fn 1 out of range");
    let panic = ExprKind::Panic { msg: MsgId(0), origin: PanicOrigin::Panic, shown: vec![] };
    rejected(&with_stmt(base(), Expr::new(Types::UNIT, at(), panic)), Rule::V20, "panic message out of range");
    // An arm of a tag at the number of the variants, or past it.
    for tag in [1, 2, 300] {
        let mut m = base();
        let e = m.tys.intern(TyKind::Enum(TypeId(1)));
        let a = Expr::new(e, sp(), ExprKind::Variant { ty: TypeId(1), tag: 0, fields: vec![one()] });
        let arm = |t| (t, Block { stmts: vec![], value: Some(Box::new(one())) });
        let sw = ExprKind::Switch { scrutinee: Box::new(a), arms: vec![arm(0), arm(tag)], default: None };
        rejected(&with_g(m, Expr::new(Types::U32, sp(), sw)), Rule::V08, "out of range or duplicated");
    }
}

/// Each function and each type of a flow is in range.
#[test]
fn each_function_and_type_of_a_flow_is_checked() {
    use crate::lower::flow::FlowMeta;
    use onsa_sema::clock::ClockStage;
    let m = crate::tests::core("pub flow f(x: F32 at sample, g: F32 at block) -> F32 at sample {\n  x * g\n}\n");
    let fl = &m.flows[0];
    assert!(!fl.params.is_empty() && !fl.sig_inputs.is_empty() && !fl.outputs.is_empty());
    let far = foreign(m.tys.kinds().len() + 7);
    type Set = fn(&mut FlowMeta, CTy);
    let sets: [(&str, Set); 16] = [
        ("config", |fl, _| fl.fns.config = TypeId(999)),
        ("params", |fl, _| fl.fns.params = TypeId(999)),
        ("out", |fl, _| fl.fns.out = TypeId(999)),
        ("init", |fl, _| fl.fns.init = FnId(999)),
        ("reset", |fl, _| fl.fns.reset = FnId(999)),
        ("ctl", |fl, _| fl.fns.ctl = FnId(999)),
        ("process", |fl, _| fl.fns.process = Some(FnId(999))),
        ("process_inplace", |fl, _| fl.fns.process_inplace = Some(FnId(999))),
        ("render", |fl, _| fl.fns.render = Some(FnId(999))),
        ("params_default", |fl, _| fl.fns.params_default = Some(FnId(999))),
        ("reset_kept", |fl, _| fl.fns.reset_kept = Some(FnId(999))),
        ("stages", |fl, _| fl.fns.stages = vec![(ClockStage::SAMPLE, FnId(999))]),
        ("events", |fl, _| fl.fns.events.push((ClockStage::SAMPLE, FnId(999)))),
        ("a param", |fl, t| fl.params[0].1 = t),
        ("a signal input", |fl, t| fl.sig_inputs[0].1 = t),
        ("an output", |fl, t| fl.outputs[0].1 = t),
    ];
    for (name, set) in sets {
        let mut m = m.clone();
        set(&mut m.flows[0], far);
        let err = verify(&m).expect_err(name);
        assert!(err.rule == Rule::V20 && err.fn_name == m.flows[0].name, "{name}: {err}");
    }
}

fn st(span: Span, kind: StmtKind) -> Stmt {
    Stmt { span, kind }
}

fn block(stmts: Vec<Stmt>, value: Expr) -> Block {
    Block { stmts, value: Some(Box::new(value)) }
}

/// A block expression of `stmts` and then the value `value`.
fn inline(stmts: Vec<Stmt>, value: Expr) -> Expr {
    Expr::new(value.ty, sp(), ExprKind::Block(block(stmts, value)))
}

fn yes() -> Expr {
    lit(Types::BOOL, Lit::Bool(true))
}

/// `g` of the locals `a` and `b` (`U32`): its statements `stmts`, then the
/// value of the local `l`, read at `at()`.
fn reads(l: u32, stmts: Vec<Stmt>) -> Module {
    let mut m = base();
    m.messages.push("m".into());
    let ab = vec![Local::value("a", Types::U32), Local::value("b", Types::U32)];
    m.fns.push(f("g", vec![], Types::U32, ab, stmts, Expr::new(Types::U32, at(), ExprKind::Local(LocalId(l)))));
    m
}

/// V-04: a local is seen from its definition to the end of its scope. A
/// block a backend opens and a child not always evaluated close the names
/// defined in them; a block expression does not (W8-02, the `tick` of a
/// flow); an assignment defines nothing.
#[test]
fn a_local_is_seen_in_its_scope_only() {
    let let_a = || st(sp(), StmtKind::Let(LocalId(0), one()));
    let unit = || lit(Types::UNIT, Lit::Unit);
    let empty = || block(vec![], unit());
    let expr = |e| st(sp(), StmtKind::Expr(e));
    let if_expr = |then| ExprKind::IfExpr { cond: Box::new(yes()), then, else_: empty() };
    let logic = ExprKind::Logic { op: LogicOp::And, lhs: Box::new(yes()), rhs: Box::new(inline(vec![let_a()], yes())) };
    let panic =
        ExprKind::Panic { msg: MsgId(0), origin: PanicOrigin::Panic, shown: vec![inline(vec![let_a()], one())] };
    let past = [
        ("an arm of an if", st(sp(), StmtKind::If(yes(), block(vec![let_a()], unit()), empty()))),
        ("an arm of an if expression", expr(Expr::new(Types::UNIT, sp(), if_expr(block(vec![let_a()], unit()))))),
        ("the body of a while", st(sp(), StmtKind::While(yes(), block(vec![let_a()], unit())))),
        ("the right operand of a logic", expr(Expr::new(Types::BOOL, sp(), logic))),
        ("the condition of a while", st(sp(), StmtKind::While(inline(vec![let_a()], yes()), empty()))),
        ("a value a panic shows", expr(Expr::new(Types::UNIT, sp(), panic))),
    ];
    for (name, s) in past {
        let err = rejected(&reads(0, vec![s]), Rule::V04, "local `a` read before definition");
        assert_eq!(err.span, Some(at()), "{name}: {err}");
    }
    // The condition of a while is not seen in its body.
    let body = block(vec![st(sp(), StmtKind::Expr(Expr::new(Types::U32, at(), ExprKind::Local(LocalId(0)))))], unit());
    let s = st(sp(), StmtKind::While(inline(vec![let_a()], yes()), body));
    assert_eq!(rejected(&reads(1, vec![let_b(), s]), Rule::V04, "local `a` read").span, Some(at()));
    // The variable of a `for` past its body; an assignment to a local never defined.
    let for_ = st(sp(), StmtKind::for_excluded(LocalId(1), one(), one(), empty()));
    assert_eq!(rejected(&reads(1, vec![for_]), Rule::V04, "local `b` read before").span, Some(at()));
    let assign = st(at(), StmtKind::Assign(Place::Local(LocalId(0)), one()));
    assert_eq!(rejected(&reads(0, vec![assign]), Rule::V04, "local `a` written before").span, Some(at()));
    // Seen: past a block expression, a condition of an if in its arms and
    // past it, a second `let`, the variable of a `for` in its body.
    let mut m = reads(0, vec![expr(inline(vec![let_a()], unit()))]);
    let cond = inline(vec![let_a()], yes());
    let arm = || block(vec![], Expr::new(Types::U32, sp(), ExprKind::Local(LocalId(0))));
    let if_ = ExprKind::IfExpr { cond: Box::new(cond), then: arm(), else_: arm() };
    let ab = m.fns[0].locals.clone();
    m.fns.push(f("h", vec![], Types::U32, ab.clone(), vec![expr(Expr::new(Types::U32, sp(), if_))], read(0)));
    let read_b = block(vec![expr(read(1))], unit());
    let for_ = st(sp(), StmtKind::for_excluded(LocalId(1), one(), one(), read_b));
    m.fns.push(f("k", vec![], Types::U32, ab, vec![let_a(), let_a(), for_], read(0)));
    m.fill_all_facts();
    verify(&m).expect("seen");
}

fn read(l: u32) -> Expr {
    Expr::new(Types::U32, sp(), ExprKind::Local(LocalId(l)))
}

fn let_b() -> Stmt {
    st(sp(), StmtKind::Let(LocalId(1), one()))
}

/// V-05: neither an assignment nor an `inout` argument writes a place of a
/// parameter taken by borrow; one taken by `inout` or by move is written.
#[test]
fn a_borrowed_parameter_is_not_written() {
    let arr = |m: &mut Module| m.tys.intern(TyKind::Array(Types::U32, 2));
    let g = |m: &mut Module, mode, ty, stmts| {
        let x = Param { local: LocalId(0), mode, ty };
        let unit = lit(Types::UNIT, Lit::Unit);
        m.fns.push(f("g", vec![x], Types::UNIT, vec![Local::value("x", ty)], stmts, unit));
    };
    let mut m = base();
    g(&mut m, Mode::Borrow, Types::U32, vec![st(at(), StmtKind::Assign(Place::Local(LocalId(0)), one()))]);
    assert_eq!(rejected(&m, Rule::V05, "write to the borrowed parameter `x`").span, Some(at()));
    let mut m = base();
    let t = arr(&mut m);
    let elem = Place::Index(Box::new(Place::Local(LocalId(0))), Box::new(one()), sp(), Bounds::Checked);
    g(&mut m, Mode::Borrow, t, vec![st(at(), StmtKind::Assign(elem, one()))]);
    assert_eq!(rejected(&m, Rule::V05, "write to the borrowed parameter `x`").span, Some(at()));
    // `callee(inout y: U32)` given `x`, or `x[0]` of an array.
    let callee = |m: &mut Module| {
        let y = Param { local: LocalId(0), mode: Mode::Inout, ty: Types::U32 };
        let unit = lit(Types::UNIT, Lit::Unit);
        m.fns.push(f("callee", vec![y], Types::UNIT, vec![Local::value("y", Types::U32)], vec![], unit));
    };
    let pass = |x: Expr| {
        let call = ExprKind::Call { fn_: FnId(0), args: vec![Arg { mode: Mode::Inout, expr: x }] };
        vec![st(sp(), StmtKind::Expr(Expr::new(Types::UNIT, at(), call)))]
    };
    let mut m = base();
    callee(&mut m);
    g(&mut m, Mode::Borrow, Types::U32, pass(read(0)));
    assert_eq!(rejected(&m, Rule::V05, "write to the borrowed parameter `x`").span, Some(at()));
    let mut m = base();
    callee(&mut m);
    let t = arr(&mut m);
    let base_x = Box::new(Expr::new(t, sp(), ExprKind::Local(LocalId(0))));
    let index = ExprKind::Index { base: base_x, index: Box::new(one()), bounds: Bounds::Checked };
    g(&mut m, Mode::Borrow, t, pass(Expr::new(Types::U32, sp(), index)));
    rejected(&m, Rule::V05, "write to the borrowed parameter `x`");
    // Written: a parameter by `inout`, one by move.
    for mode in [Mode::Inout, Mode::Move] {
        let mut m = base();
        callee(&mut m);
        let mut stmts = pass(read(0));
        stmts.push(st(sp(), StmtKind::Assign(Place::Local(LocalId(0)), one())));
        g(&mut m, mode, Types::U32, stmts);
        m.fill_all_facts();
        verify(&m).expect("written");
    }
}

/// V-07: a `break` is in the body of a loop. The condition of a `while` is
/// outside its body (§7): there a `break` is of the loop around it, and
/// with none it is rejected.
#[test]
fn a_break_is_in_the_body_of_a_loop() {
    let unit = || lit(Types::UNIT, Lit::Unit);
    let breaks = || {
        let leave = block(vec![st(at(), StmtKind::Break)], unit());
        let cond = inline(vec![st(sp(), StmtKind::If(yes(), leave, block(vec![], unit())))], yes());
        st(sp(), StmtKind::While(cond, block(vec![], unit())))
    };
    let mut m = base();
    m.fns.push(f("g", vec![], Types::UNIT, vec![], vec![breaks()], unit()));
    assert_eq!(rejected(&m, Rule::V07, "break / continue outside a loop").span, Some(at()));
    let mut m = base();
    let outer = st(sp(), StmtKind::While(yes(), block(vec![breaks()], unit())));
    m.fns.push(f("g", vec![], Types::UNIT, vec![], vec![outer], unit()));
    m.fill_all_facts();
    verify(&m).expect("of the loop around");
}

/// The loop is left: a `break` after a `while` is outside a loop.
#[test]
fn a_break_after_a_loop_is_outside_it() {
    let unit = || lit(Types::UNIT, Lit::Unit);
    let mut m = base();
    let looped = st(sp(), StmtKind::While(yes(), block(vec![], unit())));
    m.fns.push(f("g", vec![], Types::UNIT, vec![], vec![looped, st(at(), StmtKind::Break)], unit()));
    assert_eq!(rejected(&m, Rule::V07, "break / continue outside a loop").span, Some(at()));
}

/// A local seen outside stays seen past an inner scope that `let`s it again.
#[test]
fn a_second_let_in_an_arm_does_not_end_with_the_arm() {
    let unit = || lit(Types::UNIT, Lit::Unit);
    let let_a = || st(sp(), StmtKind::Let(LocalId(0), one()));
    let arm = block(vec![let_a()], unit());
    let s = st(sp(), StmtKind::If(yes(), arm, block(vec![], unit())));
    let mut m = reads(0, vec![let_a(), s]);
    m.fill_all_facts();
    verify(&m).expect("seen past the arm");
}

/// The local of a `let` is not seen in its own value.
#[test]
fn a_let_is_not_seen_in_its_value() {
    let s = st(sp(), StmtKind::Let(LocalId(0), Expr::new(Types::U32, at(), ExprKind::Local(LocalId(0)))));
    assert_eq!(rejected(&reads(1, vec![s]), Rule::V04, "local `a` read before definition").span, Some(at()));
}

/// An `inout` argument of a field of a borrowed parameter.
#[test]
fn a_field_of_a_borrowed_parameter_is_not_written() {
    let mut m = base();
    let s = m.tys.intern(TyKind::Struct(TypeId(0)));
    let unit = || lit(Types::UNIT, Lit::Unit);
    let y = Param { local: LocalId(0), mode: Mode::Inout, ty: Types::U32 };
    m.fns.push(f("callee", vec![y], Types::UNIT, vec![Local::value("y", Types::U32)], vec![], unit()));
    let x = Param { local: LocalId(0), mode: Mode::Borrow, ty: s };
    let base_x = Box::new(Expr::new(s, sp(), ExprKind::Local(LocalId(0))));
    let field = Expr::new(Types::U32, sp(), ExprKind::Field { base: base_x, index: 0 });
    let call = ExprKind::Call { fn_: FnId(0), args: vec![Arg { mode: Mode::Inout, expr: field }] };
    let stmts = vec![st(sp(), StmtKind::Expr(Expr::new(Types::UNIT, at(), call)))];
    m.fns.push(f("g", vec![x], Types::UNIT, vec![Local::value("x", s)], stmts, unit()));
    rejected(&m, Rule::V05, "write to the borrowed parameter `x`");
}

/// The value of a block in a loop is checked: a local read there before
/// its definition (V-04).
#[test]
fn a_value_of_a_block_in_a_loop_is_checked() {
    let value = Expr::new(Types::U32, at(), ExprKind::Local(LocalId(0)));
    let s = st(sp(), StmtKind::While(yes(), block(vec![], value)));
    assert_eq!(rejected(&reads(1, vec![let_b(), s]), Rule::V04, "local `a` read before").span, Some(at()));
}

/// A type of the form `shape`, its element `F32`; `inv` gives another type,
/// which is not of it.
fn of_shape(m: &mut Module, shape: Shape, inv: bool) -> CTy {
    let f32 = Types::float(FloatKind::F32);
    if inv {
        return if shape == Shape::Bool { Types::U32 } else { Types::BOOL };
    }
    match shape {
        Shape::Int(k) => Types::int(k),
        Shape::Float(k) => Types::float(k),
        Shape::Bool => Types::BOOL,
        Shape::Unit => Types::UNIT,
        Shape::Parts(k) => m.tys.intern(TyKind::Tuple(vec![Types::BOOL, Types::int(k)].into())),
        Shape::Seq | Shape::SpanOf | Shape::SpanOfNum => m.tys.intern(TyKind::Span(f32)),
        Shape::BufOf => m.tys.intern(TyKind::Buf(f32)),
        Shape::Elem => f32,
        Shape::Any => Types::U32,
    }
}

/// How a call of a primitive is broken (V-02).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Break {
    None,
    Count,
    Mode,
    Operand,
    Value,
    Near(usize, bool),
}

/// `g`, an `rt` function when `rt`, whose value is a call of `prim` at
/// `at()`, its operands the `inout` parameters of `g` of the forms of its
/// row, broken by `how`.
fn calls(prim: &Prim, how: Break, rt: bool) -> Module {
    let mut m = base();
    let sig = sig(prim);
    // The first operand the table reads the type of, broken by `Operand`.
    let read = sig.args.iter().position(|&(_, s)| s != Shape::Any);
    let (mut params, mut locals, mut args) = (Vec::new(), Vec::new(), Vec::new());
    for (i, &(mode, shape)) in sig.args.iter().enumerate() {
        let ty = match how {
            Break::Near(p, e) if p == i => near(&mut m, shape, e).expect("near"),
            _ => of_shape(&mut m, shape, how == Break::Operand && read == Some(i)),
        };
        let mode = match mode {
            _ if how != Break::Mode || i > 0 => mode,
            Mode::Inout => Mode::Borrow,
            _ => Mode::Inout,
        };
        params.push(Param { local: LocalId(i as u32), mode: Mode::Inout, ty });
        locals.push(Local::value(format!("x{i}"), ty));
        args.push(Arg { mode, expr: Expr::new(ty, sp(), ExprKind::Local(LocalId(i as u32))) });
    }
    if how == Break::Count && args.pop().is_none() {
        args.push(Arg { mode: Mode::Borrow, expr: one() });
    }
    let ret = match how {
        Break::Near(p, e) if p == sig.args.len() => near(&mut m, sig.ret, e).expect("near"),
        _ => of_shape(&mut m, sig.ret, how == Break::Value),
    };
    let value = Expr::new(ret, at(), ExprKind::Prim { prim: prim.clone(), args });
    m.fns.push(f("g", params, ret, locals, vec![], value));
    let g = m.fns.last_mut().expect("g");
    (g.sret, g.rt) = (m.tys.is_aggregate(ret), rt);
    m
}

/// V-02: a call of each primitive of the forms of its row is of the table,
/// and one with an operand too few (or too many), an operand of another
/// mode, an operand or the value of another type is rejected at the call.
#[test]
fn the_operands_and_the_value_of_a_primitive_are_of_its_row() {
    let prims = super::prim_tests::every_prim();
    let mut broken = 0;
    for prim in &prims {
        let sig = sig(prim);
        let mut m = calls(prim, Break::None, false);
        m.fill_all_facts();
        verify(&m).unwrap_or_else(|e| panic!("{}: {e}", prim.name()));
        for (how, message) in [
            (Break::Count, "operand(s), expected"),
            (Break::Mode, "the mode of operand 0"),
            (Break::Operand, "is not of the form"),
            (Break::Value, "the value of"),
        ] {
            let none = sig.args.is_empty() && how != Break::Count;
            if none
                || (how == Break::Operand && sig.args.iter().all(|&(_, s)| s == Shape::Any))
                || (how == Break::Value && sig.ret == Shape::Any)
            {
                continue;
            }
            let err = rejected(&calls(prim, how, false), Rule::V02, message);
            assert_eq!(err.span, Some(at()), "{how:?} of {}: {err}", prim.name());
            broken += 1;
        }
    }
    assert!(prims.len() > 100 && broken > 3 * prims.len(), "{} primitives, {broken} broken", prims.len());
}

/// V-02: the element of the forms of a row is one type; `add_from` adds numbers.
#[test]
fn the_element_of_the_operands_of_a_primitive_is_one() {
    let mut m = base();
    let (f32, f64) = (Types::float(FloatKind::F32), Types::float(FloatKind::F64));
    let (a, b) = (m.tys.intern(TyKind::Span(f32)), m.tys.intern(TyKind::Span(f64)));
    let bools = m.tys.intern(TyKind::Span(Types::BOOL));
    let call = |m: &Module, prim: Prim, tys: [CTy; 2]| {
        let mut m = m.clone();
        let params = (0..2).map(|i| Param { local: LocalId(i), mode: Mode::Inout, ty: tys[i as usize] }).collect();
        let locals = tys.iter().map(|&ty| Local::value("x", ty)).collect();
        let modes = [Mode::Inout, Mode::Borrow];
        let args =
            (0..2).map(|i| Arg { mode: modes[i], expr: Expr::new(tys[i], sp(), ExprKind::Local(LocalId(i as u32))) });
        let value = Expr::new(Types::UNIT, at(), ExprKind::Prim { prim, args: args.collect() });
        m.fns.push(f("g", params, Types::UNIT, locals, vec![], value));
        m
    };
    let err =
        rejected(&call(&m, Prim::CopyFrom, [a, b]), Rule::V02, "operand 1 of `Span[F64]` is not of the form SpanOf");
    assert_eq!(err.span, Some(at()));
    rejected(&call(&m, Prim::Fill, [a, f64]), Rule::V02, "operand 1 of `F64` is not of the form Elem");
    rejected(
        &call(&m, Prim::AddFrom, [bools, bools]),
        Rule::V02,
        "operand 0 of `Span[Bool]` is not of the form SpanOfNum",
    );
    let mut ok = call(&m, Prim::Fill, [bools, Types::BOOL]);
    ok.fill_all_facts();
    verify(&ok).expect("a span of Bool filled");
    let mut ok = call(&m, Prim::AddFrom, [b, b]);
    ok.fill_all_facts();
    verify(&ok).expect("added");
}

/// V-03: a cast is a widening of §3.3, as sema judges it: not a narrowing,
/// a signed integer to an unsigned one, an `F64` to an `F32` or an integer
/// wider than the mantissa to a float.
#[test]
fn a_cast_is_a_widening() {
    let (int, float) = (Types::int, Types::float);
    let cast = |from: CTy, to: CTy| {
        let x = match from {
            t if t == float(FloatKind::F32) => lit(t, Lit::F32(1.0)),
            t if t == float(FloatKind::F64) => lit(t, Lit::F64(1.0)),
            t => lit(t, Lit::Int(1)),
        };
        with_g(base(), Expr::new(to, at(), ExprKind::Cast(Box::new(x))))
    };
    for (from, to, shown) in [
        (int(IntKind::I32), int(IntKind::I16), "`I32` as `I16`"),
        (int(IntKind::I8), int(IntKind::U16), "`I8` as `U16`"),
        (float(FloatKind::F64), float(FloatKind::F32), "`F64` as `F32`"),
        (int(IntKind::I32), float(FloatKind::F32), "`I32` as `F32`"),
        (int(IntKind::U32), int(IntKind::I32), "`U32` as `I32`"),
    ] {
        let err = rejected(&cast(from, to), Rule::V03, &format!("{shown} is no widening"));
        assert_eq!(err.span, Some(at()), "{err}");
    }
    for (from, to) in [
        (int(IntKind::U8), int(IntKind::I16)),
        (int(IntKind::I16), float(FloatKind::F32)),
        (int(IntKind::U32), float(FloatKind::F64)),
        (float(FloatKind::F32), float(FloatKind::F64)),
        (int(IntKind::I8), int(IntKind::I64)),
    ] {
        let mut m = cast(from, to);
        m.fill_all_facts();
        verify(&m).unwrap_or_else(|e| panic!("{e}"));
    }
}

/// V-06: an `rt` function calls the primitives of the `rt` declarations
/// alone (`Buf.zeroed` allocates; `assert_near` and the functions of
/// `std.test` are no `rt`), and the float `%`.
#[test]
fn an_rt_function_calls_rt_primitives_alone() {
    let (mut kept, mut out) = (0, 0);
    for prim in super::prim_tests::every_prim() {
        let mut m = calls(&prim, Break::None, true);
        m.fill_all_facts();
        if prim.rt() {
            verify(&m).unwrap_or_else(|e| panic!("{}: {e}", prim.name()));
            kept += 1;
        } else {
            let err = rejected(&m, Rule::V06, &format!("non-rt primitive `{}`", prim.name()));
            assert_eq!(err.span, Some(at()), "{err}");
            out += 1;
        }
    }
    assert!(!Prim::BufZeroed.rt() && !Prim::AssertNear.rt() && Prim::Math(MathFn::Fmod, FloatKind::F32).rt());
    assert!(kept > 100 && out == 6, "{kept} rt, {out} not");
}

/// A type near the form `shape`: of the same family but another kind, or of
/// the form with another element (`elem`).
fn near(m: &mut Module, shape: Shape, elem: bool) -> Option<CTy> {
    let (f32, f64) = (Types::float(FloatKind::F32), Types::float(FloatKind::F64));
    let other = |k: IntKind| Types::int(if k == IntKind::U64 { IntKind::U32 } else { IntKind::U64 });
    Some(match (shape, elem) {
        (Shape::Int(k), false) => other(k),
        (Shape::Float(k), false) => Types::float(if k == FloatKind::F64 { FloatKind::F32 } else { FloatKind::F64 }),
        (Shape::Parts(k), false) => m.tys.intern(TyKind::Tuple(vec![Types::BOOL, other(k)].into())),
        (Shape::SpanOf | Shape::SpanOfNum, false) => m.tys.intern(TyKind::Buf(f32)),
        (Shape::BufOf, false) => m.tys.intern(TyKind::Span(f32)),
        (Shape::SpanOf | Shape::SpanOfNum | Shape::Seq, true) => m.tys.intern(TyKind::Span(f64)),
        (Shape::BufOf, true) => m.tys.intern(TyKind::Buf(f64)),
        (Shape::Elem, true) => f64,
        _ => return None,
    })
}

#[test]
fn a_near_miss_of_an_operand_or_the_value_is_rejected() {
    let carries = |s: Shape| matches!(s, Shape::Seq | Shape::SpanOf | Shape::SpanOfNum | Shape::BufOf | Shape::Elem);
    let mut n = 0;
    for prim in super::prim_tests::every_prim() {
        let sig = sig(&prim);
        let shapes: Vec<Shape> = sig.args.iter().map(|&(_, s)| s).chain([sig.ret]).collect();
        let linked = shapes.iter().filter(|&&s| carries(s)).count() >= 2;
        for (pos, &shape) in shapes.iter().enumerate() {
            for elem in [false, true] {
                if (elem && !linked) || near(&mut base(), shape, elem).is_none() {
                    continue;
                }
                let err = rejected(&calls(&prim, Break::Near(pos, elem), false), Rule::V02, "");
                assert_eq!(err.span, Some(at()), "{} {pos} {elem}", prim.name());
                n += 1;
            }
        }
    }
    assert!(n > 150, "{n}");
}

// ---------------------------------------------------------------- lowering verifies its output

/// Lowering verifies the Core it makes (R-82, W8-02 U5c): what it gives back
/// passes, and a Core that breaks a rule at its end comes back as
/// `LowerFailure::Verify` with the rule, the position of the node and the
/// Core of the item, not as a module.
#[test]
fn lowering_gives_back_a_verified_core_or_the_failure() {
    let src = "const K: I32 = 3\n\npub fn f(x: I32) -> I32 {\n  x + K\n}\n";
    let mut m = crate::lower::verified(super::core(src)).expect("verified");
    let f = m.fns.iter_mut().find(|f| f.name == "t.f").expect("t.f");
    let span = f.span;
    f.body = Some(Block { stmts: Vec::new(), value: Some(Box::new(lit(Types::BOOL, Lit::Bool(true)))) });
    let Err(crate::LowerFailure::Verify { error, item_core }) = crate::lower::verified(m) else {
        panic!("a broken Core is not a verify failure")
    };
    assert_eq!((error.rule, error.span, error.fn_name.as_str()), (Rule::V01, Some(span), "t.f"), "{error}");
    assert!(item_core.starts_with("fn t.f(") && !item_core.contains("const t.K"), "{item_core}");
}
