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
use crate::prim::Prim;
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
    let one = || vec![lit(Types::U32, Lit::Int(1))];
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
    let variant = ExprKind::Variant { ty: TypeId(1), tag: 0, fields: one() };
    rejected(&with_g(base(), Expr::new(Types::BOOL, sp(), variant)), Rule::V01, "variant: type mismatch `E` vs `Bool`");
}

#[test]
fn a_field_a_view_or_an_argument_of_another_type_is_rejected() {
    let mut m = base();
    let s = m.tys.intern(TyKind::Struct(TypeId(0)));
    let fields = vec![lit(Types::BOOL, Lit::Bool(true))];
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
    m.fns.push(f("g", vec![], view8, vec![Local { name: "a".into(), ty: arr }], vec![let_], view));
    rejected(&m, Rule::V01, "span: type mismatch `Span[U32]` vs `Span[U8]`");
    // A `Bool` for the `U32` of `callee`.
    let mut m = base();
    let x = Param { local: LocalId(0), mode: Mode::Borrow, ty: Types::U32 };
    let read = Expr::new(Types::U32, sp(), ExprKind::Local(LocalId(0)));
    m.fns.push(f("callee", vec![x], Types::U32, vec![Local { name: "x".into(), ty: Types::U32 }], vec![], read));
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
    let xs = || vec![Local { name: "x".into(), ty: Types::U32 }];
    let unit = || lit(Types::UNIT, Lit::Unit);
    let mut m = base();
    m.fns.push(f("t", vec![x()], Types::UNIT, xs(), vec![], unit()));
    m.fns[0].test = Some(TestMark { module: "m".into(), name: "t".into() });
    rejected(&m, Rule::V01, "a test function with parameters or a value");
    let cast = ExprKind::Cast(Box::new(lit(Types::BOOL, Lit::Bool(true))));
    rejected(&with_g(base(), Expr::new(Types::U32, sp(), cast)), Rule::V03, "cast between non-numeric types");
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
    rejected(&rt(with_stmt(base(), Expr::new(Types::UNIT, sp(), zeroed))), Rule::V06, "rt function allocates");
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
    m.fns[0].locals.push(Local { name: "x".into(), ty: foreign(300) });
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
    let all = [V01, V02, V03, V04, V05, V06, V07, V08, V09, V10, V11, V12, V13, V14, V15, V16, V17, V18, V19, V20];
    let shown: Vec<String> = all.iter().map(|r| r.to_string()).collect();
    assert_eq!(shown, (1..=20).map(|i| format!("V-{i:02}")).collect::<Vec<_>>());
}

/// The position of an error in a statement, past a statement at the node
/// around it, and in the initializer of a `const`.
#[test]
fn an_error_of_a_statement_or_a_const_has_its_position() {
    let let_ = Stmt { span: at(), kind: StmtKind::Let(LocalId(0), lit(Types::BOOL, Lit::Bool(true))) };
    let mut m = base();
    let a = vec![Local { name: "a".into(), ty: Types::U32 }];
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
    let xs = || vec![Local { name: "x".into(), ty: Types::U32 }];
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
