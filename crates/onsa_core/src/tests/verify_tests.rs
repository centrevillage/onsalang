//! The verifier matches the kinds of the types of a module one level deep
//! without interning (W8-14): a struct literal, a variant, a field, the view
//! of a `Span` and an argument of a call of another type are rejected, each
//! with the type it has and the one it is in.

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::verify;

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn lit(ty: CTy, l: Lit) -> Expr {
    Expr::new(ty, sp(), ExprKind::Lit(l))
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

fn rejected(m: &Module, message: &str) {
    let err = verify(m).expect_err(message);
    assert!(err.message.contains(message), "{err}");
}

#[test]
fn a_struct_literal_or_a_variant_of_another_type_is_rejected() {
    let one = || vec![lit(Types::U32, Lit::Int(1))];
    let m = base();
    rejected(
        &with_g(m, Expr::new(Types::BOOL, sp(), ExprKind::Struct { ty: TypeId(0), fields: one() })),
        "struct literal: type mismatch `S` vs `Bool`",
    );
    let mut m = base();
    m.types.push(TypeDef { name: "T".into(), kind: TypeDefKind::Struct { fields: vec![("a".into(), Types::U32)] } });
    let t = m.tys.intern(TyKind::Struct(TypeId(2)));
    rejected(
        &with_g(m, Expr::new(t, sp(), ExprKind::Struct { ty: TypeId(0), fields: one() })),
        "struct literal: type mismatch `S` vs `T`",
    );
    let variant = ExprKind::Variant { ty: TypeId(1), tag: 0, fields: one() };
    rejected(&with_g(base(), Expr::new(Types::BOOL, sp(), variant)), "variant: type mismatch `E` vs `Bool`");
}

#[test]
fn a_field_a_view_or_an_argument_of_another_type_is_rejected() {
    let mut m = base();
    let s = m.tys.intern(TyKind::Struct(TypeId(0)));
    let fields = vec![lit(Types::BOOL, Lit::Bool(true))];
    rejected(
        &with_g(m, Expr::new(s, sp(), ExprKind::Struct { ty: TypeId(0), fields })),
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
    rejected(&m, "span: type mismatch `Span[U32]` vs `Span[U8]`");
    // A `Bool` for the `U32` of `callee`.
    let mut m = base();
    let x = Param { local: LocalId(0), mode: Mode::Borrow, ty: Types::U32 };
    let read = Expr::new(Types::U32, sp(), ExprKind::Local(LocalId(0)));
    m.fns.push(f("callee", vec![x], Types::U32, vec![Local { name: "x".into(), ty: Types::U32 }], vec![], read));
    let args = vec![Arg { mode: Mode::Borrow, expr: lit(Types::BOOL, Lit::Bool(true)) }];
    rejected(
        &with_g(m, Expr::new(Types::U32, sp(), ExprKind::Call { fn_: FnId(0), args })),
        "argument: type mismatch `Bool` vs `U32`",
    );
}
