//! V-22 (W8-02 U5b): the Core of an item is at most `CORE_DEPTH_LIMIT`
//! nodes deep. The limit itself passes and one node more is rejected, in a
//! Core made by hand, before the other rules and with no dump of its item
//! (a Core lowered too deep: `onsa_tests/tests/verify.rs`). Each Core is
//! made, verified and dropped on a thread of a large stack
//! (`onsa_diag::stack`): the ones made here are up to 1401 deep.

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::verify::depth::deepest;
use crate::{CORE_DEPTH_LIMIT, Rule, verify};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// `!` applied `n` times to `true`, which is at `at`: `n + 1` nodes deep.
fn nots(n: u32, at: Span) -> Expr {
    let mut e = Expr::new(Types::BOOL, at, ExprKind::Lit(Lit::Bool(true)));
    for _ in 0..n {
        e = Expr::new(Types::BOOL, sp(), ExprKind::Unary(UnOp::Not, Box::new(e)));
    }
    e
}

/// A module of the function `g` of the value `value` (its body is one
/// node more) and the `const` `K` of `init`.
fn module(value: Expr, init: Expr) -> Module {
    let mut m = Module::default();
    let body = Some(Block { stmts: Vec::new(), value: Some(Box::new(value)) });
    m.fns.push(FnDef {
        name: "g".into(),
        params: Vec::new(),
        ret: Types::BOOL,
        sret: false,
        rt: false,
        locals: Vec::new(),
        body,
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    });
    m.consts.push(ConstDef { name: "K".into(), ty: Types::BOOL, init });
    m.fill_all_facts();
    m
}

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    onsa_diag::stack::spawn("depth", f).unwrap().join().unwrap()
}

#[test]
fn the_limit_passes_and_one_node_more_is_rejected_at_that_node() {
    on_large_stack(|| {
        let at = Span::new(FileId(0), 7, 9);
        // The value the conditions of the limit were measured for (its doc).
        let limit = 1400;
        assert_eq!(CORE_DEPTH_LIMIT, limit);
        // The body is one node above its value.
        let m = module(nots(limit - 2, sp()), nots(limit - 1, sp()));
        assert_eq!(deepest(&m), limit);
        assert_eq!(verify(&m), Ok(()));
        let past = [(module(nots(limit - 1, at), nots(0, sp())), "g"), (module(nots(0, sp()), nots(limit, at)), "K")];
        for (m, item) in past {
            let e = verify(&m).expect_err("one node past the limit");
            assert_eq!((e.rule, e.span, e.fn_name.as_str()), (Rule::V22, Some(at), item), "{e}");
            assert!(e.message.contains(&format!("deeper than {limit}")), "{e}");
        }
    })
}

/// V-22 comes before the other rules, which recurse: a Core that also
/// breaks V-01 is rejected by V-22, and its item is not dumped.
#[test]
fn a_core_too_deep_is_rejected_first_and_has_no_dump() {
    on_large_stack(|| {
        let wrong = Expr::new(Types::U32, sp(), ExprKind::Unary(UnOp::Not, Box::new(nots(CORE_DEPTH_LIMIT, sp()))));
        let (e, dump) = crate::verify::with_item(&module(nots(0, sp()), wrong)).expect_err("too deep");
        assert_eq!((e.rule, e.fn_name.as_str(), dump.as_str()), (Rule::V22, "K", ""), "{e}");
        // Of a Core in the limit, the other rule, with the dump.
        let wrong = Expr::new(Types::U32, sp(), ExprKind::Unary(UnOp::Not, Box::new(nots(0, sp()))));
        let (e, dump) = crate::verify::with_item(&module(nots(0, sp()), wrong)).expect_err("of the wrong type");
        assert_eq!(e.rule, Rule::V01, "{e}");
        assert!(dump.starts_with("const K"), "{dump}");
    })
}

// ---------------------------------------------------------------- every position of a child

fn lit() -> Expr {
    Expr::new(Types::BOOL, sp(), ExprKind::Lit(Lit::Bool(true)))
}
fn ex(k: ExprKind) -> Expr {
    Expr::new(Types::BOOL, sp(), k)
}
fn bx(e: Expr) -> Box<Expr> {
    Box::new(e)
}
fn blk(stmts: Vec<Stmt>, value: Option<Expr>) -> Block {
    Block { stmts, value: value.map(Box::new) }
}
fn st(kind: StmtKind) -> Stmt {
    Stmt { span: sp(), kind }
}
fn with_stmt(kind: StmtKind) -> Expr {
    ex(ExprKind::Block(blk(vec![st(kind)], None)))
}
type Wrap = (&'static str, fn(Expr) -> Expr);

fn wraps() -> Vec<Wrap> {
    vec![
        ("unary", |e| ex(ExprKind::Unary(UnOp::Not, bx(e)))),
        ("binary_lhs", |e| {
            ex(ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Wrap, lhs: bx(e), rhs: bx(lit()) })
        }),
        ("binary_rhs", |e| {
            ex(ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Wrap, lhs: bx(lit()), rhs: bx(e) })
        }),
        ("cmp_rhs", |e| ex(ExprKind::Cmp { op: CmpOp::Eq, lhs: bx(lit()), rhs: bx(e) })),
        ("logic_lhs", |e| ex(ExprKind::Logic { op: LogicOp::And, lhs: bx(e), rhs: bx(lit()) })),
        ("logic_rhs", |e| ex(ExprKind::Logic { op: LogicOp::And, lhs: bx(lit()), rhs: bx(e) })),
        ("cast", |e| ex(ExprKind::Cast(bx(e)))),
        ("call_arg2", |e| {
            ex(ExprKind::Call {
                fn_: FnId(0),
                args: vec![Arg { mode: Mode::Borrow, expr: lit() }, Arg { mode: Mode::Borrow, expr: e }],
            })
        }),
        ("prim_arg", |e| {
            ex(ExprKind::Prim { prim: crate::prim::Prim::Len, args: vec![Arg { mode: Mode::Borrow, expr: e }] })
        }),
        ("field", |e| ex(ExprKind::Field { base: bx(e), index: 0 })),
        ("index_base", |e| ex(ExprKind::Index { base: bx(e), index: bx(lit()), bounds: Bounds::Checked })),
        ("index_index", |e| ex(ExprKind::Index { base: bx(lit()), index: bx(e), bounds: Bounds::Checked })),
        ("spanof", |e| ex(ExprKind::SpanOf(bx(e)))),
        ("struct_last", |e| ex(ExprKind::Struct { ty: TypeId(0), fields: vec![(0, lit()), (1, e)] })),
        ("variant_last", |e| ex(ExprKind::Variant { ty: TypeId(0), tag: 0, fields: vec![lit(), e] })),
        ("array_last", |e| ex(ExprKind::Array(vec![lit(), e]))),
        ("repeat", |e| ex(ExprKind::Repeat { elem: bx(e), n: 2 })),
        ("tuple_last", |e| ex(ExprKind::Tuple(vec![lit(), e]))),
        ("tag", |e| ex(ExprKind::Tag(bx(e)))),
        ("payload", |e| ex(ExprKind::Payload { base: bx(e), tag: 0, index: 0 })),
        ("if_cond", |e| {
            ex(ExprKind::IfExpr { cond: bx(e), then: blk(vec![], Some(lit())), else_: blk(vec![], Some(lit())) })
        }),
        ("if_then", |e| {
            ex(ExprKind::IfExpr { cond: bx(lit()), then: blk(vec![], Some(e)), else_: blk(vec![], Some(lit())) })
        }),
        ("if_else", |e| {
            ex(ExprKind::IfExpr { cond: bx(lit()), then: blk(vec![], Some(lit())), else_: blk(vec![], Some(e)) })
        }),
        ("switch_scrut", |e| {
            ex(ExprKind::Switch { scrutinee: bx(e), arms: vec![(0, blk(vec![], Some(lit())))], default: None })
        }),
        ("switch_arm_last", |e| {
            ex(ExprKind::Switch {
                scrutinee: bx(lit()),
                arms: vec![(0, blk(vec![], Some(lit()))), (1, blk(vec![], Some(e)))],
                default: None,
            })
        }),
        ("switch_default", |e| {
            ex(ExprKind::Switch {
                scrutinee: bx(lit()),
                arms: vec![(0, blk(vec![], Some(lit())))],
                default: Some(blk(vec![], Some(e))),
            })
        }),
        ("block_value", |e| ex(ExprKind::Block(blk(vec![], Some(e))))),
        ("block_stmt_last", |e| {
            ex(ExprKind::Block(blk(vec![st(StmtKind::Expr(lit())), st(StmtKind::Expr(e))], Some(lit()))))
        }),
        ("panic_shown", |e| ex(ExprKind::Panic { msg: MsgId(0), origin: PanicOrigin::Assert, shown: vec![lit(), e] })),
        ("stmt_let", |e| with_stmt(StmtKind::Let(LocalId(0), e))),
        ("stmt_assign_value", |e| with_stmt(StmtKind::Assign(Place::Local(LocalId(0)), e))),
        ("stmt_assign_index", |e| {
            with_stmt(StmtKind::Assign(
                Place::Index(Box::new(Place::Local(LocalId(0))), bx(e), sp(), Bounds::Checked),
                lit(),
            ))
        }),
        ("stmt_expr", |e| with_stmt(StmtKind::Expr(e))),
        ("stmt_if_cond", |e| with_stmt(StmtKind::If(e, blk(vec![], None), blk(vec![], None)))),
        ("stmt_if_then", |e| with_stmt(StmtKind::If(lit(), blk(vec![], Some(e)), blk(vec![], None)))),
        ("stmt_if_else", |e| with_stmt(StmtKind::If(lit(), blk(vec![], None), blk(vec![], Some(e))))),
        ("stmt_while_cond", |e| with_stmt(StmtKind::While(e, blk(vec![], None)))),
        ("stmt_while_body", |e| with_stmt(StmtKind::While(lit(), blk(vec![], Some(e))))),
        ("stmt_for_lo", |e| with_stmt(StmtKind::ForRange(LocalId(0), e, lit(), blk(vec![], None)))),
        ("stmt_for_hi", |e| with_stmt(StmtKind::ForRange(LocalId(0), lit(), e, blk(vec![], None)))),
        ("stmt_for_body", |e| with_stmt(StmtKind::ForRange(LocalId(0), lit(), lit(), blk(vec![], Some(e))))),
        ("stmt_return", |e| with_stmt(StmtKind::Return(Some(e)))),
    ]
}

/// Each position of a child, nested past the limit, is rejected (W8-02
/// U5b, the break side).
#[test]
fn every_position_of_a_child_is_counted() {
    on_large_stack(|| {
        let mut missed = Vec::new();
        for (name, w) in wraps() {
            let mut e = lit();
            for _ in 0..CORE_DEPTH_LIMIT {
                e = w(e);
            }
            let m = module(e, nots(0, sp()));
            match verify(&m) {
                Err(err) if err.rule == Rule::V22 => {}
                other => missed.push((name, other.err().map(|e| e.to_string()))),
            }
        }
        assert!(missed.is_empty(), "not counted: {missed:?}");
    })
}

#[test]
fn a_deep_place_is_counted() {
    on_large_stack(|| {
        for kind in ["field", "index_base"] {
            let mut p = Place::Local(LocalId(0));
            for _ in 0..CORE_DEPTH_LIMIT {
                p = match kind {
                    "field" => Place::Field(Box::new(p), 0),
                    _ => Place::Index(Box::new(p), bx(lit()), sp(), Bounds::Checked),
                };
            }
            let m = module(with_stmt(StmtKind::Assign(p, lit())), nots(0, sp()));
            let r = verify(&m);
            assert!(matches!(&r, Err(e) if e.rule == Rule::V22), "{kind}: {r:?}");
        }
    })
}
