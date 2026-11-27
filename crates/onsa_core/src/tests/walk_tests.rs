//! The children of each form of Core in evaluation order, with how each is
//! evaluated, its scope and its role (W8-02 U1, `walk.rs`): an assignment
//! gives its value before its place (§3.5), the right operand of `&&`/`||`
//! is conditional, the condition and the body of a `while` are of a loop, a
//! block expression is inline and always evaluated, and the values a panic
//! shows are observed. Each child is named by the integer it holds.

use onsa_diag::{FileId, Span};

use crate::ir::*;
use crate::prim::Prim;
use crate::walk::{
    Child, Part, Role, block_children, expr_children, has_return, place_children, stmt_children, walk_block, walk_stmt,
    written_places,
};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

/// The integer `n`, its name in the lists.
fn n(n: i128) -> Expr {
    Expr::new(Types::U32, sp(), ExprKind::Lit(Lit::Int(n)))
}

fn e(kind: ExprKind) -> Expr {
    Expr::new(Types::U32, sp(), kind)
}

fn bx(x: Expr) -> Box<Expr> {
    Box::new(x)
}

/// A block of no statement and the value `v`.
fn blk(v: i128) -> Block {
    Block { stmts: Vec::new(), value: Some(bx(n(v))) }
}

fn st(kind: StmtKind) -> Stmt {
    Stmt { span: sp(), kind }
}

fn arg(mode: Mode, x: Expr) -> Arg {
    Arg { mode, expr: x }
}

/// The name of an expression: its integer, or `*` for another form.
fn name(x: &Expr) -> String {
    match x.kind {
        ExprKind::Lit(Lit::Int(v)) => v.to_string(),
        _ => "*".into(),
    }
}

fn place_name(p: &Place) -> String {
    match p {
        Place::Local(l) => format!("l{}", l.0),
        Place::Field(_, i) => format!("f{i}"),
        Place::Index(_, i, ..) => format!("[{}]", name(i)),
    }
}

fn shown(c: Child<'_>) -> String {
    match c {
        Child::Expr(x, eval, role) => format!("{} {eval:?} {role:?}", name(x)),
        Child::Block(b, scope, eval) => {
            format!("{{{}}} {scope:?} {eval:?}", name(b.value.as_deref().expect("a value")))
        }
        Child::Place(p, role) => format!("{} {role:?}", place_name(p)),
    }
}

fn of_stmt(kind: StmtKind) -> Vec<String> {
    let s = st(kind);
    let mut out = Vec::new();
    stmt_children(&s, &mut |c| out.push(shown(c)));
    out
}

fn of_expr(kind: ExprKind) -> Vec<String> {
    let x = e(kind);
    let mut out = Vec::new();
    expr_children(&x, &mut |c| out.push(shown(c)));
    out
}

/// `xs[i]` of the local 0, named `[i]`.
fn indexed(i: i128) -> Place {
    Place::Index(Box::new(Place::Local(LocalId(0))), bx(n(i)), sp(), Bounds::Checked)
}

#[test]
fn the_children_of_each_statement() {
    assert_eq!(of_stmt(StmtKind::Let(LocalId(0), n(1))), ["1 Always Dest"]);
    assert_eq!(
        of_stmt(StmtKind::Assign(indexed(2), n(1))),
        ["1 Always Dest", "[2] Write"],
        "the value, then the place"
    );
    assert_eq!(of_stmt(StmtKind::Expr(n(1))), ["1 Always Read"]);
    let if_ = StmtKind::If(n(1), blk(2), blk(3));
    assert_eq!(of_stmt(if_), ["1 Always Read", "{2} Opens Conditional", "{3} Opens Conditional"]);
    assert_eq!(of_stmt(StmtKind::While(n(1), blk(2))), ["1 Loop Read", "{2} Opens Loop"]);
    let for_ = StmtKind::ForRange(LocalId(0), n(1), n(2), blk(3));
    assert_eq!(of_stmt(for_), ["1 Always Read", "2 Always Read", "{3} Opens Loop"]);
    assert_eq!(of_stmt(StmtKind::Return(Some(n(1)))), ["1 Always Dest"]);
    for kind in [StmtKind::Return(None), StmtKind::Break, StmtKind::Continue] {
        assert!(of_stmt(kind).is_empty());
    }
}

#[test]
fn the_base_of_a_place_has_its_role_and_an_index_is_read() {
    let list = |p: &Place| {
        let mut out = Vec::new();
        place_children(p, crate::walk::PlaceRole::Write, &mut |c| out.push(shown(c)));
        out
    };
    assert!(list(&Place::Local(LocalId(0))).is_empty());
    assert_eq!(list(&Place::Field(Box::new(indexed(2)), 1)), ["[2] Write"]);
    let nested =
        Place::Index(Box::new(Place::Field(Box::new(Place::Local(LocalId(0))), 3)), bx(n(4)), sp(), Bounds::Known);
    assert_eq!(list(&nested), ["f3 Write", "4 Always Read"]);
}

#[test]
fn the_children_of_each_expression() {
    let none = Vec::<String>::new();
    for kind in [ExprKind::Lit(Lit::Unit), ExprKind::Local(LocalId(0)), ExprKind::Const(ConstId(0)), ExprKind::Zeroed] {
        assert_eq!(of_expr(kind), none);
    }
    let reads = [
        ExprKind::Unary(UnOp::Neg, bx(n(1))),
        ExprKind::Cast(bx(n(1))),
        ExprKind::SpanOf(bx(n(1))),
        ExprKind::Tag(bx(n(1))),
        ExprKind::Field { base: bx(n(1)), index: 0 },
        ExprKind::Payload { base: bx(n(1)), tag: 0, index: 0 },
    ];
    for kind in reads {
        assert_eq!(of_expr(kind), ["1 Always Read"]);
    }
    let two = ["1 Always Read", "2 Always Read"];
    assert_eq!(
        of_expr(ExprKind::Binary { op: BinOp::Add, overflow: Overflow::Checked, lhs: bx(n(1)), rhs: bx(n(2)) }),
        two
    );
    assert_eq!(of_expr(ExprKind::Cmp { op: CmpOp::Lt, lhs: bx(n(1)), rhs: bx(n(2)) }), two);
    assert_eq!(of_expr(ExprKind::Index { base: bx(n(1)), index: bx(n(2)), bounds: Bounds::Checked }), two);
    let logic = ExprKind::Logic { op: LogicOp::And, lhs: bx(n(1)), rhs: bx(n(2)) };
    assert_eq!(of_expr(logic), ["1 Always Read", "2 Conditional Read"]);
    let args = || vec![arg(Mode::Borrow, n(1)), arg(Mode::Inout, n(2)), arg(Mode::Move, n(3))];
    let roles = ["1 Always Read", "2 Always Inout", "3 Always Consume"];
    assert_eq!(of_expr(ExprKind::Call { fn_: FnId(0), args: args() }), roles);
    assert_eq!(of_expr(ExprKind::Prim { prim: Prim::Fill, args: args() }), roles);
    let dests = ["1 Always Dest", "2 Always Dest"];
    assert_eq!(of_expr(ExprKind::Struct { ty: TypeId(0), fields: vec![n(1), n(2)] }), dests);
    assert_eq!(of_expr(ExprKind::Variant { ty: TypeId(0), tag: 0, fields: vec![n(1), n(2)] }), dests);
    assert_eq!(of_expr(ExprKind::Array(vec![n(1), n(2)])), dests);
    assert_eq!(of_expr(ExprKind::Tuple(vec![n(1), n(2)])), dests);
    assert_eq!(of_expr(ExprKind::Repeat { elem: bx(n(1)), n: 4 }), ["1 Always Dest"]);
    let if_ = ExprKind::IfExpr { cond: bx(n(1)), then: blk(2), else_: blk(3) };
    assert_eq!(of_expr(if_), ["1 Always Read", "{2} Opens Conditional", "{3} Opens Conditional"]);
    let switch = ExprKind::Switch { scrutinee: bx(n(1)), arms: vec![(5, blk(2)), (0, blk(3))], default: Some(blk(4)) };
    let arms = ["1 Always Read", "{2} Opens Conditional", "{3} Opens Conditional", "{4} Opens Conditional"];
    assert_eq!(of_expr(switch), arms, "the arms in their order, then the default");
    let no_default = ExprKind::Switch { scrutinee: bx(n(1)), arms: vec![(0, blk(2))], default: None };
    assert_eq!(of_expr(no_default), ["1 Always Read", "{2} Opens Conditional"]);
    assert_eq!(of_expr(ExprKind::Block(blk(1))), ["{1} Inline Always"]);
    let panic = ExprKind::Panic { msg: MsgId(0), origin: PanicOrigin::Assert, shown: vec![n(1), n(2)] };
    assert_eq!(of_expr(panic), ["1 Observed Read", "2 Observed Read"]);
}

/// The parts of a block: its statements, then its value, which has the role
/// of the expression the block is a part of.
#[test]
fn a_block_gives_its_statements_then_its_value_of_the_role_given() {
    let list = |b: &Block, role| {
        let mut out = Vec::new();
        block_children(b, role, &mut |p| {
            out.push(match p {
                Part::Stmt(s) => format!("{:?}", s.kind),
                Part::Value(v, role) => format!("{} {role:?}", name(v)),
            })
        });
        out
    };
    for role in [Role::Read, Role::Consume, Role::Dest, Role::Inout] {
        let b = Block { stmts: vec![st(StmtKind::Break), st(StmtKind::Continue)], value: Some(bx(n(1))) };
        assert_eq!(list(&b, role), ["Break".to_string(), "Continue".into(), format!("1 {role:?}")]);
    }
    assert_eq!(list(&Block { stmts: vec![st(StmtKind::Break)], value: None }, Role::Dest), ["Break"]);
}

#[test]
fn a_block_is_walked_statements_then_value() {
    let b = Block { stmts: vec![st(StmtKind::Expr(n(1))), st(StmtKind::Expr(n(2)))], value: Some(bx(n(3))) };
    let mut seen = Vec::new();
    walk_block(&b, &mut |x| seen.push(name(x)));
    assert_eq!(seen, ["1", "2", "3"]);
}

/// The walk of an assignment: its value, then the index of its place (§3.5).
#[test]
fn an_assignment_is_walked_value_first() {
    let s = st(StmtKind::Assign(indexed(2), e(ExprKind::Tuple(vec![n(1)]))));
    let mut seen = Vec::new();
    walk_stmt(&s, &mut |x| seen.push(name(x)));
    assert_eq!(seen, ["*", "1", "2"]);
}

/// The places an `inout` argument writes, and whether it is of the forms
/// that write places.
#[test]
fn the_places_an_inout_argument_writes() {
    let local = |l| e(ExprKind::Local(LocalId(l)));
    let field = |l| e(ExprKind::Field { base: bx(local(l)), index: 0 });
    let span = |x| e(ExprKind::SpanOf(bx(x)));
    let slice = |x| e(ExprKind::Prim { prim: Prim::Slice, args: vec![arg(Mode::Borrow, x), arg(Mode::Borrow, n(0))] });
    let places = |x: &Expr| {
        let mut out = Vec::new();
        let ok = written_places(x, &mut |p| out.push(p.as_place().map(|p| p.root().0)));
        (ok, out)
    };
    assert_eq!(places(&field(3)), (true, vec![Some(3)]));
    assert_eq!(places(&span(local(1))), (true, vec![Some(1)]));
    assert_eq!(places(&slice(span(local(2)))), (true, vec![Some(2)]));
    let planar = e(ExprKind::Array(vec![span(local(1)), slice(span(local(2)))]));
    assert_eq!(places(&planar), (true, vec![Some(1), Some(2)]));
    let out = e(ExprKind::Struct { ty: TypeId(0), fields: vec![planar.clone(), span(field(4))] });
    assert_eq!(places(&out), (true, vec![Some(1), Some(2), Some(4)]));
    assert!(!places(&n(1)).0);
    assert!(!places(&span(n(1))).0);
    assert!(!places(&slice(n(1))).0);
    assert!(!places(&e(ExprKind::Array(vec![span(local(1)), n(1)]))).0, "every element is of the forms");
    let mixed = e(ExprKind::Array(vec![local(1), n(1), local(2)]));
    assert_eq!(places(&mixed), (false, vec![Some(1), Some(2)]), "the places after one that is not are given too");
    let call = e(ExprKind::Call { fn_: FnId(0), args: vec![] });
    assert!(!places(&e(ExprKind::Field { base: bx(call), index: 0 })).0);
}

/// `has_return` sees a `return` in each part a list gives: a block of a
/// statement, a block expression, an arm, the index of an assigned place.
#[test]
fn has_return_sees_each_part() {
    let ret = || Block { stmts: vec![st(StmtKind::Return(None))], value: Some(bx(n(0))) };
    let body = |s: Stmt| FnDef {
        name: "f".into(),
        params: Vec::new(),
        ret: Types::UNIT,
        sret: false,
        rt: false,
        locals: vec![Local { name: "v".into(), ty: Types::U32 }],
        body: Some(Block { stmts: vec![s], value: None }),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    };
    assert!(!has_return(&body(st(StmtKind::While(n(1), blk(2))))));
    assert!(has_return(&body(st(StmtKind::While(n(1), ret())))));
    assert!(has_return(&body(st(StmtKind::Expr(e(ExprKind::Block(ret())))))));
    let arm = ExprKind::IfExpr { cond: bx(n(1)), then: blk(2), else_: ret() };
    assert!(has_return(&body(st(StmtKind::Let(LocalId(0), e(arm))))));
    let index = Place::Index(Box::new(Place::Local(LocalId(0))), bx(e(ExprKind::Block(ret()))), sp(), Bounds::Checked);
    assert!(has_return(&body(st(StmtKind::Assign(index, n(1))))));
    assert!(!has_return(&body(st(StmtKind::Assign(indexed(1), n(1))))));
}
