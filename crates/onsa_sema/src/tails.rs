//! The tails of a value (spec §5.2, §5.4, S-604): the expressions that give
//! its value through `if`, `match`, blocks and parentheses. The one walk of
//! them on the tree, for the rows of the heads of the bindings (§5.4) and
//! the checks of each tail of an owned one (W4-09). And what diverges (§7,
//! S-891), which only the names stage can decide (`panic` is a name):
//! [`Diverging`], the table it makes once and every later stage reads.

use onsa_diag::hash::HashSet;
use onsa_syntax::ast::{Ast, BinOp, Block, ExprId, ExprKind, Lit, MatchArm, StmtId, StmtKind};
use serde::{Deserialize, Serialize};

/// What diverges in a body (§7): the table the walk of the names stage
/// fills, child before parent, and the later stages read (D-15).
///
/// `Ast::sub_exprs` and that walk go in one order (R-91), and the types stage
/// reads the children in it too. So in a body where the walk stopped with no
/// report (S-692), every child the types stage reads is recorded: it stops at
/// the same place. A candidate is read with the table of its form
/// ([`Diverging::patched`]): a pure function of that form, no second decision.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct Diverging {
    /// The expressions of a diverging form.
    exprs: HashSet<ExprId>,
    /// The `while` statements that diverge.
    loops: HashSet<StmtId>,
}

impl Diverging {
    /// Whether `e` has a diverging form: `panic(...)`, a block that ends in
    /// a diverging statement, an `if` (with an `else`) or a `match` (with an
    /// arm) all of whose branches do, and parentheses around one.
    pub fn expr(&self, e: ExprId) -> bool {
        self.exprs.contains(&e)
    }

    /// Whether the statement `s` diverges: `return`, `break`, `continue`, a
    /// diverging `while`, a diverging expression, and a `let` or `var` whose
    /// whole initializer is one.
    pub fn stmt(&self, ast: &Ast, s: StmtId) -> bool {
        match &ast.stmt(s).kind {
            StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue => true,
            StmtKind::While { .. } => self.forever(s),
            StmtKind::Let { init: e, .. } | StmtKind::Var { init: e, .. } | StmtKind::Expr(e) => self.expr(*e),
            StmtKind::Assign { .. } | StmtKind::For { .. } | StmtKind::Assert(_) => false,
        }
    }

    /// Whether the `while` statement `s` diverges: its condition is the
    /// literal `true` and no `break` leaves it.
    pub fn forever(&self, s: StmtId) -> bool {
        self.loops.contains(&s)
    }

    /// Whether the block `b` ends in a diverging form.
    pub fn block(&self, ast: &Ast, b: &Block) -> bool {
        match b.tail {
            Some(t) => self.expr(t),
            None => b.stmts.last().is_some_and(|&s| self.stmt(ast, s)),
        }
    }

    /// The part of the expression `e` that is always evaluated and diverges,
    /// so that `e` is never carried out (§7, S-291, S-889). Not a part: the
    /// right of `&&` and `||`, a guard (§3.5), the body of an anonymous
    /// function, a branch and the last expression of a block. The types stage
    /// asks before it checks `e`: the child would stop it at its open type
    /// (E0420).
    pub fn evaluated_part(&self, ast: &Ast, e: ExprId) -> Option<ExprId> {
        if self.exprs.is_empty() {
            return None;
        }
        match &ast.expr(e).kind {
            ExprKind::Binary { op: BinOp::And | BinOp::Or, lhs: x, .. }
            | ExprKind::Unary { expr: x, .. }
            | ExprKind::Cast { expr: x, .. }
            | ExprKind::Try(x)
            | ExprKind::Move(x)
            | ExprKind::At { expr: x, .. }
            | ExprKind::Field { base: x, .. }
            | ExprKind::TupleIndex { base: x, .. }
            | ExprKind::Repeat { elem: x, .. }
            | ExprKind::If { cond: x, .. }
            | ExprKind::Match { scrutinee: x, .. } => self.first(ast, [*x]),
            ExprKind::Binary { lhs: a, rhs: b, .. } | ExprKind::Index { base: a, index: b } => {
                self.first(ast, [*a, *b])
            }
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => self.first(ast, xs.iter().copied()),
            ExprKind::Struct { fields, .. } => self.first(ast, fields.iter().map(|(_, x)| *x)),
            ExprKind::Range(r) => self.first(ast, [r.lo, r.hi]),
            ExprKind::Call { callee, args, .. } => {
                // The callee of a value call, or the receiver of a method: no
                // `check_expr` reads the `Field` of a method.
                let receiver = match ast.expr(*callee).kind {
                    ExprKind::Field { base, .. } => Some(base),
                    _ => None,
                };
                self.first(ast, [*callee].into_iter().chain(receiver).chain(args.iter().map(|a| a.expr)))
            }
            _ => None,
        }
    }

    /// [`Diverging::evaluated_part`] of a statement's head (§7: E0503 at the
    /// statement). The initializer of a `let` is no part of it (S-268). The
    /// ends of a range go through here: `for` reads them with no `check_expr`
    /// of the range.
    pub fn stmt_part(&self, ast: &Ast, s: StmtId) -> Option<ExprId> {
        if self.exprs.is_empty() {
            return None;
        }
        match &ast.stmt(s).kind {
            StmtKind::For { iter, .. } if matches!(ast.expr(*iter).kind, ExprKind::Range(_)) => {
                self.evaluated_part(ast, *iter)
            }
            StmtKind::Assign { value: x, .. }
            | StmtKind::Return(Some(x))
            | StmtKind::Assert(x)
            | StmtKind::While { cond: x, .. }
            | StmtKind::For { iter: x, .. } => self.first(ast, [*x]),
            _ => None,
        }
    }

    /// The first of `parts` that diverges, through parentheses and `move`
    /// (`f(move ({ return 1 }))` is one of `f`'s).
    fn first(&self, ast: &Ast, parts: impl IntoIterator<Item = ExprId>) -> Option<ExprId> {
        parts.into_iter().find_map(|mut x| {
            while let ExprKind::Paren(inner) | ExprKind::Move(inner) = ast.expr(x).kind {
                x = inner;
            }
            self.expr(x).then_some(x)
        })
    }

    /// Record the expression `e`, after its children; `panic`: it is a call
    /// of `panic`, which the walk knows by the name.
    pub fn note_expr(&mut self, ast: &Ast, e: ExprId, panic: bool) {
        self.read_expr(ast, e, panic, None);
    }

    fn read_expr(&mut self, ast: &Ast, e: ExprId, panic: bool, patch: Option<&Patch>) {
        let diverges = panic
            || match &ast.expr(e).kind {
                ExprKind::Paren(x) => self.expr(*x),
                ExprKind::Block(b) => self.block(ast, Patch::block(patch, e, b)),
                ExprKind::If { then, else_: Some(other), .. } => self.expr(*then) && self.expr(*other),
                ExprKind::Match { arms, .. } => {
                    let arms = Patch::arms(patch, e, arms);
                    !arms.is_empty() && arms.iter().all(|a| self.expr(a.body))
                }
                _ => false,
            };
        if diverges {
            self.exprs.insert(e);
        }
    }

    /// Record the statement `s`, a `while`. The search for a `break` stops
    /// at the loops inside, so an expression is searched for its innermost
    /// loop alone: O(n) over a body.
    pub fn note_while(&mut self, ast: &Ast, s: StmtId) {
        self.read_while(ast, s, None);
    }

    fn read_while(&mut self, ast: &Ast, s: StmtId, patch: Option<&Patch>) {
        let StmtKind::While { cond, body } = ast.stmt(s).kind else { return };
        // A parenthesis is the same as none (`fmt` takes it off, §18.2).
        let forever = matches!(ast.expr(ast.without_parens(cond)).kind, ExprKind::Lit(Lit::Bool(true)));
        if forever && !leaves_loop(ast, body, patch) {
            self.loops.insert(s);
        }
    }

    /// The table of the body `root` with `patch` in it, made as the walk of
    /// the names stage makes it, child before parent, with the same reading
    /// of each node. A `panic` stays as it is: no form changes one, and only
    /// that walk knows it by the name. What a form takes away is read too and
    /// nothing asks for it. Linear in the body, whose reads are few.
    pub fn patched(&self, ast: &Ast, root: ExprId, patch: &Patch) -> Diverging {
        let mut table = self.clone();
        table.read_again(ast, root, patch);
        table
    }

    fn read_again(&mut self, ast: &Ast, e: ExprId, patch: &Patch) {
        for x in ast.sub_exprs(e) {
            self.read_again(ast, x, patch);
        }
        let kind = &ast.expr(e).kind;
        if let ExprKind::Block(b) = kind {
            for &s in &b.stmts {
                self.loops.remove(&s);
                self.read_while(ast, s, Some(patch));
            }
        }
        if matches!(kind, ExprKind::Paren(_) | ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::Match { .. }) {
            self.exprs.remove(&e);
            self.read_expr(ast, e, false, Some(patch));
        }
    }
}

/// A candidate as a form of the body (§18.1): of an E0503 (§7), of the `return`
/// of an E0401 and of the join of an E0418 (§6.1). One node read as another,
/// so a body is read with it applied and no copy of the tree.
#[derive(Debug, Clone)]
pub enum Patch {
    /// The block reads as this one: as the parser reads what is left, the
    /// last item an expression is its `tail`.
    Block(ExprId, Block),
    /// The `match` has these arms, in this order.
    Arms(ExprId, Vec<MatchArm>),
    /// The block reads as this one, which has lost its last expression, and
    /// that expression is the value of the `return` statement: `return`, then
    /// `x` on the next line, read as `return x` (§7, S-886).
    Joined(ExprId, Block, StmtId, ExprId),
    /// The block reads as this one, which has lost the statement before its
    /// last expression `-x`, and that statement is the left operand of it:
    /// `a`, then `-x` on the next line, read as `a - x` (§6.1, §2.5).
    Operand(ExprId, Block, ExprId, ExprId),
}

impl Patch {
    /// The block `b` of the node `e` in the form `patch` has of it.
    pub fn block<'x>(patch: Option<&'x Patch>, e: ExprId, b: &'x Block) -> &'x Block {
        match patch {
            Some(Patch::Block(id, p) | Patch::Joined(id, p, ..) | Patch::Operand(id, p, ..)) if *id == e => p,
            _ => b,
        }
    }

    /// The arms `arms` of the `match` `e` in the form `patch` has of them.
    pub fn arms<'x>(patch: Option<&'x Patch>, e: ExprId, arms: &'x [MatchArm]) -> &'x [MatchArm] {
        match patch {
            Some(Patch::Arms(id, patched)) if *id == e => patched,
            _ => arms,
        }
    }

    /// The value `patch` gives the `return` statement `s`, which has none.
    pub fn joined(patch: Option<&Patch>, s: StmtId) -> Option<ExprId> {
        match patch {
            Some(Patch::Joined(_, _, at, x)) if *at == s => Some(*x),
            _ => None,
        }
    }

    /// The left operand `patch` gives the `-x` node `e`, read as `a - x`.
    pub fn left(patch: Option<&Patch>, e: ExprId) -> Option<ExprId> {
        match patch {
            Some(Patch::Operand(_, _, at, a)) if *at == e => Some(*a),
            _ => None,
        }
    }
}

/// A tail of a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tail {
    /// An expression that is no `if`, `match`, block or parenthesis.
    Value(ExprId),
    /// A diverging form ([`Diverging::expr`]): it gives no value.
    Exits,
    /// The `()` of a block with no tail that does not diverge, or of an
    /// `if` with no `else` (the node of the block or the `if`).
    Unit(ExprId),
}

/// The tails of `e` (§5.2: the tail of a block, of each branch of an `if`
/// and of each arm of a `match`), through parentheses, in source order.
/// The depth of the walk is that of the nesting of `e` (§2.5).
pub fn tails(ast: &Ast, e: ExprId, diverging: &Diverging, out: &mut Vec<Tail>) {
    if diverging.expr(e) {
        return out.push(Tail::Exits);
    }
    let e = ast.without_parens(e);
    match &ast.expr(e).kind {
        ExprKind::If { then, else_: Some(other), .. } => {
            tails(ast, *then, diverging, out);
            tails(ast, *other, diverging, out);
        }
        ExprKind::If { else_: None, .. } => out.push(Tail::Unit(e)),
        ExprKind::Match { arms, .. } => {
            for arm in arms {
                tails(ast, arm.body, diverging, out);
            }
        }
        ExprKind::Block(b) => match b.tail {
            Some(t) => tails(ast, t, diverging, out),
            None => out.push(Tail::Unit(e)),
        },
        _ => out.push(Tail::Value(e)),
    }
}

/// Whether `e`, in the body of a loop, holds a `break` of that loop (§7):
/// not one in the body of a loop inside it (the head of such a loop is
/// evaluated in this one, so a `break` there counts) or in an anonymous
/// function. By the structure alone, of the form `patch` has of it: one
/// that is not reached counts.
pub fn leaves_loop(ast: &Ast, e: ExprId, patch: Option<&Patch>) -> bool {
    let leaves = |x: ExprId| leaves_loop(ast, x, patch);
    match &ast.expr(e).kind {
        ExprKind::Closure { .. } => false,
        ExprKind::Block(b) => {
            let b = Patch::block(patch, e, b);
            b.stmts.iter().any(|&s| stmt_leaves_loop(ast, s, patch)) || b.tail.is_some_and(leaves)
        }
        ExprKind::Match { scrutinee, arms, .. } => {
            let mut arms = Patch::arms(patch, e, arms).iter();
            leaves(*scrutinee) || arms.any(|a| a.guard.is_some_and(leaves) || leaves(a.body))
        }
        // The left operand a form gives `-x` is out of the block (`a - x`).
        _ => ast.sub_exprs(e).into_iter().chain(Patch::left(patch, e)).any(leaves),
    }
}

/// [`leaves_loop`] of a statement.
fn stmt_leaves_loop(ast: &Ast, s: StmtId, patch: Option<&Patch>) -> bool {
    let leaves = |x: ExprId| leaves_loop(ast, x, patch);
    match &ast.stmt(s).kind {
        StmtKind::Break => true,
        StmtKind::Continue => false,
        StmtKind::Return(None) => Patch::joined(patch, s).is_some_and(leaves),
        StmtKind::While { cond: head, .. } | StmtKind::For { iter: head, .. } => leaves(*head),
        StmtKind::Let { init: x, .. }
        | StmtKind::Var { init: x, .. }
        | StmtKind::Return(Some(x))
        | StmtKind::Assert(x)
        | StmtKind::Expr(x) => leaves(*x),
        StmtKind::Assign { target, value } => leaves(*target) || leaves(*value),
    }
}
