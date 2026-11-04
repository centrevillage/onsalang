//! The tails of a value (spec §5.2, §5.4, S-604): the expressions that give
//! its value through `if`, `match`, blocks and parentheses. The one walk of
//! them on the tree, for the rows of the heads of the bindings (§5.4) and
//! the checks of each tail of an owned one (W4-09). And what diverges (§7,
//! S-891), which only the names stage can decide (`panic` is a name):
//! [`Diverging`], the table it makes once and every later stage reads.

use onsa_diag::hash::HashSet;

use crate::ast::{Arg, Ast, Block, ExprId, ExprKind, Lit, Mode, StmtId, StmtKind, StrSeg};

/// What diverges in a body (§7): the table the walk of the names stage
/// fills, child before parent, and the later stages read (D-15).
///
/// `Ast::sub_exprs` and that walk go in one order (R-91), and the types stage
/// reads the children in it too. So in a body where the walk stopped with no
/// report (S-692), every child the types stage reads is recorded: it stops at
/// the same place. [`Ast::leaves_loop`] is read by the names stage and a
/// candidate of the types stage: a pure function of the tree, no second
/// decision.
#[derive(Debug, Default, Clone)]
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

    /// Record the expression `e`, after its children; `panic`: it is a call
    /// of `panic`, which the walk knows by the name.
    pub fn note_expr(&mut self, ast: &Ast, e: ExprId, panic: bool) {
        let diverges = panic
            || match &ast.expr(e).kind {
                ExprKind::Paren(x) => self.expr(*x),
                ExprKind::Block(b) => self.block(ast, b),
                ExprKind::If { then, else_: Some(other), .. } => self.expr(*then) && self.expr(*other),
                ExprKind::Match { arms, .. } => !arms.is_empty() && arms.iter().all(|a| self.expr(a.body)),
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
        let StmtKind::While { cond, body } = ast.stmt(s).kind else { return };
        // A parenthesis is the same as none (`fmt` takes it off, §18.2).
        let forever = matches!(ast.expr(ast.without_parens(cond)).kind, ExprKind::Lit(Lit::Bool(true)));
        if forever && !ast.leaves_loop(body) {
            self.loops.insert(s);
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

impl Ast {
    /// The tails of `e` (§5.2: the tail of a block, of each branch of an `if`
    /// and of each arm of a `match`), through parentheses, in source order.
    /// The depth of the walk is that of the nesting of `e` (§2.5).
    pub fn tails(&self, e: ExprId, diverging: &Diverging, out: &mut Vec<Tail>) {
        if diverging.expr(e) {
            return out.push(Tail::Exits);
        }
        let e = self.without_parens(e);
        match &self.expr(e).kind {
            ExprKind::If { then, else_: Some(other), .. } => {
                self.tails(*then, diverging, out);
                self.tails(*other, diverging, out);
            }
            ExprKind::If { else_: None, .. } => out.push(Tail::Unit(e)),
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.tails(arm.body, diverging, out);
                }
            }
            ExprKind::Block(b) => match b.tail {
                Some(t) => self.tails(t, diverging, out),
                None => out.push(Tail::Unit(e)),
            },
            _ => out.push(Tail::Value(e)),
        }
    }

    /// Whether `e`, in the body of a loop, holds a `break` of that loop (§7):
    /// not one in the body of a loop inside it (the head of such a loop is
    /// evaluated in this one, so a `break` there counts) or in an anonymous
    /// function. By the structure alone: one that is not reached counts.
    pub fn leaves_loop(&self, e: ExprId) -> bool {
        match &self.expr(e).kind {
            ExprKind::Closure { .. } => false,
            ExprKind::Block(b) => {
                b.stmts.iter().any(|&s| self.stmt_leaves_loop(s)) || b.tail.is_some_and(|t| self.leaves_loop(t))
            }
            _ => self.sub_exprs(e).into_iter().any(|x| self.leaves_loop(x)),
        }
    }

    fn stmt_leaves_loop(&self, s: StmtId) -> bool {
        match &self.stmt(s).kind {
            StmtKind::Break => true,
            StmtKind::Continue | StmtKind::Return(None) => false,
            StmtKind::While { cond: head, .. } | StmtKind::For { iter: head, .. } => self.leaves_loop(*head),
            StmtKind::Let { init: x, .. }
            | StmtKind::Var { init: x, .. }
            | StmtKind::Return(Some(x))
            | StmtKind::Assert(x)
            | StmtKind::Expr(x) => self.leaves_loop(*x),
            StmtKind::Assign { target, value } => self.leaves_loop(*target) || self.leaves_loop(*value),
        }
    }

    /// The text of the argument `arg` of `panic` (§9.2): a string literal
    /// with no interpolation, through parentheses; none for anything else.
    pub fn panic_message(&self, arg: &Arg) -> Option<String> {
        let ExprKind::Lit(Lit::Str(s)) = &self.expr(self.without_parens(arg.expr)).kind else { return None };
        let mut text = String::new();
        for seg in &s.segments {
            match seg {
                StrSeg::Text(t) => text.push_str(t),
                StrSeg::Interp(_) => return None,
            }
        }
        (arg.mode == Mode::Borrow && !s.pathless_hole).then_some(text)
    }
}
