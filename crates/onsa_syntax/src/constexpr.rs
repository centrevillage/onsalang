//! The forms of a constant expression on the AST (§4.5): a chain of names,
//! read the one way by the names stage, the reader of the constants and the
//! order of the declarations (R-426), and the grammar of the nodes, whose
//! operators the syntax stage's reading of a type argument shares (Y1).

use onsa_diag::Span;

use crate::ast::{Ast, BinOp, ExprId, ExprKind, Ident, Lit, Path, UnOp};

/// The names of a chain (`a.b.c`, `Rg::[F32, 4].CAP`) from its head, each
/// with its node, and its type arguments, each with the index of the name
/// before it ([`Ast::chain`]).
#[derive(Debug, Clone)]
pub struct NameChain<'a> {
    pub names: Vec<(ExprId, &'a Ident)>,
    pub lists: Vec<(usize, ExprId)>,
}

impl NameChain<'_> {
    /// The path of its first `n` names, without the type arguments between
    /// them ([`path_of`]).
    pub fn path(&self, n: usize) -> Path {
        path_of(&self.names[..n].iter().map(|&(_, name)| name).collect::<Vec<_>>())
    }
}

/// The span from the first name of `names` to its last.
pub fn span_of(names: &[&Ident]) -> Span {
    let (first, last) = (names[0].span, names[names.len() - 1].span);
    Span::new(first.file, first.start, last.end)
}

/// The path of the names `names`, from the first to the last ([`span_of`]).
pub fn path_of(names: &[&Ident]) -> Path {
    Path { segments: names.iter().map(|&s| s.clone()).collect(), span: span_of(names) }
}

impl BinOp {
    /// Whether it is an operator of a constant expression: `+ - * / %`
    /// (§4.5). The one table of them, for the syntax stage and `onsa_sema`.
    pub fn in_constant(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem)
    }
}

/// The form of a node of a constant expression (§4.5; [`Ast::const_form`]).
#[derive(Debug, Clone)]
pub enum ConstForm<'a> {
    /// A chain of names ([`Ast::chain`]).
    Chain(NameChain<'a>),
    Paren(ExprId),
    /// A prefix `-`.
    Neg(ExprId),
    /// An operator of [`BinOp::in_constant`], with its operands.
    Arith(ExprId, ExprId),
    /// A literal of any type: one not an integer is of the grammar, and an
    /// error of its type (E0401).
    Lit(&'a Lit),
    /// What a syntax error left unread.
    Error,
    /// Any other form: no constant expression.
    Outside,
}

impl Ast {
    /// The chain of names `e` ends (`a.b.c` is `Field(Field(Path(a), b), c)`),
    /// from its head, with the node of each, and its type arguments
    /// (`Buf::[F32].zeroed`, §4.5), each with the index of the name before
    /// it; none when its head is no name (`f().x`, `(K).x`).
    pub fn chain(&self, e: ExprId) -> Option<NameChain<'_>> {
        let (mut names, mut lists) = (Vec::new(), Vec::new());
        let mut cur = e;
        loop {
            match &self.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    names.push((cur, name));
                    cur = *base;
                }
                ExprKind::TypeArgs { base, .. } => {
                    lists.push((names.len(), cur));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    names.push((cur, &p.segments[0]));
                    names.reverse();
                    let n = names.len();
                    let lists = lists.into_iter().rev().map(|(after, x)| (n - after - 1, x)).collect();
                    return Some(NameChain { names, lists });
                }
                _ => return None,
            }
        }
    }

    /// The form of the node `e` of a constant expression (§4.5): its
    /// operands are not looked at. Each kind of node is named, so a new one
    /// is put in or out of the grammar here (the names stage, the reader
    /// and the order of the declarations read by it, S-989).
    pub fn const_form(&self, e: ExprId) -> ConstForm<'_> {
        if let Some(chain) = self.chain(e) {
            return ConstForm::Chain(chain);
        }
        use {ConstForm::Outside, ExprKind as K};
        match &self.expr(e).kind {
            K::Paren(x) => ConstForm::Paren(*x),
            K::Unary { op: UnOp::Neg, expr } => ConstForm::Neg(*expr),
            K::Binary { op, lhs, rhs, .. } if op.in_constant() => ConstForm::Arith(*lhs, *rhs),
            K::Lit(lit) => ConstForm::Lit(lit),
            K::Error => ConstForm::Error,
            // A chain whose head is no name (`f().x`, `(K).x`), the other
            // operators, and every other form.
            K::Path(_) | K::Field { .. } | K::TypeArgs { .. } | K::TupleIndex { .. } | K::Unary { .. } => Outside,
            K::Binary { .. } | K::Cast { .. } | K::Call { .. } | K::Index { .. } | K::Try(_) | K::Move(_) => Outside,
            K::Tuple(_) | K::Array(_) | K::Repeat { .. } | K::Struct { .. } | K::Block(_) | K::If { .. } => Outside,
            K::Match { .. } | K::Closure { .. } | K::Handle { .. } | K::Unsafe(_) | K::Par { .. } => Outside,
            K::Range(_) | K::At { .. } | K::Feedback(_) | K::Hole => Outside,
        }
    }
}
