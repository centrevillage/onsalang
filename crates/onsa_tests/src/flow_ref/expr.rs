//! The expressions of the evaluator (§11.2): names, literals, parentheses, the operators
//! of §3.4 with the short circuit of `&&` and `||` (§3.5), `as` (§3.3), `at` (§11.3: it
//! changes neither the value nor the stage), `if` (§11.5: only the branch taken) and the
//! blocks that hold them. The operands are evaluated from the left (§3.5), and a panic is
//! a [`Stop`] at the span of the expression it comes from. Each value is checked against
//! the type of the table (the memo's way (1)): a disagreement is an internal error, not a guess.
//! The aggregates are in [`super::aggregate`], the patterns in [`super::pattern`]. The other forms (calls, the
//! forms of a flow) are [`Fault::Unavailable`] until the units that have them.

use std::collections::HashMap;

use onsa_diag::Span;
use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{ConstValue, DefId, LocalId, Target, Ty};
use onsa_syntax::ast::{BinOp, Block, CallKind, ExprId, ExprKind, Lit, StmtKind, UnOp};
use onsa_syntax::{FloatWidth, float_value};

use super::scalar::{Bin, Fault, Un, binary, cast, unary};
use super::sema_view::{Body, View};
use super::value::{Scalar, Value};

/// A fault and where it came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stop {
    pub fault: Fault,
    pub at: Span,
}

pub type Eval = Result<Value, Stop>;

/// A chain of constants that read constants is followed this far: a limit of the evaluator (the spec has none) on the
/// work and the length of a chain. It is not what keeps the stack: a chain times the depth of each initializer (§2.5
/// allows 256) would use more than the stack, so [`Limits::reserve`] is read at each evaluation, whatever the chain.
const CHAIN: u32 = 256;

/// What the evaluator does not go past, and stops with `Unavailable` at (the spec has none of them): the stack kept
/// back (`onsa_diag::stack::remaining`, read at each `eval`; a thread that is not a command thread has no guard) and
/// the places a value that `[e; N]` makes or a row of a constant gives holds ([`Value::places`]). A test gives smaller
/// ones, so that it does not have to build or to nest a lot.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub reserve: usize,
    pub most: usize,
}

/// 4 MiB of the 64 MiB of a command thread stay: the frames between two `eval`s (a pattern 256 levels deep) are well
/// within it. 2^20 places are 40 MB or so.
pub const LIMITS: Limits = Limits { reserve: 4 << 20, most: 1 << 20 };

/// The evaluation of one body: the values its locals have so far.
pub struct Frame<'a> {
    pub body: Body<'a>,
    pub locals: HashMap<LocalId, Value>,
    pub limits: Limits,
    chain: u32,
}

/// `+%` is the evaluator's `WAdd` and so on; `&&` and `||` are not operators of the evaluator.
fn bin(op: BinOp) -> Result<Bin, Fault> {
    Ok(match op {
        BinOp::Add => Bin::Add,
        BinOp::Sub => Bin::Sub,
        BinOp::Mul => Bin::Mul,
        BinOp::Div => Bin::Div,
        BinOp::Rem => Bin::Rem,
        BinOp::WrapAdd => Bin::WAdd,
        BinOp::WrapSub => Bin::WSub,
        BinOp::WrapMul => Bin::WMul,
        BinOp::SatAdd => Bin::SAdd,
        BinOp::SatSub => Bin::SSub,
        BinOp::SatMul => Bin::SMul,
        BinOp::Eq => Bin::Eq,
        BinOp::Ne => Bin::Ne,
        BinOp::Lt => Bin::Lt,
        BinOp::Le => Bin::Le,
        BinOp::Gt => Bin::Gt,
        BinOp::Ge => Bin::Ge,
        BinOp::BitAnd => Bin::And,
        BinOp::BitOr => Bin::Or,
        BinOp::BitXor => Bin::Xor,
        BinOp::Shl => Bin::Shl,
        BinOp::Shr => Bin::Shr,
        BinOp::And | BinOp::Or => return Err(Fault::Internal("a short circuit is not an operator")),
    })
}

impl<'a> Frame<'a> {
    pub fn new(body: Body<'a>) -> Frame<'a> {
        Frame { body, locals: HashMap::new(), limits: LIMITS, chain: 0 }
    }

    /// The value of `e`, which has the type the table gives it. Call it on a large stack (`mod.rs`): it recurses.
    pub fn eval(&mut self, e: ExprId) -> Eval {
        let at = self.body.ast.expr(e).span;
        if onsa_diag::stack::remaining().is_some_and(|left| left < self.limits.reserve) {
            return Err(Stop { fault: Fault::Unavailable("the stack is nearly used up"), at });
        }
        let v = self.form(e, at)?;
        match self.body.ty(e).and_then(|ty| v.agrees(ty, self.body.view)) {
            Ok(true) => Ok(v),
            Ok(false) => Err(Stop { fault: Fault::Internal("the value is not of the type of the table"), at }),
            Err(fault) => Err(Stop { fault, at }),
        }
    }

    /// The form of `e`: each one with work to do is its own function, so that the frame of a deep recursion is small.
    fn form(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        Ok(match &self.body.ast.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::At { expr: x, .. } => return self.eval(*x),
            ExprKind::Lit(l) => self.literal(e, l, false).map_err(here)?,
            ExprKind::Path(_) => return self.name(e, at),
            ExprKind::Field { .. }
            | ExprKind::TupleIndex { .. }
            | ExprKind::Index { .. }
            | ExprKind::Tuple(_)
            | ExprKind::Array(_)
            | ExprKind::Repeat { .. }
            | ExprKind::Struct { .. } => return self.aggregate(e, at),
            ExprKind::Call { args, kind: CallKind::Plain, .. } => return self.call(e, args, at),
            ExprKind::Match { tilde: None, .. } => return self.select(e, at),
            ExprKind::Unary { op: UnOp::Neg, .. } if self.body.ast.negated_literal(e).is_some() => {
                return self.negated(e, at);
            }
            ExprKind::Unary { op, expr: x } => return self.unary(*op, *x, at),
            ExprKind::Binary { op: op @ (BinOp::And | BinOp::Or), lhs, rhs, .. } => {
                return self.short(*op, *lhs, *rhs, at);
            }
            ExprKind::Binary { op, lhs, rhs, .. } => return self.binary(*op, *lhs, *rhs, at),
            ExprKind::Cast { expr: x, .. } => return self.cast(e, *x, at),
            ExprKind::If { cond, then, else_, tilde: None } => return self.branch(*cond, *then, *else_, at),
            ExprKind::Block(b) => return self.block(b, at),
            _ => return Err(here(Fault::Unavailable("a form of a later unit"))),
        })
    }

    pub(super) fn truth(&mut self, e: ExprId, at: Span) -> Result<bool, Stop> {
        match self.eval(e)? {
            Value::Bool(b) => Ok(b),
            _ => Err(Stop { fault: Fault::Internal("a condition that is not a `Bool`"), at }),
        }
    }

    /// §4.7: the `-` of `-128` is a part of the literal, which is out of the range of an `I8` without it.
    fn negated(&mut self, e: ExprId, at: Span) -> Eval {
        let lit = self.body.ast.negated_literal(e).unwrap_or(e);
        let ExprKind::Lit(l) = &self.body.ast.expr(lit).kind else {
            return Err(Stop { fault: Fault::Internal("a negated literal"), at });
        };
        self.literal(lit, l, true).map_err(|fault| Stop { fault, at })
    }

    #[inline(never)]
    fn unary(&mut self, op: UnOp, x: ExprId, at: Span) -> Eval {
        let v = self.eval(x)?;
        unary(if matches!(op, UnOp::Neg) { Un::Neg } else { Un::Not }, &v).map_err(|fault| Stop { fault, at })
    }

    /// The right operand only when the left does not decide (§3.5).
    fn short(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, at: Span) -> Eval {
        let a = self.truth(lhs, at)?;
        if a == (op == BinOp::Or) { Ok(Value::Bool(a)) } else { self.eval(rhs) }
    }

    #[inline(never)]
    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let (a, b) = (self.eval(lhs)?, self.eval(rhs)?);
        binary(bin(op).map_err(here)?, &a, &b).map_err(here)
    }

    #[inline(never)]
    fn cast(&mut self, e: ExprId, x: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let to = Scalar::of(self.body.ty(e).map_err(here)?);
        let to = to.ok_or(here(Fault::Internal("`as` to a type that is not a scalar")))?;
        cast(to, &self.eval(x)?).map_err(here)
    }

    fn branch(&mut self, cond: ExprId, then: ExprId, else_: Option<ExprId>, at: Span) -> Eval {
        let taken = if self.truth(cond, at)? { Some(then) } else { else_ };
        taken.map_or(Ok(Value::Unit), |branch| self.eval(branch))
    }

    #[inline(never)]
    fn block(&mut self, b: &Block, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        let ast = self.body.ast;
        for s in &b.stmts {
            let StmtKind::Let { pat, init, .. } = &ast.stmt(*s).kind else {
                return Err(here(Fault::Unavailable("a statement")));
            };
            let v = self.eval(*init)?;
            self.destructure(*pat, &v, self.body.ty(*init).map_err(here)?)?;
        }
        b.tail.map_or(Ok(Value::Unit), |tail| self.eval(tail))
    }

    /// A literal of the type of the table (`e` is the literal), negated when the `-` before it is a part of it.
    fn literal(&self, e: ExprId, lit: &Lit, neg: bool) -> Result<Value, Fault> {
        let sign = if neg { -1 } else { 1 };
        Ok(match (lit, self.body.ty(e)?) {
            (Lit::Int { value, .. }, Ty::Int(k)) => Value::int(*k, sign * i128::from(*value)),
            (Lit::Float { text }, Ty::Float(k)) => {
                let width = if *k == FloatKind::F32 { FloatWidth::F32 } else { FloatWidth::F64 };
                let x = sign as f64 * float_value(text, width).map_err(|_| Fault::Internal("a float out of range"))?;
                Value::float(*k, x)
            }
            (Lit::Bool(b), Ty::Bool) => Value::Bool(*b),
            (Lit::Char(c), Ty::Char) => Value::Char(*c),
            (Lit::Str(_), _) => return Err(Fault::Unavailable("a string")),
            _ => return Err(Fault::Internal("a literal that is not of the type of the table")),
        })
    }

    /// A name: a local (an input or a `let`), or a constant (an associated one, `F32.PI`, included).
    pub(super) fn name(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        match self.body.target(e).map_err(here)? {
            Target::Local(l) => self.locals.get(l).cloned().ok_or(here(Fault::Internal("a local with no value"))),
            Target::Const { def, .. } => self.constant(e, *def, at),
            Target::Variant { index, .. } => Ok(Value::Enum { tag: *index, fields: vec![] }),
            _ => Err(here(Fault::Unavailable("a name of a later unit"))),
        }
    }

    /// The value the checker worked out, else the initializer evaluated here (`F32.INFINITY` is `1.0 / 0.0`).
    fn constant(&mut self, e: ExprId, def: DefId, at: Span) -> Eval {
        let ty = self.body.ty(e).map_err(|fault| Stop { fault, at })?;
        self.const_def(def, ty, at)
    }

    /// The constant `def` of the type `ty`: the row of the table when it reads as the type (an aggregate of a form
    /// it cannot read falls to the initializer, which is evaluated here).
    pub(super) fn const_def(&mut self, def: DefId, ty: &Ty, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        if let Some(c) = self.body.view.const_value(def).filter(|c| places(c) <= self.limits.most) {
            match from_const(self.body.view, c, ty) {
                Err(Fault::Unavailable(_)) => {}
                v => return v.map_err(here),
            }
        }
        if self.chain >= CHAIN {
            return Err(here(Fault::Unavailable("constants that read constants too deep")));
        }
        let (body, init) = self.body.view.const_init(def).map_err(here)?;
        Frame { chain: self.chain + 1, limits: self.limits, ..Frame::new(body) }.eval(init)
    }
}

/// The places a row holds, as [`Value::places`] counts them.
fn places(c: &ConstValue) -> usize {
    match c {
        ConstValue::Array(cs) | ConstValue::Tuple(cs) | ConstValue::Struct(cs) => {
            cs.iter().map(places).sum::<usize>().max(1)
        }
        _ => 1,
    }
}

/// A value of the checker's table, as the type says. The rows of tuples and arrays are read; a struct (its field
/// types may be arguments of the type) is not: `Unavailable`.
pub(super) fn from_const(view: View, c: &ConstValue, ty: &Ty) -> Result<Value, Fault> {
    Ok(match (c, ty) {
        (ConstValue::Tuple(cs), Ty::Tuple(ts)) if cs.len() == ts.len() => {
            Value::tuple(cs.iter().zip(ts).map(|(c, t)| from_const(view, c, view.ty(*t))).collect::<Result<_, _>>()?)
        }
        (ConstValue::Array(cs), Ty::Array(t, Len::Const(n))) if cs.len() == *n as usize => {
            Value::Array(cs.iter().map(|c| from_const(view, c, view.ty(*t))).collect::<Result<_, _>>()?)
        }
        (ConstValue::Int(v), Ty::Int(k)) => Value::int(*k, *v),
        (ConstValue::Float(x), Ty::Float(k)) => Value::float(*k, *x),
        (ConstValue::Bool(b), Ty::Bool) => Value::Bool(*b),
        (ConstValue::Char(c), Ty::Char) => Value::Char(*c),
        (ConstValue::Unit, Ty::Unit) => Value::Unit,
        _ => return Err(Fault::Unavailable("a constant of a form the table does not give as the type says")),
    })
}
