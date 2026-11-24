//! The expressions of the evaluator (§11.2): names, literals, parentheses, the operators
//! of §3.4 with the short circuit of `&&` and `||` (§3.5), `as` (§3.3), `at` (§11.3: it
//! changes neither the value nor the stage), `if` (§11.5: only the branch taken) and the
//! blocks that hold them. The operands are evaluated from the left (§3.5), and a panic is
//! a [`Stop`] at the span of the expression it comes from. Each value is checked against
//! the type of the table (the memo's way (1)): a disagreement is an internal error, not a guess.
//! The aggregates are in [`super::aggregate`], the patterns in [`super::pattern`], the calls in [`super::call`]. The
//! other forms (the forms of a flow) are [`Fault::Unavailable`] until the units that have them.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use onsa_diag::Span;
use onsa_sema::ty::{FloatKind, Len};
use onsa_sema::{ConstValue, DefId, LocalId, Target, Ty};
use onsa_syntax::ast::{BinOp, Block, CallKind, ExprId, ExprKind, Lit, PatId, StmtKind, UnOp};
use onsa_syntax::{FloatWidth, float_value};

use super::flow::Clock;
use super::host::FnHost;
use super::scalar::{Bin, Fault, Un, binary, cast, unary};
use super::sema_view::{Body, View};
use super::state::Run;
use super::value::{Scalar, Value, sum_places};

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
/// within it. 2^20 places are 40 MB in a value. In a tree they are a value, a cell of a delay line, a value a `let` keeps,
/// and in an instance 8 and one for each step of its body, and they cost (2026-11-18, `guard.py` on `par~ i in 0 ..< 1000000 {
/// prev~(x) }` and on 60 000 instances of a flow, less the 70 MB of the test binary): some 700 B for the node of a delay in
/// a `par~` (its key, its two stores, its entry in a map), some 3.7 KB for an instance, so that a tree at the limit is some
/// 700 MB of nodes, or 130 000 instances (some 500 MB), and not the 150 MB a place of a value would make it.
pub const LIMITS: Limits = Limits { reserve: 4 << 20, most: 1 << 20 };

impl Limits {
    /// Does the evaluator hold this many places? The one judgment of the limit (a row of a constant, `[e; N]`, an array of the default, the replicas of a
    /// `par~` and their values, the places of a tree).
    pub fn holds(self, places: usize) -> bool {
        places <= self.most
    }
}

/// The parts a stage made: by expression, the stage (`reset_if~` puts back those of a tick, `Frame::restart`), then by the replicas it is in (empty outside a `par~`).
pub(super) type Hoisted = HashMap<ExprId, (Clock, HashMap<Vec<u32>, Value>)>;

pub(super) const LOW_STACK: Fault = Fault::Unavailable("the stack is nearly used up");

/// The evaluation of one body: the values its locals have so far.
pub struct Frame<'a> {
    pub body: Body<'a>,
    pub locals: HashMap<LocalId, Value>,
    pub limits: Limits,
    /// Where the calls the evaluator does not evaluate go; none is [`super::host::NoHost`].
    pub host: Option<&'a mut dyn FnHost>,
    /// The state of the flow instance this evaluation is a tick of, and what its delays save (none for a function).
    pub run: Option<Run>,
    /// The values of the parts of the body that a stage before the one of their `let` has made (`flow::pre`, §11.3), by
    /// expression and by the replica of each `par~` around it (a part of the body of a `par~` has a value for each replica, as
    /// its field does, S-1140): `eval` of such a part gives the value that was kept, and does not make it again (the panic of it
    /// was the one of the stage that made it). Empty for a function.
    pub(super) hoisted: Hoisted,
    chain: u32,
    /// Which of the functions called from here the evaluator evaluates itself (`call::plain`), kept by declaration: a
    /// recursive function is not walked at each call. A frame of a call or a constant shares it with the one that made it.
    pub(super) plain: Rc<RefCell<HashMap<DefId, bool>>>,
    /// The calls this evaluation is inside of (§12.5): 0 at its entry, and a `const` starts at its own entry.
    depth: u32,
}

/// The one list of the forms the evaluator evaluates: `Frame::form` has an arm for each of them, and `call::plain` asks
/// it of every expression a function evaluates, which has any other go to the host. There is no `_`: a form added to
/// the syntax is put on one side here. `At` is on the list for a flow; a function body cannot write it (E0821).
pub(super) fn evaluates(body: &Body, e: ExprId) -> bool {
    use ExprKind as K;
    let ast = body.ast;
    // A name that is a value: a local, a constant or a variant (a function is not, nor a `panic`).
    let value = || matches!(body.target(e), Ok(Target::Local(_) | Target::Const { .. } | Target::Variant { .. }));
    match &ast.expr(e).kind {
        K::Block(b) => b.stmts.iter().all(|s| matches!(ast.stmt(*s).kind, StmtKind::Let { .. })),
        K::Lit(l) => !matches!(l, Lit::Str(_)),
        K::Path(_) => value(),
        K::Field { .. } => !body.names(e) || value(),
        K::Call { kind: CallKind::Plain, .. } => {
            let call = matches!(
                body.target(e),
                Ok(Target::Variant { .. } | Target::Fn { .. } | Target::Method { .. } | Target::Panic)
            );
            call || body.time_call(e)
        }
        K::Par { .. } => true,
        K::If { .. } | K::Match { .. } => true,
        K::Paren(_) | K::At { .. } | K::Binary { .. } | K::Unary { .. } | K::Cast { .. } | K::Index { .. } => true,
        K::TupleIndex { .. } | K::Struct { .. } | K::Tuple(_) | K::Array(_) | K::Repeat { .. } => true,
        K::Call { kind: CallKind::Flow, .. } | K::Feedback(_) => true,
        K::Call { .. } | K::Hole | K::Error | K::Closure { .. } | K::Handle { .. } | K::Unsafe(_) => false,
        K::TypeArgs { .. } | K::Try(_) | K::Move(_) | K::Range(_) => false,
    }
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
        Frame {
            body,
            locals: HashMap::new(),
            limits: LIMITS,
            host: None,
            run: None,
            hoisted: HashMap::new(),
            chain: 0,
            plain: Rc::default(),
            depth: 0,
        }
    }

    /// `expr` of the body of a function called from this frame, with `locals` its parameters: the same limits and
    /// host (taken for the call and given back), one call deeper.
    pub(super) fn run_callee(&mut self, body: Body<'a>, locals: HashMap<LocalId, Value>, expr: ExprId) -> Eval {
        let host = self.host.take();
        let plain = self.plain.clone();
        let mut inner = Frame {
            body,
            locals,
            limits: self.limits,
            host,
            run: None,
            hoisted: HashMap::new(),
            chain: self.chain,
            plain,
            depth: self.depth + 1,
        };
        let value = inner.eval(expr);
        self.host = inner.host.take();
        value
    }

    /// The number of calls this evaluation is inside of.
    pub(super) fn depth(&self) -> u32 {
        self.depth
    }

    /// Is the stack left under what the limits keep back? (`Unavailable`: [`LOW_STACK`].)
    #[inline(never)]
    pub(super) fn low_stack(&self) -> bool {
        onsa_diag::stack::remaining().is_some_and(|left| left < self.limits.reserve)
    }

    /// The value of `e`, which has the type the table gives it. Call it on a large stack (`mod.rs`): it recurses.
    pub fn eval(&mut self, e: ExprId) -> Eval {
        if let Some(kept) = self.hoisted.get(&e) {
            let replicas = self.run.as_ref().map_or(&[][..], |r| &r.replicas[..]);
            if let Some(v) = kept.1.get(replicas) {
                return Ok(v.clone());
            }
        }
        let at = self.body.ast.expr(e).span;
        if self.low_stack() {
            return Err(Stop { fault: LOW_STACK, at });
        }
        let v = self.form(e, at)?;
        match self.body.ty(e).and_then(|ty| v.agrees(ty, self.body.view)) {
            Ok(true) => Ok(v),
            // A type the checker did not make (`Ty::Error`: a form the check gave an error, such as one of the E0200 of this version) is a body with tables that are not whole.
            Ok(false) if matches!(self.body.ty(e), Ok(Ty::Error)) => {
                Err(Stop { fault: Fault::Unavailable("a body whose tables are not whole"), at })
            }
            Ok(false) => Err(Stop { fault: Fault::Internal("the value is not of the type of the table"), at }),
            Err(fault) => Err(Stop { fault, at }),
        }
    }

    /// The form of `e`: each one with work to do is its own function, so that the frame of a deep recursion is small.
    /// The forms with an arm are the ones [`evaluates`] lists, and the others are not met here.
    fn form(&mut self, e: ExprId, at: Span) -> Eval {
        let here = |fault| Stop { fault, at };
        Ok(match &self.body.ast.expr(e).kind {
            _ if !evaluates(&self.body, e) => return Err(here(Fault::Unavailable("a form of a later unit"))),
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
            ExprKind::Call { callee, args, kind: CallKind::Plain } => return self.call(e, *callee, args, at),
            ExprKind::Match { tilde: None, .. } => return self.select(e, at),
            ExprKind::Match { .. } => return self.select_all(e, at),
            ExprKind::Par { .. } => return self.par(e),
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
            ExprKind::If { .. } => return self.all_branches(e, at),
            ExprKind::Block(b) => return self.block(b, at),
            ExprKind::Feedback(_) | ExprKind::Call { kind: CallKind::Flow, .. } => return self.stateful(e, at),
            _ => return Err(here(Fault::Internal("a form of the list with no arm"))),
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
                return Err(here(Fault::Internal("a statement that is not a `let`")));
            };
            self.bind(*pat, *init)?;
        }
        b.tail.map_or(Ok(Value::Unit), |tail| self.eval(tail))
    }

    /// A `let`: the value of `init`, taken apart by `pat` into its locals (§11.2).
    pub(super) fn bind(&mut self, pat: PatId, init: ExprId) -> Result<(), Stop> {
        let v = self.eval(init)?;
        self.keep_places(init, &v)?;
        let ty = self.body.ty(init).map_err(|fault| Stop { fault, at: self.body.ast.expr(init).span })?;
        self.destructure(pat, &v, ty)
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
            _ => Err(here(Fault::Internal("a name that is not a value"))),
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
        if let Some(c) = self.body.view.const_value(def).filter(|c| self.limits.holds(places(c))) {
            match from_const(self.body.view, c, ty) {
                Err(Fault::Unavailable(_)) => {}
                v => return v.map_err(here),
            }
        }
        if self.chain >= CHAIN {
            return Err(here(Fault::Unavailable("constants that read constants too deep")));
        }
        let (body, init) = self.body.view.const_init(def).map_err(here)?;
        let host = self.host.take();
        let mut inner =
            Frame { chain: self.chain + 1, limits: self.limits, host, plain: self.plain.clone(), ..Frame::new(body) };
        let value = inner.eval(init);
        self.host = inner.host.take();
        value
    }
}

/// The places a row holds, as [`Value::places`] counts them.
fn places(c: &ConstValue) -> usize {
    match c {
        ConstValue::Array(cs) | ConstValue::Tuple(cs) | ConstValue::Struct(cs) => sum_places(cs.iter().map(places)),
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
