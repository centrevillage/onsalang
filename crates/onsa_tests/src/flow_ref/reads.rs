//! What an assert reads of the outputs a `render` gave (`o.out[2]`, `o.l[c][k]`, `is_nan(o.out[0])`, `o.out.len()`, W7-19 U2a):
//! the path into the outputs read from the syntax tree and the tables, each component taken from the values the call gave.

use onsa_sema::prim::PrimRow;
use onsa_syntax::ast::{BinOp, ExprId, ExprKind};

use super::scalar::{Bin, Fault, PanicKind, binary};
use super::sema_view::Body;
use super::value::{IntKind, Value};
use super::walk::{Halt, Walk};

impl Walk<'_, '_> {
    /// The value of `e` when it reads what a render gave (`o.out[2]`, `is_nan(o.out[0])`, `o.out.len()`), else evaluated.
    pub(super) fn value(&mut self, body: Body, e: ExprId) -> Result<Value, Halt> {
        if !self.reads(body, e) || self.user_call(body, e) {
            return self.eval(body, e);
        }
        if let ExprKind::Paren(x) = &body.ast.expr(e).kind {
            return self.value(body, *x);
        }
        let ExprKind::Binary { op, lhs, rhs, .. } = &body.ast.expr(e).kind else { return self.shape(body, e) };
        // `a && b` and `a || b` of reads: the right side is read only where the left does not decide (§3.4).
        if let BinOp::And | BinOp::Or = op {
            let left = self.value(body, *lhs)?;
            return match (&left, op) {
                (Value::Bool(false), BinOp::And) | (Value::Bool(true), BinOp::Or) => Ok(left),
                _ => self.value(body, *rhs),
            };
        }
        let bin = match op {
            BinOp::Eq => Bin::Eq,
            BinOp::Ne => Bin::Ne,
            _ => return Err(Fault::Unavailable("an operator on what `render` gave").into()),
        };
        let (a, b) = (self.value(body, *lhs)?, self.value(body, *rhs)?);
        Ok(binary(bin, &a, &b)?)
    }

    /// A call of a function of the user (not a primitive, nor `len` of the channels): it reads the outputs a `render` gave as any other value does, by the struct that the `let` of the render holds (`Walk::bind`).
    fn user_call(&self, body: Body, e: ExprId) -> bool {
        let ExprKind::Call { .. } = &body.ast.expr(e).kind else { return false };
        body.callee(e).is_ok_and(|c| body.view.prim(c.def).is_none() && body.view.array_len() != Some(c.def))
    }

    fn reads(&self, body: Body, e: ExprId) -> bool {
        let local = matches!(body.target(e), Ok(onsa_sema::Target::Local(l)) if self.rendered.contains_key(l));
        local || body.ast.sub_exprs(e).into_iter().any(|x| self.reads(body, x))
    }

    /// A path into the outputs (`.out` or a field, then the channel and the frame), or a primitive on one.
    fn shape(&mut self, body: Body, e: ExprId) -> Result<Value, Halt> {
        match self.node(body, e)? {
            Node::One(v) => Ok(v),
            Node::Frames(..) => Err(Fault::Internal("a column read as a value").into()),
        }
    }

    fn node(&mut self, body: Body, e: ExprId) -> Result<Node, Halt> {
        let unavailable = || Halt::Fault(Fault::Unavailable("a form of an assert on what `render` gave"));
        match &body.ast.expr(e).kind {
            ExprKind::Paren(x) => self.node(body, *x),
            ExprKind::Field { base, name } => {
                let Ok(onsa_sema::Target::Local(l)) = body.target(*base) else { return Err(unavailable()) };
                let r = self.rendered.get(l).ok_or_else(unavailable)?;
                let at = r.fields.iter().position(|f| *f == name.name).ok_or_else(unavailable)?;
                Ok(Node::Frames(r.outs.iter().map(|v| part(v, at)).collect(), r.channels[at]))
            }
            ExprKind::Index { base, index } => {
                let (Node::Frames(c, channels), Value::Int(_, k, _)) =
                    (self.node(body, *base)?, self.value(body, *index)?)
                else {
                    return Err(unavailable());
                };
                let at = usize::try_from(k).map_err(|_| Fault::Panic(PanicKind::Bounds))?;
                match channels {
                    Some(n) if at < n => {
                        Ok(Node::Frames(c.iter().map(|v| elem(v, at)).collect::<Result<_, _>>()?, None))
                    }
                    Some(_) => Err(Fault::Panic(PanicKind::Bounds).into()),
                    None => Ok(Node::One(c.get(at).cloned().ok_or(Fault::Panic(PanicKind::Bounds))?)),
                }
            }
            ExprKind::Call { args, .. } => {
                let callee = body.callee(e)?;
                let receiver = onsa_sema::receiver(
                    body.ast,
                    match &body.ast.expr(e).kind {
                        ExprKind::Call { callee, .. } => *callee,
                        _ => e,
                    },
                );
                let arg = receiver.or(args.first().map(|a| a.expr)).ok_or_else(unavailable)?;
                match (body.view.prim(callee.def), self.node(body, arg)?) {
                    (Some(PrimRow::Len), Node::Frames(c, None)) => {
                        Ok(Node::One(Value::int(IntKind::U32, c.len() as i128)))
                    }
                    // `len` of the array of the channels (`[Buf[T]; N]`, std's `impl [T; N]`, no primitive): N.
                    (None, Node::Frames(_, Some(n))) if body.view.array_len() == Some(callee.def) => {
                        Ok(Node::One(Value::int(IntKind::U32, n as i128)))
                    }
                    (Some(PrimRow::IsNan), Node::One(Value::F32(x))) => Ok(Node::One(Value::Bool(x.is_nan()))),
                    (Some(PrimRow::IsNan), Node::One(Value::F64(x))) => Ok(Node::One(Value::Bool(x.is_nan()))),
                    (Some(PrimRow::ToBits(_)), Node::One(Value::F32(x))) => {
                        Ok(Node::One(Value::int(IntKind::U32, x.to_bits().into())))
                    }
                    (Some(PrimRow::ToBits(_)), Node::One(Value::F64(x))) => {
                        Ok(Node::One(Value::int(IntKind::U64, x.to_bits().into())))
                    }
                    _ => Err(unavailable()),
                }
            }
            _ => Err(unavailable()),
        }
    }
}

/// The value of a `Rendered` that a `render` gave, as the evaluator reads it (`rendered_value`): each field is the frames of one output, or the channels of it (the frames of each) when the output is an array.
pub(super) fn rendered_struct(outs: &[Value], fields: usize) -> Result<Value, Fault> {
    let field = |at: usize| -> Result<Value, Fault> {
        let frames: Vec<Value> = outs.iter().map(|v| part(v, at)).collect();
        match frames.first() {
            Some(Value::Array(a)) => {
                let channel = |k| frames.iter().map(|v| elem(v, k)).collect::<Result<_, _>>().map(Value::Array);
                (0..a.len()).map(channel).collect::<Result<_, _>>().map(Value::Array)
            }
            _ => Ok(Value::Array(frames)),
        }
    };
    Ok(Value::Struct((0..fields).map(field).collect::<Result<_, _>>()?))
}

/// The field `at` of a struct output, or the output itself (it is no struct).
pub(super) fn part(v: &Value, at: usize) -> Value {
    if let Value::Struct(fs) = v { fs[at].clone() } else { v.clone() }
}

/// What a path into the outputs is so far: the values of one component in each frame (and its channels, when it is an
/// array of them: its length, though there are no frames), or one value.
enum Node {
    Frames(Vec<Value>, Option<usize>),
    One(Value),
}

pub(super) fn elem(v: &Value, at: usize) -> Result<Value, Fault> {
    match v {
        Value::Array(a) => a.get(at).cloned().ok_or(Fault::Panic(PanicKind::Bounds)),
        _ => Err(Fault::Internal("a channel of a value that is not an array")),
    }
}
