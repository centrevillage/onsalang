//! Interpreter for Onsa Core; the reference semantics (M3, T3-7).
//!
//! A tree walker over [`onsa_core::Module`]. Numerics follow spec §3.4 and
//! §13.4 exactly: `F32` arithmetic stays in `f32`, integer operators are
//! checked / wrapping / saturating per instruction, every index is
//! bounds-checked, and a panic (§9.2) unwinds to the nearest call made from
//! outside the interpreter (a test, a `const` initializer, a tool).
//!
//! # Places and aliasing
//!
//! Every local lives in a [`Slot`]; an `inout` parameter is an alias of the
//! caller's place (slot + projections), so writes through it land in the
//! caller's storage. `Span` values carry their slot too (see `value.rs`).
//!
//! # Decisions recorded for the spec (S-25)
//!
//! - `round` is round-half-to-even (IEEE `roundToIntegralTiesToEven`, like
//!   the `round_f32` conversions of §3.3, WASM `nearest`, C `rint` under the
//!   default rounding mode). Half-away-from-zero is not available.
//! - `min` / `max` return NaN when either operand is NaN (WASM / JS
//!   semantics; the C backend must not use `fminf`), `min(-0.0, 0.0)` is
//!   `-0.0` and `max(-0.0, 0.0)` is `0.0`.

pub mod value;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use onsa_core::prim::{CheckedOp, MathFn, Prim};
use onsa_core::{
    Arg, BinOp, Block, CmpOp, ConstId, Expr, ExprKind, FloatKind, FnId, Lit, LocalId, LogicOp, Mode, Module, Overflow,
    Place, Stmt, StmtKind, Ty, TypeDefKind, UnOp,
};
use onsa_diag::Span;

pub use value::{ArrayData, Proj, Slot, SpanRef, Value, show, slot, zero};
use value::{clamp_int, in_range, int_value, wrap_int, zero_array};

/// A panic (spec §9.2) with the position of the instruction that raised it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Panic {
    pub message: String,
    pub span: Span,
}

/// Non-local control flow inside the interpreter.
#[derive(Debug)]
enum Signal {
    Panic(Panic),
    Return(Value),
    Break,
    Continue,
}

type R<T> = Result<T, Signal>;

fn panic<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(Signal::Panic(Panic { message: msg.into(), span }))
}

/// A resolved memory location: a slot and the projections inside its value.
#[derive(Debug, Clone)]
struct PlaceRef {
    root: Slot,
    projs: Vec<Proj>,
}

/// What a local binding refers to.
#[derive(Debug, Clone)]
enum Loc {
    Slot(Slot),
    /// An `inout` parameter: the caller's place.
    Alias(PlaceRef),
}

struct Frame {
    locals: Vec<Option<Loc>>,
}

/// A leaf found by walking projections.
enum Leaf<'a> {
    Val(&'a Value),
    F32(f32),
}

enum LeafMut<'a> {
    Val(&'a mut Value),
    F32(&'a mut f32),
}

/// An argument after evaluation: a value, or the caller's place for `inout`.
enum ArgVal {
    Val(Value),
    Place(PlaceRef),
}

/// A sequence a prim reads or writes: the array at `root` + `projs`, from
/// `start` for `len` elements.
struct SeqRef {
    root: Slot,
    projs: Vec<Proj>,
    start: u32,
    len: u32,
}

enum ConstState {
    Unevaluated,
    InProgress,
    Done(Value),
}

const MAX_DEPTH: u32 = 4096;

pub struct Interp<'m> {
    pub m: &'m Module,
    consts: Vec<RefCell<ConstState>>,
    depth: Cell<u32>,
}

impl<'m> Interp<'m> {
    pub fn new(m: &'m Module) -> Interp<'m> {
        Interp {
            m,
            consts: m.consts.iter().map(|_| RefCell::new(ConstState::Unevaluated)).collect(),
            depth: Cell::new(0),
        }
    }

    pub fn fn_by_name(&self, name: &str) -> Option<FnId> {
        self.m.fns.iter().position(|f| f.name == name).map(|i| FnId(i as u32))
    }

    /// Call a function with by-value arguments (an `inout` parameter gets a
    /// fresh slot, so the caller does not see its writes; use
    /// [`Interp::call_inout`] for that).
    pub fn call(&self, fn_: FnId, args: Vec<Value>) -> Result<Value, Panic> {
        self.call_with(fn_, args.into_iter().map(ArgVal::Val).collect()).map_err(Self::into_panic)
    }

    /// Call with an `inout` first argument held in `state` (flows: `process(inout s, ...)`).
    pub fn call_inout(&self, fn_: FnId, state: &Slot, rest: Vec<Value>) -> Result<Value, Panic> {
        let mut args = vec![ArgVal::Place(PlaceRef { root: state.clone(), projs: Vec::new() })];
        args.extend(rest.into_iter().map(ArgVal::Val));
        self.call_with(fn_, args).map_err(Self::into_panic)
    }

    /// Value of a `const` (evaluated on first use; T3-9).
    pub fn const_value(&self, id: ConstId) -> Result<Value, Panic> {
        self.const_val(id).map_err(Self::into_panic)
    }

    fn into_panic(s: Signal) -> Panic {
        match s {
            Signal::Panic(p) => p,
            Signal::Return(_) | Signal::Break | Signal::Continue => Panic {
                message: "internal: control flow escaped a function".into(),
                span: Span::new(onsa_diag::FileId(0), 0, 0),
            },
        }
    }

    fn const_val(&self, id: ConstId) -> R<Value> {
        let cell = &self.consts[id.0 as usize];
        {
            let st = cell.borrow();
            match &*st {
                ConstState::Done(v) => return Ok(v.clone()),
                ConstState::InProgress => {
                    return panic(
                        self.m.const_(id).init.span,
                        format!("const `{}` depends on itself", self.m.const_(id).name),
                    );
                }
                ConstState::Unevaluated => {}
            }
        }
        *cell.borrow_mut() = ConstState::InProgress;
        let mut f = Frame { locals: Vec::new() };
        let r = self.eval(&mut f, &self.m.const_(id).init);
        match r {
            Ok(v) => {
                *cell.borrow_mut() = ConstState::Done(v.clone());
                Ok(v)
            }
            Err(e) => {
                *cell.borrow_mut() = ConstState::Unevaluated;
                Err(e)
            }
        }
    }

    // ------------------------------------------------------------ calls

    fn call_with(&self, fn_: FnId, args: Vec<ArgVal>) -> R<Value> {
        let f = self.m.fn_(fn_);
        let Some(body) = &f.body else {
            return panic(f.span, format!("`{}` has no body in this version (target function)", f.name));
        };
        if self.depth.get() >= MAX_DEPTH {
            return panic(f.span, "call depth limit reached");
        }
        if args.len() != f.params.len() {
            return panic(f.span, format!("internal: `{}` called with {} arguments", f.name, args.len()));
        }
        let mut frame = Frame { locals: vec![None; f.locals.len()] };
        for (p, a) in f.params.iter().zip(args) {
            let loc = match (p.mode, a) {
                (Mode::Inout, ArgVal::Place(pr)) => Loc::Alias(pr),
                (_, ArgVal::Val(v)) => Loc::Slot(slot(v)),
                (_, ArgVal::Place(pr)) => Loc::Slot(slot(self.read(&pr)?)),
            };
            frame.locals[p.local.0 as usize] = Some(loc);
        }
        self.depth.set(self.depth.get() + 1);
        let r = self.exec_block(&mut frame, body);
        self.depth.set(self.depth.get() - 1);
        match r {
            Ok(v) => Ok(v),
            Err(Signal::Return(v)) => Ok(v),
            Err(Signal::Break) | Err(Signal::Continue) => panic(f.span, "internal: loop control outside a loop"),
            Err(e) => Err(e),
        }
    }

    // ------------------------------------------------------------ places

    fn local_place(&self, f: &Frame, l: LocalId, span: Span) -> R<PlaceRef> {
        match &f.locals[l.0 as usize] {
            Some(Loc::Slot(s)) => Ok(PlaceRef { root: s.clone(), projs: Vec::new() }),
            Some(Loc::Alias(p)) => Ok(p.clone()),
            None => panic(span, "internal: local read before initialization"),
        }
    }

    fn resolve_place(&self, f: &mut Frame, p: &Place, span: Span) -> R<PlaceRef> {
        match p {
            Place::Local(l) => self.local_place(f, *l, span),
            Place::Field(b, i) => {
                let r = self.resolve_place(f, b, span)?;
                self.project_field(r, *i, span)
            }
            Place::Index(b, e) => {
                let i = self.eval_u32(f, e)?;
                let r = self.resolve_place(f, b, span)?;
                self.project_index(r, i, span)
            }
        }
    }

    fn project_field(&self, mut r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        let ok = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Struct(fs)) | Leaf::Val(Value::Tuple(fs)) | Leaf::Val(Value::Enum { fields: fs, .. }) => {
                (i as usize) < fs.len()
            }
            _ => false,
        })?;
        if !ok {
            return panic(span, "internal: field projection on a non-aggregate");
        }
        r.projs.push(Proj::Field(i));
        Ok(r)
    }

    /// Index into the sequence at `r`, following `Span` / `Buf` indirection.
    fn project_index(&self, r: PlaceRef, i: u32, span: Span) -> R<PlaceRef> {
        enum Kind {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let kind = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => Kind::Array(a.len()),
            Leaf::Val(Value::Span(s)) => Kind::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => Kind::Buf(b.clone()),
            _ => Kind::Other,
        })?;
        match kind {
            Kind::Array(len) => {
                if i >= len {
                    return panic(span, format!("index {i} out of range for a sequence of length {len}"));
                }
                let mut r = r;
                r.projs.push(Proj::Index(i));
                Ok(r)
            }
            Kind::Span(s) => {
                if i >= s.len {
                    return panic(span, format!("index {i} out of range for a span of length {}", s.len));
                }
                let mut projs = s.projs.clone();
                projs.push(Proj::Index(s.start + i));
                Ok(PlaceRef { root: s.root, projs })
            }
            Kind::Buf(b) => {
                let len = match &*b.borrow() {
                    Value::Array(a) => a.len(),
                    _ => 0,
                };
                if i >= len {
                    return panic(span, format!("index {i} out of range for a buffer of length {len}"));
                }
                Ok(PlaceRef { root: b, projs: vec![Proj::Index(i)] })
            }
            Kind::Other => panic(span, "internal: index on a non-sequence"),
        }
    }

    fn walk<'a>(v: &'a Value, projs: &[Proj]) -> Option<Leaf<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get(*i as usize).map(|x| Leaf::F32(*x)) } else { None };
                }
                _ => return None,
            }
        }
        Some(Leaf::Val(cur))
    }

    fn walk_mut<'a>(v: &'a mut Value, projs: &[Proj]) -> Option<LeafMut<'a>> {
        let mut cur = v;
        for (k, p) in projs.iter().enumerate() {
            match (cur, p) {
                (Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. }, Proj::Field(i)) => {
                    cur = fs.get_mut(*i as usize)?;
                }
                (Value::Array(ArrayData::Any(xs)), Proj::Index(i)) => cur = xs.get_mut(*i as usize)?,
                (Value::Array(ArrayData::F32(xs)), Proj::Index(i)) => {
                    return if k + 1 == projs.len() { xs.get_mut(*i as usize).map(LeafMut::F32) } else { None };
                }
                _ => return None,
            }
        }
        Some(LeafMut::Val(cur))
    }

    fn peek<T>(&self, r: &PlaceRef, span: Span, f: impl FnOnce(Leaf<'_>) -> T) -> R<T> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(leaf) => Ok(f(leaf)),
            None => panic(span, "internal: dangling place"),
        }
    }

    fn read(&self, r: &PlaceRef) -> R<Value> {
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => panic(Span::new(onsa_diag::FileId(0), 0, 0), "internal: dangling place"),
        }
    }

    fn write(&self, r: &PlaceRef, value: Value, span: Span) -> R<()> {
        let mut v = r.root.borrow_mut();
        match Self::walk_mut(&mut v, &r.projs) {
            Some(LeafMut::Val(x)) => {
                *x = value;
                Ok(())
            }
            Some(LeafMut::F32(x)) => match value {
                Value::F32(y) => {
                    *x = y;
                    Ok(())
                }
                _ => panic(span, "internal: non-F32 written into an F32 array"),
            },
            None => panic(span, "internal: dangling place"),
        }
    }

    /// The sequence an expression denotes (a `Span` value, a `Buf`, or an
    /// array place); temporaries are copied into a fresh slot.
    fn seq_of_arg(&self, f: &mut Frame, a: &Arg) -> R<SeqRef> {
        let span = a.expr.span;
        if a.mode == Mode::Inout
            && let Some(p) = a.expr.as_place()
        {
            let r = self.resolve_place(f, &p, span)?;
            return self.seq_of_place(r, span);
        }
        let v = self.eval(f, &a.expr)?;
        self.seq_of_value(v, span)
    }

    fn seq_of_place(&self, r: PlaceRef, span: Span) -> R<SeqRef> {
        enum K {
            Array(u32),
            Span(SpanRef),
            Buf(Slot),
            Other,
        }
        let k = self.peek(&r, span, |v| match v {
            Leaf::Val(Value::Array(a)) => K::Array(a.len()),
            Leaf::Val(Value::Span(s)) => K::Span(s.clone()),
            Leaf::Val(Value::Buf(b)) => K::Buf(b.clone()),
            _ => K::Other,
        })?;
        match k {
            K::Array(len) => Ok(SeqRef { root: r.root, projs: r.projs, start: 0, len }),
            K::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            K::Buf(b) => {
                let len = buf_len(&b);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            K::Other => panic(span, "internal: sequence expected"),
        }
    }

    fn seq_of_value(&self, v: Value, span: Span) -> R<SeqRef> {
        match v {
            Value::Span(s) => Ok(SeqRef { root: s.root, projs: s.projs, start: s.start, len: s.len }),
            Value::Buf(b) => {
                let len = buf_len(&b);
                Ok(SeqRef { root: b, projs: Vec::new(), start: 0, len })
            }
            Value::Array(a) => {
                let len = a.len();
                Ok(SeqRef { root: slot(Value::Array(a)), projs: Vec::new(), start: 0, len })
            }
            _ => panic(span, "internal: sequence expected"),
        }
    }

    fn seq_get(&self, s: &SeqRef, i: u32, span: Span) -> R<Value> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        let r = PlaceRef { root: s.root.clone(), projs };
        let v = r.root.borrow();
        match Self::walk(&v, &r.projs) {
            Some(Leaf::Val(x)) => Ok(x.clone()),
            Some(Leaf::F32(x)) => Ok(Value::F32(x)),
            None => panic(span, "internal: dangling sequence"),
        }
    }

    fn seq_set(&self, s: &SeqRef, i: u32, v: Value, span: Span) -> R<()> {
        let mut projs = s.projs.clone();
        projs.push(Proj::Index(s.start + i));
        self.write(&PlaceRef { root: s.root.clone(), projs }, v, span)
    }

    /// Fast path: the `f32` slice of a sequence, when its storage is `F32`.
    fn with_f32_slice<T>(&self, s: &SeqRef, f: impl FnOnce(&mut [f32]) -> T) -> Option<T> {
        let mut v = s.root.borrow_mut();
        match Self::walk_mut(&mut v, &s.projs) {
            Some(LeafMut::Val(Value::Array(ArrayData::F32(xs)))) => {
                let (a, b) = (s.start as usize, (s.start + s.len) as usize);
                Some(f(&mut xs[a..b]))
            }
            _ => None,
        }
    }

    // ------------------------------------------------------------ statements

    /// Run a block; its value, or `()`.
    fn exec_block(&self, f: &mut Frame, b: &Block) -> R<Value> {
        for s in &b.stmts {
            self.exec(f, s)?;
        }
        match &b.value {
            Some(e) => self.eval(f, e),
            None => Ok(Value::Unit),
        }
    }

    fn exec(&self, f: &mut Frame, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                let v = self.eval(f, e)?;
                f.locals[l.0 as usize] = Some(Loc::Slot(slot(v)));
                Ok(())
            }
            StmtKind::Assign(p, e) => {
                let v = self.eval(f, e)?;
                let r = self.resolve_place(f, p, s.span)?;
                self.write(&r, v, s.span)
            }
            StmtKind::Expr(e) => {
                self.eval(f, e)?;
                Ok(())
            }
            StmtKind::If(c, t, e) => {
                let c = self.eval_bool(f, c)?;
                self.exec_block(f, if c { t } else { e })?;
                Ok(())
            }
            StmtKind::While(c, body) => {
                while self.eval_bool(f, c)? {
                    match self.exec_block(f, body) {
                        Ok(_) | Err(Signal::Continue) => {}
                        Err(Signal::Break) => break,
                        Err(e) => return Err(e),
                    }
                }
                Ok(())
            }
            StmtKind::ForRange(l, lo, hi, body) => {
                let lo_v = self.eval(f, lo)?;
                let hi_v = self.eval(f, hi)?;
                let kind = lo_v
                    .int_kind()
                    .ok_or_else(|| Signal::Panic(Panic { message: "internal: range bound".into(), span: s.span }))?;
                let (lo_i, hi_i) = (lo_v.to_i128().unwrap(), hi_v.to_i128().unwrap_or(0));
                let var = slot(lo_v);
                f.locals[l.0 as usize] = Some(Loc::Slot(var.clone()));
                let mut i = lo_i;
                while i < hi_i {
                    *var.borrow_mut() = int_value(kind, i);
                    match self.exec_block(f, body) {
                        Ok(_) | Err(Signal::Continue) => {}
                        Err(Signal::Break) => break,
                        Err(e) => return Err(e),
                    }
                    i += 1;
                }
                Ok(())
            }
            StmtKind::Break => Err(Signal::Break),
            StmtKind::Continue => Err(Signal::Continue),
            StmtKind::Return(e) => {
                let v = match e {
                    Some(e) => self.eval(f, e)?,
                    None => Value::Unit,
                };
                Err(Signal::Return(v))
            }
        }
    }

    // ------------------------------------------------------------ expressions

    fn eval_bool(&self, f: &mut Frame, e: &Expr) -> R<bool> {
        match self.eval(f, e)? {
            Value::Bool(b) => Ok(b),
            _ => panic(e.span, "internal: Bool expected"),
        }
    }

    fn eval_u32(&self, f: &mut Frame, e: &Expr) -> R<u32> {
        match self.eval(f, e)? {
            Value::U32(x) => Ok(x),
            v => match v.to_i128() {
                Some(i) if (0..=u32::MAX as i128).contains(&i) => Ok(i as u32),
                _ => panic(e.span, "internal: U32 expected"),
            },
        }
    }

    fn eval_args(&self, f: &mut Frame, args: &[Arg]) -> R<Vec<ArgVal>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            if a.mode == Mode::Inout
                && let Some(p) = a.expr.as_place()
            {
                out.push(ArgVal::Place(self.resolve_place(f, &p, a.expr.span)?));
            } else {
                out.push(ArgVal::Val(self.eval(f, &a.expr)?));
            }
        }
        Ok(out)
    }

    fn eval(&self, f: &mut Frame, e: &Expr) -> R<Value> {
        let span = e.span;
        match &e.kind {
            ExprKind::Lit(l) => Ok(match l {
                Lit::Int(n) => match &e.ty {
                    Ty::Int(k) => int_value(*k, *n),
                    _ => return panic(span, "internal: integer literal type"),
                },
                Lit::F32(x) => Value::F32(*x),
                Lit::F64(x) => Value::F64(*x),
                Lit::Bool(b) => Value::Bool(*b),
                Lit::Char(c) => Value::Char(*c),
                Lit::Unit => Value::Unit,
            }),
            ExprKind::Local(l) => {
                let r = self.local_place(f, *l, span)?;
                self.read(&r)
            }
            ExprKind::Const(c) => self.const_val(*c),
            ExprKind::Zeroed => Ok(zero(self.m, &e.ty)),
            ExprKind::Unary(op, x) => {
                let v = self.eval(f, x)?;
                self.unary(*op, v, span)
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                let a = self.eval(f, lhs)?;
                let b = self.eval(f, rhs)?;
                self.binary(*op, *overflow, a, b, span)
            }
            ExprKind::Cmp { op, lhs, rhs } => {
                let a = self.eval(f, lhs)?;
                let b = self.eval(f, rhs)?;
                Ok(Value::Bool(self.compare(*op, &a, &b, span)?))
            }
            ExprKind::Logic { op, lhs, rhs } => {
                let a = self.eval_bool(f, lhs)?;
                Ok(Value::Bool(match op {
                    LogicOp::And => a && self.eval_bool(f, rhs)?,
                    LogicOp::Or => a || self.eval_bool(f, rhs)?,
                }))
            }
            ExprKind::Cast(x) => {
                let v = self.eval(f, x)?;
                self.cast(v, &e.ty, span)
            }
            ExprKind::Call { fn_, args } => {
                let args = self.eval_args(f, args)?;
                self.call_with(*fn_, args)
            }
            ExprKind::Prim { prim, args } => self.prim(f, prim, args, &e.ty, span),
            ExprKind::Field { base, index } => {
                if let Some(p) = base.as_place() {
                    let r = self.resolve_place(f, &p, span)?;
                    let r = self.project_field(r, *index, span)?;
                    return self.read(&r);
                }
                match self.eval(f, base)? {
                    Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. } => fs
                        .into_iter()
                        .nth(*index as usize)
                        .ok_or_else(|| Signal::Panic(Panic { message: "internal: field".into(), span })),
                    _ => panic(span, "internal: field on a non-aggregate"),
                }
            }
            ExprKind::Index { base, index } => {
                if let Some(p) = base.as_place() {
                    let i = self.eval_u32(f, index)?;
                    let r = self.resolve_place(f, &p, span)?;
                    let r = self.project_index(r, i, span)?;
                    return self.read(&r);
                }
                let v = self.eval(f, base)?;
                let i = self.eval_u32(f, index)?;
                let s = self.seq_of_value(v, span)?;
                if i >= s.len {
                    return panic(span, format!("index {i} out of range for a sequence of length {}", s.len));
                }
                self.seq_get(&s, i, span)
            }
            ExprKind::SpanOf(inner) => {
                let s = match inner.as_place() {
                    Some(p) => {
                        let r = self.resolve_place(f, &p, span)?;
                        self.seq_of_place(r, span)?
                    }
                    None => {
                        let v = self.eval(f, inner)?;
                        self.seq_of_value(v, span)?
                    }
                };
                Ok(Value::Span(SpanRef { root: s.root, projs: s.projs, start: s.start, len: s.len }))
            }
            ExprKind::Struct { fields, .. } => {
                let mut out = Vec::with_capacity(fields.len());
                for x in fields {
                    out.push(self.eval(f, x)?);
                }
                Ok(Value::Struct(out))
            }
            ExprKind::Variant { tag, fields, .. } => {
                let mut out = Vec::with_capacity(fields.len());
                for x in fields {
                    out.push(self.eval(f, x)?);
                }
                Ok(Value::Enum { tag: *tag, fields: out })
            }
            ExprKind::Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                for x in items {
                    out.push(self.eval(f, x)?);
                }
                let elem = match &e.ty {
                    Ty::Array(el, _) => (**el).clone(),
                    _ => return panic(span, "internal: array literal type"),
                };
                Ok(Value::Array(ArrayData::from_values(&elem, out)))
            }
            ExprKind::Repeat { elem, n } => {
                let v = self.eval(f, elem)?;
                Ok(Value::Array(match v {
                    Value::F32(x) => ArrayData::F32(vec![x; *n as usize]),
                    v => ArrayData::Any(vec![v; *n as usize]),
                }))
            }
            ExprKind::Tuple(items) => {
                let mut out = Vec::with_capacity(items.len());
                for x in items {
                    out.push(self.eval(f, x)?);
                }
                Ok(Value::Tuple(out))
            }
            ExprKind::Tag(x) => {
                let tag = match x.as_place() {
                    Some(p) => {
                        let r = self.resolve_place(f, &p, span)?;
                        self.peek(&r, span, |v| match v {
                            Leaf::Val(Value::Enum { tag, .. }) => Some(*tag),
                            _ => None,
                        })?
                    }
                    None => match self.eval(f, x)? {
                        Value::Enum { tag, .. } => Some(tag),
                        _ => None,
                    },
                };
                let Some(tag) = tag else { return panic(span, "internal: tag of a non-enum") };
                match &e.ty {
                    Ty::Int(k) => Ok(int_value(*k, tag as i128)),
                    _ => panic(span, "internal: tag type"),
                }
            }
            ExprKind::Payload { base, tag, index } => {
                if let Some(p) = base.as_place() {
                    let r = self.resolve_place(f, &p, span)?;
                    let ok =
                        self.peek(&r, span, |v| matches!(v, Leaf::Val(Value::Enum { tag: t, .. }) if *t == *tag))?;
                    if !ok {
                        return panic(span, "internal: payload of the wrong variant");
                    }
                    let r = self.project_field(r, *index, span)?;
                    return self.read(&r);
                }
                match self.eval(f, base)? {
                    Value::Enum { tag: t, fields } if t == *tag => fields
                        .into_iter()
                        .nth(*index as usize)
                        .ok_or_else(|| Signal::Panic(Panic { message: "internal: payload".into(), span })),
                    _ => panic(span, "internal: payload of the wrong variant"),
                }
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                let c = self.eval_bool(f, cond)?;
                self.exec_block(f, if c { then } else { else_ })
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let tag = match self.eval(f, scrutinee)? {
                    Value::Enum { tag, .. } => tag,
                    _ => return panic(span, "internal: switch on a non-enum"),
                };
                match arms.iter().find(|(t, _)| *t == tag) {
                    Some((_, b)) => self.exec_block(f, b),
                    None => match default {
                        Some(b) => self.exec_block(f, b),
                        None => panic(span, "internal: switch without a matching arm"),
                    },
                }
            }
            ExprKind::Block(b) => self.exec_block(f, b),
            ExprKind::Panic(msg) => panic(span, self.m.messages[msg.0 as usize].clone()),
        }
    }

    // ------------------------------------------------------------ numerics

    fn unary(&self, op: UnOp, v: Value, span: Span) -> R<Value> {
        Ok(match (op, v) {
            (UnOp::Neg, Value::F32(x)) => Value::F32(-x),
            (UnOp::Neg, Value::F64(x)) => Value::F64(-x),
            (UnOp::Neg, v) => {
                let (Some(k), Some(i)) = (v.int_kind(), v.to_i128()) else { return panic(span, "internal: neg") };
                let r = -i;
                if !in_range(k, r) {
                    return panic(span, format!("integer overflow in `-{i}`"));
                }
                int_value(k, r)
            }
            (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
            (UnOp::Not, v) => {
                let (Some(k), Some(i)) = (v.int_kind(), v.to_i128()) else { return panic(span, "internal: not") };
                int_value(k, wrap_int(k, !i))
            }
        })
    }

    fn binary(&self, op: BinOp, overflow: Overflow, a: Value, b: Value, span: Span) -> R<Value> {
        match (&a, &b) {
            (Value::F32(x), Value::F32(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F32(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => return panic(span, "internal: bit operation on a float"),
                }));
            }
            (Value::F64(x), Value::F64(y)) => {
                let (x, y) = (*x, *y);
                return Ok(Value::F64(match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => return panic(span, "internal: bit operation on a float"),
                }));
            }
            (Value::Bool(x), Value::Bool(y)) => {
                return Ok(Value::Bool(match op {
                    BinOp::BitAnd => *x & *y,
                    BinOp::BitOr => *x | *y,
                    BinOp::BitXor => *x ^ *y,
                    _ => return panic(span, "internal: arithmetic on Bool"),
                }));
            }
            _ => {}
        }
        let (Some(k), Some(x)) = (a.int_kind(), a.to_i128()) else { return panic(span, "internal: binary operand") };
        let Some(y) = b.to_i128() else { return panic(span, "internal: binary operand") };
        let bits = k.bits() as i128;
        let r = match op {
            BinOp::Add => x + y,
            BinOp::Sub => x - y,
            BinOp::Mul => x * y,
            BinOp::Div | BinOp::Rem => {
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let q = x / y;
                if !in_range(k, q) {
                    return panic(span, format!("integer overflow in `{x} / {y}`"));
                }
                if op == BinOp::Div { q } else { x % y }
            }
            BinOp::BitAnd => x & y,
            BinOp::BitOr => x | y,
            BinOp::BitXor => x ^ y,
            BinOp::Shl | BinOp::Shr => {
                if y < 0 || y >= bits {
                    return panic(span, format!("shift amount {y} is not below the bit width {bits}"));
                }
                if op == BinOp::Shl { wrap_int(k, x << y) } else { x >> y }
            }
        };
        let r = match (op, overflow) {
            (BinOp::Add | BinOp::Sub | BinOp::Mul, Overflow::Wrap) => wrap_int(k, r),
            (BinOp::Add | BinOp::Sub | BinOp::Mul, Overflow::Sat) => clamp_int(k, r),
            _ => {
                if !in_range(k, r) {
                    let sym = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        _ => "?",
                    };
                    return panic(span, format!("integer overflow in `{x} {sym} {y}` ({})", k.name()));
                }
                r
            }
        };
        Ok(int_value(k, r))
    }

    fn compare(&self, op: CmpOp, a: &Value, b: &Value, span: Span) -> R<bool> {
        use std::cmp::Ordering;
        let ord: Option<Ordering> = match (a, b) {
            (Value::F32(x), Value::F32(y)) => x.partial_cmp(y),
            (Value::F64(x), Value::F64(y)) => x.partial_cmp(y),
            (Value::Bool(x), Value::Bool(y)) => Some(x.cmp(y)),
            (Value::Char(x), Value::Char(y)) => Some(x.cmp(y)),
            (Value::Unit, Value::Unit) => Some(Ordering::Equal),
            _ => match (a.to_i128(), b.to_i128()) {
                (Some(x), Some(y)) => Some(x.cmp(&y)),
                _ => return panic(span, "internal: comparison operands"),
            },
        };
        Ok(match (op, ord) {
            (CmpOp::Eq, o) => o == Some(Ordering::Equal),
            (CmpOp::Ne, o) => o != Some(Ordering::Equal),
            (CmpOp::Lt, o) => o == Some(Ordering::Less),
            (CmpOp::Le, o) => matches!(o, Some(Ordering::Less | Ordering::Equal)),
            (CmpOp::Gt, o) => o == Some(Ordering::Greater),
            (CmpOp::Ge, o) => matches!(o, Some(Ordering::Greater | Ordering::Equal)),
        })
    }

    /// Lossless widening (§3.3).
    fn cast(&self, v: Value, to: &Ty, span: Span) -> R<Value> {
        Ok(match (v, to) {
            (Value::F32(x), Ty::Float(FloatKind::F64)) => Value::F64(x as f64),
            (Value::F32(x), Ty::Float(FloatKind::F32)) => Value::F32(x),
            (Value::F64(x), Ty::Float(FloatKind::F64)) => Value::F64(x),
            (v, Ty::Float(FloatKind::F32)) => match v.to_i128() {
                Some(i) => Value::F32(i as f32),
                None => return panic(span, "internal: cast operand"),
            },
            (v, Ty::Float(FloatKind::F64)) => match v.to_i128() {
                Some(i) => Value::F64(i as f64),
                None => return panic(span, "internal: cast operand"),
            },
            (v, Ty::Int(k)) => match v.to_i128() {
                Some(i) if in_range(*k, i) => int_value(*k, i),
                _ => return panic(span, "internal: cast out of range"),
            },
            _ => return panic(span, "internal: cast type"),
        })
    }

    // ------------------------------------------------------------ primitives

    fn prim(&self, f: &mut Frame, prim: &Prim, args: &[Arg], ty: &Ty, span: Span) -> R<Value> {
        // Sequence prims take their receiver as a sequence reference.
        match prim {
            Prim::Len => {
                let s = self.seq_of_arg(f, &args[0])?;
                return Ok(Value::U32(s.len));
            }
            Prim::Slice => {
                let s = self.seq_of_arg(f, &args[0])?;
                let from = self.eval_u32(f, &args[1].expr)?;
                let to = self.eval_u32(f, &args[2].expr)?;
                if from > to || to > s.len {
                    return panic(
                        span,
                        format!("slice {from}..{to} is out of range for a sequence of length {}", s.len),
                    );
                }
                return Ok(Value::Span(SpanRef {
                    root: s.root,
                    projs: s.projs,
                    start: s.start + from,
                    len: to - from,
                }));
            }
            Prim::Get => {
                let s = self.seq_of_arg(f, &args[0])?;
                let i = self.eval_u32(f, &args[1].expr)?;
                return Ok(if i < s.len { some(self.seq_get(&s, i, span)?) } else { none() });
            }
            Prim::Fill => {
                let s = self.seq_of_arg(f, &args[0])?;
                let v = self.eval(f, &args[1].expr)?;
                if let Value::F32(x) = v
                    && self.with_f32_slice(&s, |xs| xs.fill(x)).is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..s.len {
                    self.seq_set(&s, i, v.clone(), span)?;
                }
                return Ok(Value::Unit);
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let dst = self.seq_of_arg(f, &args[0])?;
                let src = self.seq_of_arg(f, &args[1])?;
                if dst.len != src.len {
                    return panic(span, format!("span lengths differ: {} and {}", dst.len, src.len));
                }
                let add = *prim == Prim::AddFrom;
                let src_vals: Option<Vec<f32>> = self.with_f32_slice(&src, |xs| xs.to_vec());
                if let Some(sv) = src_vals
                    && self
                        .with_f32_slice(&dst, |xs| {
                            for (d, s) in xs.iter_mut().zip(&sv) {
                                if add {
                                    *d += *s;
                                } else {
                                    *d = *s;
                                }
                            }
                        })
                        .is_some()
                {
                    return Ok(Value::Unit);
                }
                for i in 0..dst.len {
                    let sv = self.seq_get(&src, i, span)?;
                    let nv = if add {
                        self.binary(BinOp::Add, Overflow::Checked, self.seq_get(&dst, i, span)?, sv, span)?
                    } else {
                        sv
                    };
                    self.seq_set(&dst, i, nv, span)?;
                }
                return Ok(Value::Unit);
            }
            Prim::BufZeroed => {
                let n = self.eval_u32(f, &args[0].expr)?;
                let elem = match ty {
                    Ty::Buf(e) => (**e).clone(),
                    _ => return panic(span, "internal: Buf.zeroed type"),
                };
                return Ok(Value::Buf(slot(Value::Array(zero_array(self.m, &elem, n)))));
            }
            _ => {}
        }
        let mut vs = Vec::with_capacity(args.len());
        for a in args {
            vs.push(self.eval(f, &a.expr)?);
        }
        match prim {
            Prim::Math(mf, k) => self.math(*mf, *k, &vs, span),
            Prim::IntAbs(k) => {
                let x = vs[0].to_i128().unwrap_or(0);
                let r = x.abs();
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in `abs({x})`"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IntMin(k) => Ok(int_value(*k, vs[0].to_i128().unwrap_or(0).min(vs[1].to_i128().unwrap_or(0)))),
            Prim::IntMax(k) => Ok(int_value(*k, vs[0].to_i128().unwrap_or(0).max(vs[1].to_i128().unwrap_or(0)))),
            Prim::Narrow { to, .. } => {
                let x = vs[0].to_i128().unwrap_or(0);
                Ok(if in_range(*to, x) { some(int_value(*to, x)) } else { none() })
            }
            Prim::IntToFloat { to, .. } => {
                let x = vs[0].to_i128().unwrap_or(0);
                Ok(match to {
                    FloatKind::F32 => Value::F32(x as f32),
                    FloatKind::F64 => Value::F64(x as f64),
                })
            }
            Prim::FloatToFloat { to, .. } => Ok(match (&vs[0], to) {
                (Value::F64(x), FloatKind::F32) => Value::F32(*x as f32),
                (Value::F32(x), FloatKind::F64) => Value::F64(*x as f64),
                (v, _) => v.clone(),
            }),
            Prim::TruncToInt { to, sat, .. } => {
                let x = match &vs[0] {
                    Value::F32(x) => *x as f64,
                    Value::F64(x) => *x,
                    _ => return panic(span, "internal: trunc operand"),
                };
                let (lo, hi) = value::int_range(*to);
                if *sat {
                    // Rust `as` semantics: saturate, NaN -> 0.
                    let r = if x.is_nan() {
                        0
                    } else {
                        let t = x.trunc();
                        if t <= lo as f64 {
                            lo
                        } else if t >= hi as f64 {
                            hi
                        } else {
                            t as i128
                        }
                    };
                    Ok(int_value(*to, r))
                } else {
                    if x.is_nan() {
                        return panic(span, "conversion of NaN to an integer");
                    }
                    let t = x.trunc();
                    if t < lo as f64 || t > hi as f64 {
                        return panic(span, format!("{x:?} is out of range for {}", to.name()));
                    }
                    Ok(int_value(*to, t as i128))
                }
            }
            Prim::ToBits(_) => Ok(match &vs[0] {
                Value::F32(x) => Value::U32(x.to_bits()),
                Value::F64(x) => Value::U64(x.to_bits()),
                _ => return panic(span, "internal: to_bits operand"),
            }),
            Prim::FromBits(k) => Ok(match (k, &vs[0]) {
                (FloatKind::F32, Value::U32(b)) => Value::F32(f32::from_bits(*b)),
                (FloatKind::F64, Value::U64(b)) => Value::F64(f64::from_bits(*b)),
                _ => return panic(span, "internal: from_bits operand"),
            }),
            Prim::Checked(op, k) => {
                let (x, y) = (vs[0].to_i128().unwrap_or(0), vs[1].to_i128().unwrap_or(0));
                let r = match op {
                    CheckedOp::Add => Some(x + y),
                    CheckedOp::Sub => Some(x - y),
                    CheckedOp::Mul => Some(x * y),
                    CheckedOp::Div => (y != 0).then(|| x / y),
                };
                Ok(match r {
                    Some(r) if in_range(*k, r) => some(int_value(*k, r)),
                    _ => none(),
                })
            }
            Prim::DivEuclid(k) | Prim::RemEuclid(k) => {
                let (x, y) = (vs[0].to_i128().unwrap_or(0), vs[1].to_i128().unwrap_or(0));
                if y == 0 {
                    return panic(span, "division by zero");
                }
                let r = if matches!(prim, Prim::DivEuclid(_)) { x.div_euclid(y) } else { x.rem_euclid(y) };
                if !in_range(*k, r) {
                    return panic(span, format!("integer overflow in euclidean division of {x} by {y}"));
                }
                Ok(int_value(*k, r))
            }
            Prim::IsNan(_) => Ok(Value::Bool(match &vs[0] {
                Value::F32(x) => x.is_nan(),
                Value::F64(x) => x.is_nan(),
                _ => false,
            })),
            Prim::IsFinite(_) => Ok(Value::Bool(match &vs[0] {
                Value::F32(x) => x.is_finite(),
                Value::F64(x) => x.is_finite(),
                _ => false,
            })),
            Prim::Std(name) => self.std_prim(name, &vs, span),
            Prim::Len | Prim::Slice | Prim::Get | Prim::Fill | Prim::AddFrom | Prim::CopyFrom | Prim::BufZeroed => {
                unreachable!()
            }
        }
    }

    fn math(&self, mf: MathFn, k: FloatKind, vs: &[Value], span: Span) -> R<Value> {
        match k {
            FloatKind::F32 => {
                let x = vs[0]
                    .as_f32()
                    .ok_or_else(|| Signal::Panic(Panic { message: "internal: math operand".into(), span }))?;
                let y = vs.get(1).and_then(|v| v.as_f32()).unwrap_or(0.0);
                Ok(Value::F32(math_f32(mf, x, y)))
            }
            FloatKind::F64 => {
                let x = vs[0]
                    .as_f64()
                    .ok_or_else(|| Signal::Panic(Panic { message: "internal: math operand".into(), span }))?;
                let y = vs.get(1).and_then(|v| v.as_f64()).unwrap_or(0.0);
                Ok(Value::F64(math_f64(mf, x, y)))
            }
        }
    }

    /// `std` `target fn`s the interpreter implements directly.
    fn std_prim(&self, name: &str, vs: &[Value], span: Span) -> R<Value> {
        match name {
            "std.dsp.test.assert_near" => {
                let (a, b, tol) =
                    (vs[0].as_f64().unwrap_or(0.0), vs[1].as_f64().unwrap_or(0.0), vs[2].as_f64().unwrap_or(0.0));
                if (a - b).abs() <= tol {
                    Ok(Value::Unit)
                } else {
                    panic(span, format!("assert_near failed: {a:?} and {b:?} differ by more than {tol:?}"))
                }
            }
            _ => panic(span, format!("`{name}` is not available in this version of the interpreter")),
        }
    }
}

fn buf_len(b: &Slot) -> u32 {
    match &*b.borrow() {
        Value::Array(a) => a.len(),
        _ => 0,
    }
}

fn some(v: Value) -> Value {
    Value::Enum { tag: 1, fields: vec![v] }
}

fn none() -> Value {
    Value::Enum { tag: 0, fields: Vec::new() }
}

/// Round half to even (S-25).
fn round_even_f32(x: f32) -> f32 {
    x.round_ties_even()
}

fn round_even_f64(x: f64) -> f64 {
    x.round_ties_even()
}

/// `min` / `max` with NaN propagation and signed zeros ordered (S-25).
fn min_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() || b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a < b { a } else { b }
}

fn max_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    if a == 0.0 && b == 0.0 {
        return if a.is_sign_negative() && b.is_sign_negative() { -0.0 } else { 0.0 };
    }
    if a > b { a } else { b }
}

fn math_f32(mf: MathFn, x: f32, y: f32) -> f32 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f32(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x as f64, y as f64) as f32,
        MathFn::Max => max_f64(x as f64, y as f64) as f32,
        MathFn::Fmod => x % y,
    }
}

fn math_f64(mf: MathFn, x: f64, y: f64) -> f64 {
    match mf {
        MathFn::Exp => x.exp(),
        MathFn::Exp2 => x.exp2(),
        MathFn::Log => x.ln(),
        MathFn::Log2 => x.log2(),
        MathFn::Sin => x.sin(),
        MathFn::Cos => x.cos(),
        MathFn::Tan => x.tan(),
        MathFn::Tanh => x.tanh(),
        MathFn::Pow => x.powf(y),
        MathFn::Sqrt => x.sqrt(),
        MathFn::Floor => x.floor(),
        MathFn::Ceil => x.ceil(),
        MathFn::Trunc => x.trunc(),
        MathFn::Round => round_even_f64(x),
        MathFn::Abs => x.abs(),
        MathFn::Min => min_f64(x, y),
        MathFn::Max => max_f64(x, y),
        MathFn::Fmod => x % y,
    }
}

/// Type information for tools: the variant names of an enum type.
pub fn variant_names(m: &Module, ty: &Ty) -> Vec<String> {
    match ty {
        Ty::Enum(id) => match &m.ty(*id).kind {
            TypeDefKind::Enum { variants } => variants.iter().map(|(n, _)| n.clone()).collect(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// A fresh slot holding `v` (for callers that build `inout` state).
pub fn new_slot(v: Value) -> Slot {
    Rc::new(RefCell::new(v))
}

#[cfg(test)]
mod tests;
