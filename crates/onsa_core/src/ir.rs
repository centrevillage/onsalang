//! Onsa Core IR (`design/04-core.md`, D-03): the checked,
//! typed, monomorphic, canonical form every backend consumes.
//!
//! - Every function is monomorphic; instances are named `clamp__F32`.
//! - Nothing is implicit: operators are typed instructions with an overflow
//!   mode, every index is bounds-checked, enum matches are `Switch`es on tags.
//! - Control flow is structured (`If`, `While`, `ForRange`, `Switch`).
//! - Aggregates (arrays, tuples, structs, enums) are values; functions
//!   returning one are marked `sret` (spec §12.7).
//! - Flows are lowered to ordinary functions (`lower::flow`, D-03); the
//!   module keeps per-flow metadata in [`Module::flows`].

use std::collections::HashMap;

use onsa_diag::Span;
use onsa_sema::DefId;
pub use onsa_sema::ty::{FloatKind, IntKind};

use crate::prim::Prim;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MsgId(pub u32);

/// Where a [`ExprKind::Panic`] comes from: a failed `assert` or another
/// panic. The message cannot tell them apart (§18.1 promises `assert
/// <source>` and the `msg` of `panic(msg)`, and messages are shared by text).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PanicOrigin {
    Assert,
    Panic,
}

impl PanicOrigin {
    /// The `kind` of a failure of `onsa test --json` (§18.1, S-554).
    pub fn kind(self) -> &'static str {
        match self {
            PanicOrigin::Assert => "assert",
            PanicOrigin::Panic => "panic",
        }
    }
}

/// A concrete type: an index into the table of its module ([`Module::tys`]).
/// Two types of one module are the same exactly when their ids are, so that
/// comparing, hashing and copying one is O(1). Only [`Types`] makes one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CTy(u32);

impl CTy {
    /// The position in the table: the ids of the parts of a type are smaller.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// What a type is, one level deep: the parts are ids. Structs and enums
/// refer to `Module::types`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Int(IntKind),
    Float(FloatKind),
    Bool,
    Char,
    Unit,
    Array(CTy, u32),
    Tuple(Box<[CTy]>),
    Struct(TypeId),
    Enum(TypeId),
    /// Second-class view (§5.3); only in parameters and temporaries.
    Span(CTy),
    /// Function pointer (captureless function value, §5.3).
    FnPtr(Box<FnSig>),
    /// Heap buffer; interpreter only in phase 1 (D-08).
    Buf(CTy),
}

impl TyKind {
    /// The parts of a form, in the order of `lower::limits::part_mut`.
    pub fn parts(&self) -> impl Iterator<Item = CTy> + '_ {
        let (one, many, params, ret): (_, &[CTy], &[(Mode, CTy)], _) = match self {
            TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e) => (Some(*e), &[], &[], None),
            TyKind::Tuple(ts) => (None, ts, &[], None),
            TyKind::FnPtr(f) => (None, &[], &f.params, Some(f.ret)),
            _ => (None, &[], &[], None),
        };
        one.into_iter().chain(many.iter().copied()).chain(params.iter().map(|&(_, t)| t)).chain(ret)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnSig {
    pub rt: bool,
    pub params: Vec<(Mode, CTy)>,
    pub ret: CTy,
}

/// The built-in types, at the ids of their positions (the constants of [`Types`]).
static BUILTINS: [TyKind; 13] = [
    TyKind::Int(IntKind::I8),
    TyKind::Int(IntKind::I16),
    TyKind::Int(IntKind::I32),
    TyKind::Int(IntKind::I64),
    TyKind::Int(IntKind::U8),
    TyKind::Int(IntKind::U16),
    TyKind::Int(IntKind::U32),
    TyKind::Int(IntKind::U64),
    TyKind::Float(FloatKind::F32),
    TyKind::Float(FloatKind::F64),
    TyKind::Bool,
    TyKind::Char,
    TyKind::Unit,
];

/// The types of a module, each kind once (interned). Lowering adds to it;
/// what reads a module after lowering only reads it.
#[derive(Debug, Clone)]
pub struct Types {
    kinds: Vec<TyKind>,
    ids: HashMap<TyKind, CTy>,
}

impl Default for Types {
    /// The table of the built-in types alone.
    fn default() -> Self {
        Types { kinds: BUILTINS.to_vec(), ids: HashMap::new() }
    }
}

impl Types {
    pub const U32: CTy = Types::int(IntKind::U32);
    pub const BOOL: CTy = CTy(10);
    pub const CHAR: CTy = CTy(11);
    pub const UNIT: CTy = CTy(12);

    /// The built-in integer type of `k`.
    pub const fn int(k: IntKind) -> CTy {
        CTy(k as u32)
    }

    /// The built-in floating-point type of `k`.
    pub const fn float(k: FloatKind) -> CTy {
        CTy(8 + k as u32)
    }

    /// The kind of `t` if it is a built-in type, which every table has at
    /// the same id.
    pub fn builtin(t: CTy) -> Option<&'static TyKind> {
        BUILTINS.get(t.index())
    }

    pub fn kind(&self, t: CTy) -> &TyKind {
        &self.kinds[t.index()]
    }

    /// The id of `k` if the table has it. A built-in type is at its fixed
    /// id, with no look-up (the most made of all).
    pub(crate) fn find(&self, k: &TyKind) -> Option<CTy> {
        Some(match *k {
            TyKind::Int(k) => Types::int(k),
            TyKind::Float(k) => Types::float(k),
            TyKind::Bool => Types::BOOL,
            TyKind::Char => Types::CHAR,
            TyKind::Unit => Types::UNIT,
            _ => return self.ids.get(k).copied(),
        })
    }

    /// The id of `k`: the one it has, or a new one at the end.
    pub fn intern(&mut self, k: TyKind) -> CTy {
        if let Some(t) = self.find(&k) {
            return t;
        }
        let t = CTy(self.kinds.len() as u32);
        self.kinds.push(k.clone());
        self.ids.insert(k, t);
        t
    }

    /// The kinds of every type, in the order of their ids.
    pub fn kinds(&self) -> &[TyKind] {
        &self.kinds
    }

    /// Every type, in the order of the ids.
    pub fn ids(&self) -> impl Iterator<Item = CTy> + use<> {
        (0..self.kinds.len() as u32).map(CTy)
    }

    pub fn is_aggregate(&self, t: CTy) -> bool {
        matches!(self.kind(t), TyKind::Array(..) | TyKind::Tuple(_) | TyKind::Struct(_) | TyKind::Enum(_))
    }

    pub fn is_int(&self, t: CTy) -> bool {
        matches!(self.kind(t), TyKind::Int(_))
    }

    pub fn is_float(&self, t: CTy) -> bool {
        matches!(self.kind(t), TyKind::Float(_))
    }

    pub fn is_scalar(&self, t: CTy) -> bool {
        matches!(self.kind(t), TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char)
    }

    /// Whether `t` is a planar array `[Span[T]; N]` (§5.3).
    pub fn is_planar(&self, t: CTy) -> bool {
        matches!(*self.kind(t), TyKind::Array(el, _) if matches!(self.kind(el), TyKind::Span(_)))
    }
}

/// Argument modes (§5.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Borrow,
    Inout,
    Move,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    /// `dsp.Point`, `std.core.Option__F32`, `Ring__F32__4`.
    pub name: String,
    pub kind: TypeDefKind,
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    Struct {
        fields: Vec<(String, CTy)>,
    },
    Enum {
        variants: Vec<(String, Vec<CTy>)>,
    },
    /// Fields not known (`target` / `extern` opaque types).
    Opaque,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
    pub name: String,
    pub ty: CTy,
    /// Literal / aggregate initializer, or an expression the interpreter
    /// evaluates at build time (T3-9).
    pub init: Expr,
}

#[derive(Debug, Clone)]
pub struct Local {
    pub name: String,
    pub ty: CTy,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub local: LocalId,
    pub mode: Mode,
    pub ty: CTy,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    /// `dsp.voice.wrap01`, `test.gcd`, `clamp__F32`.
    pub name: String,
    pub params: Vec<Param>,
    pub ret: CTy,
    /// The result is an aggregate built in the caller's slot (§12.7).
    pub sret: bool,
    pub rt: bool,
    pub locals: Vec<Local>,
    /// `None`: declared only (`target` functions the backend provides).
    pub body: Option<Block>,
    pub span: Span,
    /// `@fp(relaxed)` (§15.5, S-287): the floating-point operations of a call of
    /// it may be contracted and reassociated, a permission a backend may leave
    /// unused (the interpreter does).
    pub fp_relaxed: bool,
    /// The function of a `test` block: what identifies the test (spec
    /// §11.8, S-55, R-68). `onsa test` runs the functions with this mark;
    /// the name of the function decides nothing.
    pub test: Option<TestMark>,
    /// The declaration this function is an instance of, which a diagnostic
    /// names (§18.1). `None`: only lowering makes it (`__eq`, what a flow
    /// generates). No later stage reads it.
    pub decl: Option<DefId>,
    /// The locals declared in a scope whose storage a view out of it reads,
    /// stored at the function's level (R-481, `lower::storage`), ascending.
    pub hoisted: Vec<LocalId>,
}

/// The mark of the function of a `test` block (spec §11.8, S-55): a test is
/// identified by the path of its module and its name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestMark {
    /// The module path (`dsp.voice`; the file name for a single file).
    pub module: String,
    /// The value of the name (the literal with its escapes read, S-244).
    pub name: String,
}

impl TestMark {
    /// The full name text (spec §11.8): the module path, one space, and the
    /// name written as an Onsa string literal (`dsp.voice "decays"`). What
    /// the result lines show and `onsa test --filter` matches.
    pub fn full_name(&self) -> String {
        format!("{} {}", self.module, onsa_syntax::test_name::quote(&self.name))
    }
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    /// The types every id of the module refers to.
    pub tys: Types,
    pub types: Vec<TypeDef>,
    pub consts: Vec<ConstDef>,
    pub fns: Vec<FnDef>,
    /// Panic messages, by `MsgId`.
    pub messages: Vec<String>,
    /// Flows of the user package: generated functions, layout, parameters.
    pub flows: Vec<crate::lower::flow::FlowMeta>,
    /// Places where an aggregate value is copied (§12.7; `onsa audit --memory`, T4-9).
    pub moves: Vec<MoveSite>,
    /// What is known of each type, at the pointer width of the target
    /// ([`Module::facts`]): filled by lowering.
    pub facts: crate::layout::Facts,
}

/// Why an aggregate is copied (§12.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MoveKind {
    /// `let y = x` / `p = x` from another place (an owned local, a field, an element).
    Copy,
    /// `if c { a } else { b }` / `match` arms that yield existing places (no NRVO).
    Branch,
    /// Extraction of a payload from `Option` / `Result` / an enum.
    Payload,
    /// An aggregate passed as a `move` argument (the callee owns a copy).
    MoveArg,
}

/// One copy of an aggregate value, with its size on the target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MoveSite {
    pub fn_: FnId,
    pub span: onsa_diag::Span,
    pub ty: CTy,
    pub bytes: u32,
    pub kind: MoveKind,
}

impl Module {
    pub fn ty(&self, id: TypeId) -> &TypeDef {
        &self.types[id.0 as usize]
    }
    pub fn fn_(&self, id: FnId) -> &FnDef {
        &self.fns[id.0 as usize]
    }
    pub fn const_(&self, id: ConstId) -> &ConstDef {
        &self.consts[id.0 as usize]
    }
    /// The flow (its index in `flows`) whose generated function `f` is.
    pub fn flow_of(&self, f: FnId) -> Option<usize> {
        self.flows.iter().position(|flow| flow.fns.generated().any(|g| g == f))
    }
}

/// A statement list with an optional value (used by `If`, `Switch`, `Block`).
#[derive(Debug, Clone, Default)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub value: Option<Box<Expr>>,
}

impl Block {
    /// The block ends in `return` / `break` / `continue`.
    pub fn diverges(&self) -> bool {
        self.stmts.last().is_some_and(|s| matches!(s.kind, StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue))
    }
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Let(LocalId, Expr),
    /// `place = value`. From the source, the statement's span is the target
    /// (`xs[i]`): the position of a panic of the write (§18.1, R-185).
    Assign(Place, Expr),
    Expr(Expr),
    If(Expr, Block, Block),
    While(Expr, Block),
    /// `for local in lo..<hi`, or `lo..=hi` when `inclusive` (any integer
    /// type): `lo`, then `hi`, once before the loop (S-188); no iteration
    /// when `lo >= hi` (`..<`) or `lo > hi` (`..=`, S-219), and none past a
    /// `hi` that is the type's maximum (S-257).
    ForRange {
        local: LocalId,
        lo: Expr,
        hi: Expr,
        body: Block,
        inclusive: bool,
    },
    Break,
    Continue,
    Return(Option<Expr>),
}

impl StmtKind {
    /// `for local in lo..<hi`: the loops the lowering makes.
    pub fn for_excluded(local: LocalId, lo: Expr, hi: Expr, body: Block) -> StmtKind {
        StmtKind::ForRange { local, lo, hi, body, inclusive: false }
    }
}

/// A memory location: a local, or a field / element of one.
#[derive(Debug, Clone)]
pub enum Place {
    Local(LocalId),
    Field(Box<Place>, u32),
    /// `base[index]`, with the position of the whole element (`xs[i]`): where
    /// its index out of range panics (§18.1, R-188).
    Index(Box<Place>, Box<Expr>, Span, Bounds),
}

/// Whether an index is checked against the length of its sequence (§18.1),
/// or known in range: the inputs and outputs of the sample loop of
/// `process`, whose lengths it compared before the loop (S-196), and the
/// constant channels of a planar `[Span; N]` there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bounds {
    Checked,
    Known,
}

impl Place {
    pub fn root(&self) -> LocalId {
        match self {
            Place::Local(l) => *l,
            Place::Field(p, _) | Place::Index(p, ..) => p.root(),
        }
    }
}

impl Expr {
    /// The local at the root of an expression that is a place
    /// ([`Expr::as_place`], then [`Place::root`]), with no place made.
    pub fn place_root(&self) -> Option<LocalId> {
        match &self.kind {
            ExprKind::Local(l) => Some(*l),
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => base.place_root(),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// `-`: checked on signed integers, plain on floats.
    Neg,
    /// `!`: logical not on `Bool`, bitwise not on integers.
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Integer overflow behavior (§3.4). Floats are always IEEE; the field is
/// `Checked` on them and means nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Overflow {
    /// Panic on overflow, division by zero, `MIN / -1`, shift >= bits.
    Checked,
    /// Two's complement wraparound (`+% -% *%`).
    Wrap,
    /// Saturate at the type's range (`+| -| *|`).
    Sat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicOp {
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    /// Value fits the expression's integer type.
    Int(i128),
    /// Parsed directly from the source text as `f32` (no double rounding).
    F32(f32),
    F64(f64),
    Bool(bool),
    Char(char),
    Unit,
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub mode: Mode,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub ty: CTy,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    Local(LocalId),
    Const(ConstId),
    /// A zero-initialized value of the expression's type (array construction).
    Zeroed,
    Unary(UnOp, Box<Expr>),
    /// Both operands have the expression's numeric type (shifts: rhs is `U32`).
    Binary {
        op: BinOp,
        overflow: Overflow,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Scalar comparison; operands share one type. Aggregates use generated `eq` functions.
    Cmp {
        op: CmpOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Short-circuit `&&` / `||`.
    Logic {
        op: LogicOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Lossless widening `as` to the expression's type (§3.3).
    Cast(Box<Expr>),
    Call {
        fn_: FnId,
        args: Vec<Arg>,
    },
    /// A primitive the backend provides (`prim.rs`).
    Prim {
        prim: Prim,
        args: Vec<Arg>,
    },
    /// Struct field or tuple element by position.
    Field {
        base: Box<Expr>,
        index: u32,
    },
    /// Element of an array / `Span` / `Buf`; the index is `U32`.
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
        bounds: Bounds,
    },
    /// A `Span` over an array or `Buf` place.
    SpanOf(Box<Expr>),
    /// Each field once (V-01): its number in the declaration and its value,
    /// in the order of evaluation, that of the source (§3.5), the fields it
    /// does not write after.
    Struct {
        ty: TypeId,
        fields: Vec<(u32, Expr)>,
    },
    Variant {
        ty: TypeId,
        tag: u32,
        fields: Vec<Expr>,
    },
    Array(Vec<Expr>),
    Repeat {
        elem: Box<Expr>,
        n: u32,
    },
    Tuple(Vec<Expr>),
    /// The tag of an enum value (its type is the tag integer).
    Tag(Box<Expr>),
    /// Field `index` of variant `tag` of an enum value (the tag must match).
    Payload {
        base: Box<Expr>,
        tag: u32,
        index: u32,
    },
    IfExpr {
        cond: Box<Expr>,
        then: Block,
        else_: Block,
    },
    /// Switch on the tag of an enum; every tag is covered or `default` is present.
    Switch {
        scrutinee: Box<Expr>,
        arms: Vec<(u32, Block)>,
        default: Option<Block>,
    },
    Block(Block),
    /// Abort (§9.2); has whatever type the context needs.
    Panic {
        msg: MsgId,
        origin: PanicOrigin,
        /// Of a failed `assert` of a comparison whose operands have `Show`
        /// (§18.1, S-1261), the two values compared, each a read with no
        /// effect; else empty. Only the interpreter evaluates them.
        shown: Vec<Expr>,
    },
}

impl Expr {
    pub fn new(ty: CTy, span: Span, kind: ExprKind) -> Expr {
        Expr { ty, span, kind }
    }

    /// The place this expression denotes, if it is one.
    pub fn as_place(&self) -> Option<Place> {
        match &self.kind {
            ExprKind::Local(l) => Some(Place::Local(*l)),
            ExprKind::Field { base, index } => Some(Place::Field(Box::new(base.as_place()?), *index)),
            ExprKind::Index { base, index, bounds } => {
                Some(Place::Index(Box::new(base.as_place()?), index.clone(), self.span, *bounds))
            }
            _ => None,
        }
    }
}
