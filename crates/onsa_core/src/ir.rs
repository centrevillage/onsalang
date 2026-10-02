//! Onsa Core IR (docs/implementation-tasks.md §3.4, D-03): the checked,
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

use onsa_diag::Span;
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

/// A concrete type. Structs and enums refer to `Module::types`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Int(IntKind),
    Float(FloatKind),
    Bool,
    Char,
    Unit,
    Array(Box<Ty>, u32),
    Tuple(Vec<Ty>),
    Struct(TypeId),
    Enum(TypeId),
    /// Second-class view (§5.3); only in parameters and temporaries.
    Span(Box<Ty>),
    /// Function pointer (captureless function value, §5.3).
    FnPtr(Box<FnSig>),
    /// Heap buffer; interpreter only in phase 1 (D-08).
    Buf(Box<Ty>),
}

impl Ty {
    pub fn is_aggregate(&self) -> bool {
        matches!(self, Ty::Array(..) | Ty::Tuple(_) | Ty::Struct(_) | Ty::Enum(_))
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Ty::Int(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Ty::Float(_))
    }

    pub fn is_scalar(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char)
    }

    pub fn u32() -> Ty {
        Ty::Int(IntKind::U32)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnSig {
    pub rt: bool,
    pub params: Vec<(Mode, Ty)>,
    pub ret: Ty,
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
    /// `dsp.Point`, `Option__F32`, `Ring__F32__4`.
    pub name: String,
    pub kind: TypeDefKind,
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    Struct {
        fields: Vec<(String, Ty)>,
    },
    Enum {
        variants: Vec<(String, Vec<Ty>)>,
    },
    /// Fields not known (`target` / `extern` opaque types).
    Opaque,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
    pub name: String,
    pub ty: Ty,
    /// Literal / aggregate initializer, or an expression the interpreter
    /// evaluates at build time (T3-9).
    pub init: Expr,
}

#[derive(Debug, Clone)]
pub struct Local {
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub local: LocalId,
    pub mode: Mode,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    /// `dsp.voice.wrap01`, `test.gcd`, `clamp__F32`.
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Ty,
    /// The result is an aggregate built in the caller's slot (§12.7).
    pub sret: bool,
    pub rt: bool,
    pub locals: Vec<Local>,
    /// `None`: declared only (`target` functions the backend provides).
    pub body: Option<Block>,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub types: Vec<TypeDef>,
    pub consts: Vec<ConstDef>,
    pub fns: Vec<FnDef>,
    /// Panic messages, by `MsgId`.
    pub messages: Vec<String>,
    /// Flows of the user package: generated functions, layout, parameters.
    pub flows: Vec<crate::lower::flow::FlowMeta>,
    /// Places where an aggregate value is copied (§12.7; `onsa audit --memory`, T4-9).
    pub moves: Vec<MoveSite>,
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

/// One copy of an aggregate value, with its size on the reference host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MoveSite {
    pub fn_name: String,
    pub span: onsa_diag::Span,
    pub ty: Ty,
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
    Assign(Place, Expr),
    Expr(Expr),
    If(Expr, Block, Block),
    While(Expr, Block),
    /// `for local in lo..hi` (half-open, `U32` or any integer type).
    ForRange(LocalId, Expr, Expr, Block),
    Break,
    Continue,
    Return(Option<Expr>),
}

/// A memory location: a local, or a field / element of one.
#[derive(Debug, Clone)]
pub enum Place {
    Local(LocalId),
    Field(Box<Place>, u32),
    Index(Box<Place>, Box<Expr>),
}

impl Place {
    pub fn root(&self) -> LocalId {
        match self {
            Place::Local(l) => *l,
            Place::Field(p, _) | Place::Index(p, _) => p.root(),
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
    pub ty: Ty,
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
    /// Bounds-checked element of an array / `Span` / `Buf`; the index is `U32`.
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    /// A `Span` over an array or `Buf` place.
    SpanOf(Box<Expr>),
    Struct {
        ty: TypeId,
        fields: Vec<Expr>,
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
    Panic(MsgId),
}

impl Expr {
    pub fn new(ty: Ty, span: Span, kind: ExprKind) -> Expr {
        Expr { ty, span, kind }
    }

    /// The place this expression denotes, if it is one.
    pub fn as_place(&self) -> Option<Place> {
        match &self.kind {
            ExprKind::Local(l) => Some(Place::Local(*l)),
            ExprKind::Field { base, index } => Some(Place::Field(Box::new(base.as_place()?), *index)),
            ExprKind::Index { base, index } => Some(Place::Index(Box::new(base.as_place()?), index.clone())),
            _ => None,
        }
    }
}
