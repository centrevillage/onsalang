//! AST (D-02): nodes live in arenas inside [`Ast`] and refer to each other by
//! id. Every node carries its [`Span`]. Binary expressions are kept as flat
//! operand/operator lists; operator groups (E0010) are checked after parsing.

use onsa_diag::Span;

macro_rules! id {
    ($name:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(ItemId);
id!(ExprId);
id!(StmtId);
id!(TypeId);
id!(PatId);

/// One parsed file.
#[derive(Debug, Default)]
pub struct Ast {
    pub items: Vec<Item>,
    pub exprs: Vec<Expr>,
    pub stmts: Vec<Stmt>,
    pub types: Vec<TypeExpr>,
    pub pats: Vec<Pat>,
    /// Top-level items in source order.
    pub root: Vec<ItemId>,
}

impl Ast {
    pub fn item(&self, id: ItemId) -> &Item {
        &self.items[id.index()]
    }
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.index()]
    }
    pub fn stmt(&self, id: StmtId) -> &Stmt {
        &self.stmts[id.index()]
    }
    pub fn ty(&self, id: TypeId) -> &TypeExpr {
        &self.types[id.index()]
    }
    pub fn pat(&self, id: PatId) -> &Pat {
        &self.pats[id.index()]
    }
    pub fn add_item(&mut self, item: Item) -> ItemId {
        self.items.push(item);
        ItemId(self.items.len() as u32 - 1)
    }
    pub fn add_expr(&mut self, expr: Expr) -> ExprId {
        self.exprs.push(expr);
        ExprId(self.exprs.len() as u32 - 1)
    }
    pub fn add_stmt(&mut self, stmt: Stmt) -> StmtId {
        self.stmts.push(stmt);
        StmtId(self.stmts.len() as u32 - 1)
    }
    pub fn add_type(&mut self, ty: TypeExpr) -> TypeId {
        self.types.push(ty);
        TypeId(self.types.len() as u32 - 1)
    }
    pub fn add_pat(&mut self, pat: Pat) -> PatId {
        self.pats.push(pat);
        PatId(self.pats.len() as u32 - 1)
    }
}

/// An identifier with its span. Names are not interned in M1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// `a.b.c`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

/// `"..."` with interpolation split out (§2.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrLit {
    pub segments: Vec<StrSeg>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrSeg {
    /// Literal text with escapes resolved.
    Text(String),
    /// `{name.field}`
    Interp(Path),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    /// Value and source text (`1_000`, `0xFF`). Values above `u64::MAX` are E0408 at parse time.
    Int {
        value: u64,
        text: String,
    },
    /// Source text; the value is parsed once the type is known.
    Float {
        text: String,
    },
    Char(char),
    Str(StrLit),
    Bool(bool),
}

/// Argument modes (§5.2). Also used on `self` and in function types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Borrow,
    Inout,
    Move,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vis {
    Private,
    /// `pub(pkg)`
    Pkg,
    /// `pub`
    Pub,
}

// ---------------------------------------------------------------- items

#[derive(Debug, Clone)]
pub struct Item {
    pub span: Span,
    /// Spans of the `///` lines directly before the item.
    pub doc: Vec<Span>,
    pub attrs: Vec<Attr>,
    pub vis: Vis,
    pub kind: ItemKind,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Fn(FnDecl),
    Flow(FlowDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    /// `type Name = Type`
    TypeAlias {
        name: Ident,
        ty: TypeId,
    },
    /// `type Name` inside `extern` or after `target` (opaque).
    OpaqueType {
        name: Ident,
    },
    Trait(TraitDecl),
    Impl(ImplDecl),
    Effect(EffectDecl),
    Handler(HandlerDecl),
    Const(ConstDecl),
    Use(UseDecl),
    Extern(ExternDecl),
    /// `target fn ...` / `target type ...` (§15.2). The inner item has no body.
    Target(Box<ItemKind>),
    /// `test "name" { ... }`
    Test {
        name: StrLit,
        body: ExprId,
    },
}

/// `@name(args)` (§6.5, §11.7)
#[derive(Debug, Clone)]
pub struct Attr {
    pub name: Ident,
    pub args: Vec<AttrArg>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AttrArg {
    /// `min: -60.0`
    Named { key: Ident, value: ExprId },
    /// `PartialEq`, `c`
    Path(Path),
    /// `"..."`
    Str(StrLit),
}

#[derive(Debug, Clone)]
pub struct FnDecl {
    pub rt: bool,
    pub name: Ident,
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    pub ret: Option<TypeId>,
    pub effects: Option<EffectRow>,
    /// `None` for signatures (trait, effect, extern, target).
    pub body: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub enum GenericParam {
    /// `T`, `T: PartialOrd`, `T: ?Dup`
    Type { name: Ident, bounds: Vec<Bound> },
    /// `const N: U32`
    Const { name: Ident, ty: TypeId },
    /// `e` (effect-row variable, snake_case)
    Effect { name: Ident },
}

#[derive(Debug, Clone)]
pub struct Bound {
    /// `?Dup`
    pub relaxed: bool,
    pub path: Path,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub attrs: Vec<Attr>,
    pub mode: Mode,
    pub name: ParamName,
    /// `None` only for `self` and for closure parameters without annotation.
    pub ty: Option<TypeId>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ParamName {
    Ident(Ident),
    /// `_`
    Wild(Span),
    /// `self`
    SelfParam(Span),
}

/// `uses {A, B}`
#[derive(Debug, Clone)]
pub struct EffectRow {
    pub effects: Vec<Path>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FlowDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: TypeId,
    pub body: ExprId,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Ident,
    pub generics: Vec<GenericParam>,
    pub kind: StructKind,
}

#[derive(Debug, Clone)]
pub enum StructKind {
    Named(Vec<Field>),
    /// `struct Hz(F32)` (newtype)
    Tuple(TypeId),
}

#[derive(Debug, Clone)]
pub struct Field {
    pub vis: Vis,
    pub name: Ident,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EnumDecl {
    pub name: Ident,
    pub generics: Vec<GenericParam>,
    pub variants: Vec<Variant>,
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub name: Ident,
    /// Empty for unit variants.
    pub fields: Vec<TypeId>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TraitDecl {
    pub name: Ident,
    pub generics: Vec<GenericParam>,
    /// `Fn` (with or without body) and `Const` items.
    pub items: Vec<ItemId>,
}

#[derive(Debug, Clone)]
pub struct ImplDecl {
    pub generics: Vec<GenericParam>,
    /// `impl Trait for Type`
    pub trait_: Option<Path>,
    pub self_ty: TypeId,
    pub items: Vec<ItemId>,
}

#[derive(Debug, Clone)]
pub struct EffectDecl {
    pub blocking: bool,
    pub name: Ident,
    /// `Fn` items without bodies.
    pub ops: Vec<ItemId>,
}

#[derive(Debug, Clone)]
pub struct HandlerDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub effect: Path,
    pub items: Vec<ItemId>,
}

#[derive(Debug, Clone)]
pub struct ConstDecl {
    pub name: Ident,
    pub ty: TypeId,
    /// `None` only inside `trait` (`const ZERO: Self`).
    pub value: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct UseDecl {
    pub path: Path,
    /// `use a.b.{x, y}`; `None` for `use a.b`.
    pub names: Option<Vec<Ident>>,
}

#[derive(Debug, Clone)]
pub struct ExternDecl {
    pub abi: StrLit,
    pub lib: StrLit,
    /// `OpaqueType` and `Fn` without body.
    pub items: Vec<ItemId>,
}

// ---------------------------------------------------------------- types

#[derive(Debug, Clone)]
pub struct TypeExpr {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// `F32`, `Sig[F32]`, `voice.State`, `Self`
    Path { path: Path, args: Vec<TypeId> },
    /// `[T; N]`
    Array { elem: TypeId, len: ExprId },
    /// `()`
    Unit,
    /// `(A, B)`
    Tuple(Vec<TypeId>),
    /// `rt fn(inout A, B) -> R uses {E}`
    Fn { rt: bool, params: Vec<(Mode, TypeId)>, ret: Option<TypeId>, effects: Option<EffectRow> },
}

// ---------------------------------------------------------------- statements

#[derive(Debug, Clone)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// `let pat[: T] = e`
    Let {
        pat: PatId,
        ty: Option<TypeId>,
        init: ExprId,
    },
    /// `var name[: T] = e`
    Var {
        name: Ident,
        ty: Option<TypeId>,
        init: ExprId,
    },
    /// `place = e`
    Assign {
        target: ExprId,
        value: ExprId,
    },
    /// `for pat in [move] iter { }`
    For {
        pat: PatId,
        moved: bool,
        iter: ExprId,
        body: ExprId,
    },
    While {
        cond: ExprId,
        body: ExprId,
    },
    Break,
    Continue,
    Return(Option<ExprId>),
    Assert(ExprId),
    Expr(ExprId),
}

// ---------------------------------------------------------------- expressions

#[derive(Debug, Clone)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    WrapAdd,
    WrapSub,
    WrapMul,
    SatAdd,
    SatSub,
    SatMul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Operator groups (§3.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpGroup {
    Additive,
    Multiplicative,
    Comparison,
    And,
    Or,
    Bitwise,
}

impl BinOp {
    pub fn group(self) -> OpGroup {
        use BinOp::*;
        match self {
            Add | Sub | WrapAdd | WrapSub | SatAdd | SatSub => OpGroup::Additive,
            Mul | Div | Rem | WrapMul | SatMul => OpGroup::Multiplicative,
            Eq | Ne | Lt | Le | Gt | Ge => OpGroup::Comparison,
            And => OpGroup::And,
            Or => OpGroup::Or,
            BitAnd | BitOr | BitXor | Shl | Shr => OpGroup::Bitwise,
        }
    }

    /// Whether `a op b op c` is allowed within the group (§3.1 table).
    pub fn chains(self) -> bool {
        !matches!(self.group(), OpGroup::Comparison | OpGroup::Bitwise)
    }

    pub fn symbol(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            WrapAdd => "+%",
            WrapSub => "-%",
            WrapMul => "*%",
            SatAdd => "+|",
            SatSub => "-|",
            SatMul => "*|",
            Eq => "==",
            Ne => "!=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
            And => "&&",
            Or => "||",
            BitAnd => "&",
            BitOr => "|",
            BitXor => "^",
            Shl => "<<",
            Shr => ">>",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// `-`
    Neg,
    /// `!` (logical not on `Bool`, bitwise not on integers)
    Not,
}

/// Kind of call (§2.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallKind {
    /// `f(x)`
    Plain,
    /// `f~(x)`: flow instance
    Flow,
    /// `x.f!(y)`: `inout self` method
    Bang,
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub mode: Mode,
    pub expr: ExprId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<StmtId>,
    /// The value of the block (last expression without a newline after it).
    pub tail: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    /// `x`, `a.b.C`, `Type.CONST`, `Some`
    Path(Path),
    /// `_` (typed hole, §18.1)
    Hole,
    /// `(e)`
    Paren(ExprId),
    /// `(a, b)`
    Tuple(Vec<ExprId>),
    /// `[a, b]`
    Array(Vec<ExprId>),
    /// `[e; N]`
    Repeat {
        elem: ExprId,
        len: ExprId,
    },
    /// `Point { x: 1.0, y: 2.0 }`
    Struct {
        path: Path,
        fields: Vec<(Ident, ExprId)>,
    },
    Block(Block),
    /// `if c { a } else { b }`; `else if` nests another `If` in `else_`.
    If {
        cond: ExprId,
        then: ExprId,
        else_: Option<ExprId>,
    },
    Match {
        scrutinee: ExprId,
        arms: Vec<MatchArm>,
    },
    /// `fn(x: F32) -> F32 { ... }` (anonymous function)
    Closure {
        params: Vec<Param>,
        ret: Option<TypeId>,
        effects: Option<EffectRow>,
        body: ExprId,
    },
    /// `handle { ... } with h(args)` / `with Fs { fn read(...) {...} }`
    Handle {
        body: ExprId,
        with: HandlerRef,
    },
    /// `unsafe { ... }`
    Unsafe(ExprId),
    /// `par i in a..b { ... }`
    Par {
        var: Ident,
        from: ExprId,
        to: ExprId,
        body: ExprId,
    },
    /// Flat chain `operands[0] ops[0] operands[1] ops[1] ...` (groups checked later).
    Binary {
        operands: Vec<ExprId>,
        ops: Vec<(BinOp, Span)>,
    },
    /// `e as T`
    Cast {
        expr: ExprId,
        ty: TypeId,
    },
    Unary {
        op: UnOp,
        expr: ExprId,
    },
    /// `f(args)`, `f~(args)`, `x.f!(args)`
    Call {
        callee: ExprId,
        kind: CallKind,
        args: Vec<Arg>,
    },
    /// `e.name`
    Field {
        base: ExprId,
        name: Ident,
    },
    /// `e.0`
    TupleIndex {
        base: ExprId,
        index: u32,
        index_span: Span,
    },
    /// `e[i]`
    Index {
        base: ExprId,
        index: ExprId,
    },
    /// `e?`
    Try(ExprId),
    /// `a..b` (only in `for` / `par` heads)
    Range {
        lo: ExprId,
        hi: ExprId,
    },
}

#[derive(Debug, Clone)]
pub enum HandlerRef {
    /// `with memory_fs`, `with arena(inout scratch)`
    Named { path: Path, args: Vec<Arg> },
    /// `with Fs { fn read(...) { ... } }`
    Inline { effect: Path, items: Vec<ItemId> },
}

// ---------------------------------------------------------------- patterns

#[derive(Debug, Clone)]
pub struct Pat {
    pub span: Span,
    pub kind: PatKind,
}

#[derive(Debug, Clone)]
pub enum PatKind {
    /// `_`
    Wild,
    /// `x` (binding) — a lone lowercase identifier
    Bind(Ident),
    Lit(Lit),
    /// `-1` (a negated integer literal)
    Neg(Lit),
    /// `None`, `Shape.Circle`, `Type.CONST`
    Path(Path),
    /// `Some(p)`, `Shape.Rect(a, b)`
    TupleStruct {
        path: Path,
        elems: Vec<PatId>,
    },
    /// `(p, q)`
    Tuple(Vec<PatId>),
    /// `Point { x: px, y: py }`
    Struct {
        path: Path,
        fields: Vec<(Ident, PatId)>,
    },
    /// `p | q`
    Or(Vec<PatId>),
}
