//! AST (D-02): nodes live in arenas inside [`Ast`] and refer to each other by
//! id. Every node carries its [`Span`]. A chain of binary operators is the
//! tree of §3.1 ([`Chain`], made once when the AST is made from the CST);
//! its operator groups (E0010) are checked after parsing.

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
#[derive(Debug, Default, Clone)]
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

    /// The operand of `e` when `e` is an `as` or an `at` expression (`x as T`,
    /// `x at k`): the forms of one strength between the prefix and the binary
    /// operators (§3.1), which are parenthesized as an operand of a binary
    /// operator and are not chained (E0011, S-118). The one judgment of
    /// those forms on the tree ([`Operand::AsAt`] of the written text).
    pub fn as_or_at_operand(&self, e: ExprId) -> Option<ExprId> {
        match self.expr(e).kind {
            ExprKind::Cast { expr, .. } | ExprKind::At { expr, .. } => Some(expr),
            _ => None,
        }
    }

    /// `e` without the parentheses around it (`((x))` is `x`; §3.1: a
    /// parenthesis only groups). The one walk through them on the tree.
    pub fn without_parens(&self, mut e: ExprId) -> ExprId {
        while let ExprKind::Paren(inner) = self.expr(e).kind {
            e = inner;
        }
        e
    }

    /// The literal of a negative literal (spec §4.7, S-184, S-227): `e` is a prefix
    /// `-` whose operand, without its parentheses, is a numeric literal itself
    /// (`-1`, `-(128)`, `-((1.5))`). The `-` is then a part of the literal's
    /// value; any other `-` (`-(-1)` outside, `-x`, `-(I32.MIN)`) negates a value.
    /// The one definition of the rule for expressions; the patterns have the same
    /// form in their grammar (`NegLitPat`).
    pub fn negated_literal(&self, e: ExprId) -> Option<ExprId> {
        let ExprKind::Unary { op: UnOp::Neg, expr } = &self.expr(e).kind else { return None };
        let cur = self.without_parens(*expr);
        match &self.expr(cur).kind {
            ExprKind::Lit(Lit::Int { .. } | Lit::Float { .. }) => Some(cur),
            _ => None,
        }
    }

    /// The name at the root of the place `e` (§5.1, §5.2): a name alone (`a`,
    /// `self`), or a field, an element or a tuple element of a place, through
    /// parentheses (`a.f`, `a[i]`, `a.0`, `(a).f`); `None` for any other
    /// expression (a call, the result of a method, a literal, a path of more
    /// than one name). The one definition of the form of a place (`check`'s
    /// E0711 of `move` and the target of an assignment): whether the name is a
    /// local the names stage decides.
    pub fn place_root(&self, e: ExprId) -> Option<&str> {
        match &self.expr(e).kind {
            ExprKind::Path(p) if p.segments.len() == 1 => Some(p.segments[0].name.as_str()),
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } | ExprKind::TupleIndex { base, .. } => {
                self.place_root(*base)
            }
            ExprKind::Paren(inner) => self.place_root(*inner),
            _ => None,
        }
    }

    /// The direct sub-expressions of `e` in source order: every one, the
    /// expressions of the statements of a block, a callee, the base of a
    /// field, the length of `[x; N]`, the bounds of a `par` and the body of a
    /// closure or a `handle` included. The one plain enumeration of the
    /// children of an expression (R-91 (1)); a walk that treats some of them
    /// apart matches those in arms of its own before it calls this (the
    /// state marking of a flow, `onsa graph`). `^y` has none (it reads the
    /// local `y`), nor has `Error`: whether meeting one is a bug is the
    /// caller's to decide.
    pub fn sub_exprs(&self, e: ExprId) -> Vec<ExprId> {
        let mut out = Vec::new();
        match &self.expr(e).kind {
            ExprKind::Error | ExprKind::Lit(_) | ExprKind::Path(_) | ExprKind::Hole | ExprKind::Feedback(_) => {}
            ExprKind::Paren(x)
            | ExprKind::At { expr: x, .. }
            | ExprKind::Unary { expr: x, .. }
            | ExprKind::Cast { expr: x, .. }
            | ExprKind::Try(x)
            | ExprKind::Move(x)
            | ExprKind::Field { base: x, .. }
            | ExprKind::TupleIndex { base: x, .. }
            | ExprKind::TypeArgs { base: x, .. }
            | ExprKind::Unsafe(x) => out.push(*x),
            ExprKind::Tuple(xs) | ExprKind::Array(xs) => out.extend(xs.iter().copied()),
            ExprKind::Repeat { elem, len } => out.extend([*elem, *len]),
            ExprKind::Struct { fields, .. } => out.extend(fields.iter().map(|(_, x)| *x)),
            ExprKind::Block(b) => {
                for &s in &b.stmts {
                    match &self.stmt(s).kind {
                        StmtKind::Let { init, .. } | StmtKind::Var { init, .. } => out.push(*init),
                        StmtKind::Assign { target, value } => out.extend([*target, *value]),
                        StmtKind::For { iter, body, .. } => out.extend([*iter, *body]),
                        StmtKind::While { cond, body } => out.extend([*cond, *body]),
                        StmtKind::Return(Some(x)) | StmtKind::Assert(x) | StmtKind::Expr(x) => out.push(*x),
                        StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
                    }
                }
                out.extend(b.tail);
            }
            ExprKind::If { cond, then, else_, .. } => {
                out.extend([*cond, *then]);
                out.extend(*else_);
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                out.push(*scrutinee);
                for arm in arms {
                    out.extend(arm.guard);
                    out.push(arm.body);
                }
            }
            ExprKind::Closure { body, .. } | ExprKind::Handle { body, .. } => out.push(*body),
            ExprKind::Par { range, body, .. } => out.extend([range.lo, range.hi, *body]),
            ExprKind::Binary { lhs, rhs, .. } => out.extend([*lhs, *rhs]),
            ExprKind::Call { callee, args, .. } => {
                out.push(*callee);
                out.extend(args.iter().map(|a| a.expr));
            }
            ExprKind::Index { base, index } => out.extend([*base, *index]),
            ExprKind::Range(r) => out.extend([r.lo, r.hi]),
        }
        out
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

/// `at name`: the clock of an input or output of a flow or a function, or of
/// an expression (§11.3). `span` runs from `at` to the end of the name; the
/// name is not resolved here (clocks are a namespace of their own, §11.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clock {
    pub name: Ident,
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

/// The visibility of a declaration or a field (§15.1): three levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vis {
    /// No word: within the package (§15.1). Until W4-03 gives it that
    /// meaning, the names stage reads it as within the module, as `priv`.
    Default,
    /// `priv`: within the module.
    Priv,
    /// `pub`: out of the package.
    Pub,
}

// ---------------------------------------------------------------- items

#[derive(Debug, Clone)]
pub struct Item {
    pub span: Span,
    pub attrs: Vec<Attr>,
    pub vis: Vis,
    /// The first word of [`Item::vis`] when one was kept (the E0200 of
    /// `pub use`, §15.1, S-596).
    pub vis_span: Option<Span>,
    pub kind: ItemKind,
    /// The unit of the item has a diagnostic of the syntax stage (spec §18.1,
    /// S-59, R-71): the later stages do not check its body, and its uses get
    /// no diagnostic for what could not be read. `None` for the items whose
    /// unit has none. Set by [`crate::parse`] (an item the parser stopped in,
    /// and an item whose unit has a syntax diagnostic of another kind).
    pub failed: Option<Failed>,
}

/// How far a failed item was read ([`Item::failed`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Failed {
    /// The item was read whole, and its unit has a diagnostic of the syntax
    /// stage elsewhere (an E0010 in its body, a `;` after it, S-254): its body
    /// is not checked, and its uses are checked against it whole (S-260 does
    /// not apply: nothing of it is unknown).
    Unit,
    /// The heading was read whole, and the rest was cut (the name, the generics, the parameters,
    /// the return type and the effects of a function or flow; the type of a
    /// `const`; the name and generics of a struct, enum or trait; the heading
    /// of an `impl`): its uses are checked against it. The body, the value,
    /// the fields, the variants or the members were cut; what was not read is
    /// [`ExprKind::Error`], and the fields and variants that were not read are
    /// absent (their uses get no diagnostic, S-260).
    Body,
    /// The heading was cut: only the name is known. A function or flow is
    /// an error to its users (a call of it is not checked against it); a
    /// type that was not read is [`TypeKind::Error`].
    Heading,
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

impl Attr {
    /// Whether it is `@name(value)` with the one value a name (`@fp(relaxed)`,
    /// `@repr(c)`): the names and values are those of [`crate::attrs`], the
    /// table that checked the attribute where the parser read it.
    pub fn is(&self, name: &str, value: &str) -> bool {
        self.name.name == name
            && matches!(self.args.as_slice(), [AttrArg::Path(p)] if p.segments.len() == 1 && p.segments[0].name == value)
    }

    /// `@fp(relaxed)` (spec §15.5): the floating-point operations may be
    /// contracted and reassociated.
    pub fn is_fp_relaxed(&self) -> bool {
        self.is(crate::attrs::FP, crate::attrs::RELAXED)
    }
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
    /// The clock after the result type (§11.3; outside a flow E0821, W4-12).
    pub ret_clock: Option<Clock>,
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
    /// The clock after the type (`x: F32 at sample`, §11.3): of a flow's
    /// input; on any other parameter list (a function, a method, an anonymous
    /// function, `extern`, a handler, S-368) the names stage's E0821 (W4-12).
    pub clock: Option<Clock>,
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
    /// The clock of the output (`-> F32 at sample`, §11.3).
    pub ret_clock: Option<Clock>,
    pub body: ExprId,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Ident,
    pub generics: Vec<GenericParam>,
    /// `: PartialEq + Eq` at the head (§6.4).
    pub derives: Derives,
    /// The layout, from `@repr` (§6.5).
    pub repr: Repr,
    pub fields: Vec<Field>,
}

/// The traits written at the head of a struct or an enum (§6.4).
#[derive(Debug, Clone)]
pub enum Derives {
    /// The traits as written (none for no `:`).
    Listed(Vec<Path>),
    /// What the head lists is not known: an attribute of the declaration
    /// could not be read (§18.1, S-460), and the uses that rely on the list
    /// get no diagnostic.
    Unknown,
}

impl Derives {
    /// The traits as written; none when they are not known.
    pub fn listed(&self) -> &[Path] {
        match self {
            Derives::Listed(ps) => ps,
            Derives::Unknown => &[],
        }
    }
}

/// The layout of a struct (§6.5, §12.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Repr {
    /// No `@repr`: the layout of Onsa.
    Onsa,
    /// `@repr(c)`.
    C,
    /// An attribute of the declaration could not be read (§18.1, S-460).
    Unknown,
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
    /// `: PartialEq + Eq` at the head (§6.4).
    pub derives: Derives,
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
    /// The parentheses written around the type (`(I32)` is `I32`, §2.4,
    /// R-43): no part of the type, kept for `onsa fmt` (W3-12 removes them).
    pub parens: u32,
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
    /// A const generic argument written as a constant expression that is not
    /// a type (`Ring[F32, 4]`, `Ring[F32, N * 2]`, §4.5, S-24, R-192); only
    /// valid inside a `Path` type's `args`. A constant's name
    /// (`Ring[F32, TABLE_SIZE]`) parses as a `Path` type and is resolved by
    /// the expected parameter kind.
    ConstArg(ExprId),
    /// A type a syntax error left unread, in a failed item ([`Item::failed`]).
    /// The later stages read it as the error type and report nothing for it.
    Error,
}

// ---------------------------------------------------------------- statements

#[derive(Debug, Clone)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// `@mem(bulk) let pat[: T] = e`
    Let {
        /// The attributes before it (`@mem`, §12.4), checked by the table.
        attrs: Vec<Attr>,
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

/// Whether a range has its end (§7, S-257): `a..<b` does not, `a..=b` does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RangeEnd {
    /// `a..<b`
    Excluded,
    /// `a..=b`
    Included,
}

impl RangeEnd {
    /// The symbol of the range.
    pub fn symbol(self) -> &'static str {
        match self {
            RangeEnd::Excluded => "..<",
            RangeEnd::Included => "..=",
        }
    }

    /// The comparison of a value with the end that holds inside the range
    /// (`k < b`, `k <= b`; the guards of the range patterns, S-249).
    pub fn cmp(self) -> &'static str {
        match self {
            RangeEnd::Excluded => "<",
            RangeEnd::Included => "<=",
        }
    }
}

/// A range `lo..<hi` or `lo..=hi`: the head of a `for` ([`ExprKind::Range`])
/// or of a `par` ([`ExprKind::Par`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangeHead {
    pub lo: ExprId,
    pub hi: ExprId,
    pub end: RangeEnd,
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
    /// `%`, a group of its own (S-45).
    Remainder,
    Comparison,
    And,
    Or,
    Bitwise,
}

impl OpGroup {
    /// The strengths of §3.1, the one table of them: whether an expression of
    /// this group may be, without parentheses, an operand of an operator of
    /// `weaker` (multiplicative > additive > comparison > `&&`, `||`;
    /// remainder > comparison; `&&` and `||` have none between them, the
    /// remainder none with the additive and multiplicative groups, the
    /// bitwise group none with any group). The table is closed under
    /// transitivity. The tree of a chain ([`Chain`]: the AST, the height of
    /// spec §2.5, the readings of E0010) and [`BinOp::takes`] read it.
    pub fn stronger(self, weaker: OpGroup) -> bool {
        use OpGroup::*;
        matches!(
            (self, weaker),
            (Multiplicative, Additive | Comparison | And | Or)
                | (Additive, Comparison | And | Or)
                | (Remainder, Comparison | And | Or)
                | (Comparison, And | Or)
        )
    }

    /// Whether `a op b op c` of one group is allowed (§3.1 table): every
    /// group but comparison and bitwise; in the bitwise group, the same
    /// operator only ([`BinOp::takes`]).
    fn chains(self) -> bool {
        !matches!(self, OpGroup::Comparison | OpGroup::Bitwise)
    }
}

/// The rest `..` of a struct pattern (§7, S-366): its span, and what a
/// candidate removes when no field remains: the `,` before it and the
/// blanks between them, or the `..` alone when a comment is between (S-251).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructRest {
    pub span: Span,
    pub removal: Span,
}

/// The side of an operand of a binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

/// What an expression is at its top, as the operand of a binary operator
/// (§3.1, §3.3): what decides whether it is written in parentheses there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// A name, a literal, a postfix chain, a prefix operator, a bracket.
    Plain,
    /// A suffix form weaker than every binary operator: `x as T` and the
    /// `e at k` of flow. It is in parentheses as an operand (E0011).
    AsAt,
    /// A chain whose root is this operator.
    Binary(BinOp),
}

impl Operand {
    /// Whether the operand is written without parentheses before `as` or
    /// `at` (§3.1: they bind tighter than every binary operator and do not
    /// chain, E0011): the candidate that writes a clock or a cast after an
    /// expression (`clock_on_binding`) reads it.
    pub fn bare_before_as_at(self) -> bool {
        self == Operand::Plain
    }
}

impl BinOp {
    /// Whether `operand` is written without parentheses on `side` of this
    /// operator (§3.1, §3.3; S-339, S-341): the one judgment of the
    /// parentheses of a written operand ([`BinOp::takes`] for a chain, E0011
    /// for `as` and `at`). The guard candidates of the patterns read it for
    /// the ends of a range and the guard of the arm; `fmt` (W3-12) for the
    /// parentheses it may remove.
    pub fn bare(self, side: Side, operand: Operand) -> bool {
        match operand {
            Operand::Plain => true,
            Operand::AsAt => false,
            Operand::Binary(child) => self.takes(side, child),
        }
    }
}

impl BinOp {
    pub fn group(self) -> OpGroup {
        use BinOp::*;
        match self {
            Add | Sub | WrapAdd | WrapSub | SatAdd | SatSub => OpGroup::Additive,
            Mul | Div | WrapMul | SatMul => OpGroup::Multiplicative,
            Rem => OpGroup::Remainder,
            Eq | Ne | Lt | Le | Gt | Ge => OpGroup::Comparison,
            And => OpGroup::And,
            Or => OpGroup::Or,
            BitAnd | BitOr | BitXor | Shl | Shr => OpGroup::Bitwise,
        }
    }

    /// Whether an operator node `child`, not in parentheses, may be the
    /// operand on `side` of this operator (§3.1): its group is stronger, or
    /// it is on the left, of the same group, and the group chains (in the
    /// bitwise group, the same operator, S-61). The one judgment of an edge
    /// of the tree: E0010, the parentheses its candidates need, and the
    /// parentheses `fmt` may remove read it.
    pub fn takes(self, side: Side, child: BinOp) -> bool {
        let (g, c) = (self.group(), child.group());
        c.stronger(g) || (side == Side::Left && c == g && (g.chains() || (g == OpGroup::Bitwise && self == child)))
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

/// A chain of binary operators read as a tree (§3.1): the shunting-yard
/// algorithm, read from the left. The operators on the stack wait for their
/// right operand, each in the right operand of the one below it; an
/// operator closes the waiting ones it does not bind tighter than (left
/// associativity; groups without a strength between them, E0010, are read
/// left to right too). The one reading of a chain: the AST (`T` a node), the
/// height of spec §2.5 the parser counts (`T` a height), and the readings of
/// the candidates of E0010 (`tighter` a placement of strengths).
pub struct Chain<T, O> {
    /// The waiting operators, each with its left operand.
    stack: Vec<(T, O)>,
    /// The last operand, or the operators it closed.
    current: T,
}

impl<T: Copy, O: Copy> Chain<T, O> {
    pub fn new(first: T) -> Self {
        Chain { stack: Vec::new(), current: first }
    }

    /// An operator `op` after the last operand: the waiting operators it does
    /// not bind tighter than (`tighter(op, waiting)`) take the last operand
    /// as their right one and close (`join(left, waiting, right)`). Returns
    /// how many operators wait then, this one included, and its left operand.
    pub fn operator(
        &mut self,
        op: O,
        mut tighter: impl FnMut(O, O) -> bool,
        mut join: impl FnMut(T, O, T) -> T,
    ) -> (usize, T) {
        while let Some(&(left, waiting)) = self.stack.last() {
            if tighter(op, waiting) {
                break;
            }
            self.current = join(left, waiting, self.current);
            self.stack.pop();
        }
        self.stack.push((self.current, op));
        (self.stack.len(), self.current)
    }

    pub fn operand(&mut self, operand: T) {
        self.current = operand;
    }

    /// The whole chain: the waiting operators close.
    pub fn finish(mut self, mut join: impl FnMut(T, O, T) -> T) -> T {
        while let Some((left, op)) = self.stack.pop() {
            self.current = join(left, op, self.current);
        }
        self.current
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
    /// `v.(x)`: a call through a function value (§6.1, S-191); `dot` is
    /// the `.`, which follows the callee on its line or starts the next line
    /// (§2.5). `onsa fmt` and the candidates read it from here, never from
    /// the text (a comment between the callee and the `.` may hold one).
    Value { dot: Span },
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

/// The list of a `::[…]` in an expression (§4.5): its types and const
/// arguments, and its span from `::` to `]`.
#[derive(Debug, Clone)]
pub struct TypeArgList {
    pub args: Vec<TypeId>,
    pub span: Span,
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
    /// A body, a value or (from M7, T7-1) a statement a syntax error left
    /// unread, in a failed item ([`Item::failed`]). The later stages do not
    /// check the body of a failed item, so they never meet it; a statement the
    /// recovery of M7 skips will be an expression statement of it.
    Error,
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
    /// `Point { x: 1.0, y: 2.0 }`, `Pr::[U8] { a: 250 }`
    Struct {
        path: Path,
        /// The type arguments written after a name of the path (`::[…]`,
        /// §4.5): the index of that segment and the list.
        type_args: Vec<(usize, TypeArgList)>,
        fields: Vec<(Ident, ExprId)>,
    },
    Block(Block),
    /// `if c { a } else { b }`; `else if` nests another `If` in `else_`.
    /// `tilde` is the `~` of `if~` (§11.5): only the first `if` of a chain
    /// has it, and it stands for the whole chain.
    If {
        cond: ExprId,
        then: ExprId,
        else_: Option<ExprId>,
        tilde: Option<Span>,
    },
    /// `match x { … }`; `tilde` is the `~` of `match~` (§11.5).
    Match {
        scrutinee: ExprId,
        arms: Vec<MatchArm>,
        tilde: Option<Span>,
    },
    /// `fn(x: F32) -> F32 { ... }` (anonymous function)
    Closure {
        params: Vec<Param>,
        ret: Option<TypeId>,
        /// The clock after the result type (E0821, W4-12).
        ret_clock: Option<Clock>,
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
    /// `par i in a..<b { ... }`, `par i in a..=b { ... }`
    Par {
        var: Ident,
        range: RangeHead,
        body: ExprId,
    },
    /// `lhs op rhs`: one operator of a chain, the chain read as the tree of
    /// §3.1 ([`Chain`]; groups checked later, E0010).
    Binary {
        op: BinOp,
        op_span: Span,
        lhs: ExprId,
        rhs: ExprId,
    },
    /// `e as T`
    Cast {
        expr: ExprId,
        ty: TypeId,
    },
    /// `e at k` (§11.3): the clock of an expression.
    At {
        expr: ExprId,
        clock: Clock,
    },
    /// `^name` (§2.6, §11.2): the reference to a `let` of a flow; the span of
    /// the expression starts at the `^`, the ident is the name.
    Feedback(Ident),
    Unary {
        op: UnOp,
        expr: ExprId,
    },
    /// `f(args)`, `f~(args)`, `x.f!(args)`, `v.(args)`
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
    /// `e::[T, …]`: type arguments written after a path of names in an
    /// expression (§4.5, S-239). The later stages give them to the item the
    /// path names (W5-10).
    TypeArgs {
        base: ExprId,
        args: TypeArgList,
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
    /// `move x` in a consuming position (§5.2, S-21): let/var initializer,
    /// assignment value, literal element, `match move x`. Call arguments keep
    /// `Arg.mode` and `for ... in move xs` keeps `StmtKind::For.moved`.
    Move(ExprId),
    /// `a..<b`, `a..=b` (only in `for` heads; a `par` head is in `Par`)
    Range(RangeHead),
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
    /// The parentheses written around the pattern (`(p)` is `p`, §2.4,
    /// R-43): no part of the pattern, kept for `onsa fmt` (W3-12).
    pub parens: u32,
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
        /// The rest `..` (§7: E0020, S-109, S-366).
        rest: Option<StructRest>,
    },
    /// `p | q`
    Or(Vec<PatId>),
}
