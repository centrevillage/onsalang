//! The tables of a typed body that the later stages read ([`BodyInfo`]):
//! its locals, what its names resolved to, its instances, and what the
//! modes stage puts in it (the drop points, the parts bound to no name).

use onsa_diag::Span;
use onsa_diag::hash::{HashMap, HashSet};
use onsa_syntax::ast::{ExprId, Mode, PatId};
use serde::{Deserialize, Serialize};

use crate::DefId;
use crate::binding::{Bind, Head, HeadRow, LitClass};
use crate::modes::Proj;
use crate::names::body::BindingKind;
use crate::ty::{Ty, TyId, Types};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LocalId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalKind {
    /// A function parameter with its mode.
    Param(Mode),
    /// The `self` receiver with its mode.
    SelfParam(Mode),
    Let,
    Var,
    /// `for` variable; `moved` for `for x in move xs`.
    For {
        moved: bool,
    },
    MatchBind,
    ClosureParam(Mode),
}

impl LocalKind {
    /// The kind of the binding of the record: a flow's input is a borrowed
    /// parameter, its `let` and the variable of a `par` are `let`s.
    pub(super) fn of(kind: BindingKind) -> LocalKind {
        match kind {
            BindingKind::Param(m) => LocalKind::Param(m),
            BindingKind::SelfParam(m) => LocalKind::SelfParam(m),
            BindingKind::Let | BindingKind::FlowLet | BindingKind::ParVar => LocalKind::Let,
            BindingKind::Var => LocalKind::Var,
            BindingKind::For { moved } => LocalKind::For { moved },
            BindingKind::MatchBind => LocalKind::MatchBind,
            BindingKind::ClosureParam(m) => LocalKind::ClosureParam(m),
            BindingKind::FlowInput => LocalKind::Param(Mode::Borrow),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalInfo {
    pub name: String,
    pub span: Span,
    /// Resolved at the end of the body (may still contain `Ty::Param` in generic bodies).
    pub ty: TyId,
    pub kind: LocalKind,
    /// Its state (§5.4), settled after the types stage ([`crate::binding`]);
    /// the types stage does not read it.
    pub state: Bind,
}

impl LocalInfo {
    pub(crate) fn set_state(&mut self, state: Bind) {
        self.state = state;
    }

    /// A function-type parameter of the default mode (§5.2, S-190), of a
    /// function or an anonymous function: second-class in its body, as it
    /// may hold captures (§13.5). By its declared type (an alias resolved);
    /// not a `T` a function type fills, nor an `inout` or `move` one.
    pub fn fn_param(&self, types: &Types) -> bool {
        matches!(self.kind, LocalKind::Param(Mode::Borrow) | LocalKind::ClosureParam(Mode::Borrow))
            && matches!(types.get(self.ty), Ty::Fn(_))
    }
}

/// Instantiation of a generic def at a call site (for monomorphization).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Instance {
    pub def: DefId,
    /// One per generic parameter of the def (const parameters as `ConstVal`).
    pub args: Vec<TyId>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InstId(pub u32);

/// What a path, field chain, or call resolved to.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Target {
    Local(LocalId),
    /// A `const N` generic parameter used as a `U32` value.
    ConstParam(u32),
    /// A function item (as a value, or the callee of a `Call`). `of`: see
    /// [`Target::Method`].
    Fn {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A constant. `inst` holds the type arguments of a constant of a generic
    /// `impl`, read as a value (S-304); `None` for any other constant, and
    /// where a length or a constant expression reads one by its value. `of`:
    /// see [`Target::Method`].
    Const {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A unit variant (value) or tuple variant (constructor / callee).
    Variant {
        def: DefId,
        index: u32,
    },
    /// `panic` (§9.2).
    Panic,
    /// `x.m(...)` on a user type: the method def; the receiver is the callee's `base`.
    ///
    /// `of` is the type parameter of a member of its bounds (`T.ZERO`,
    /// `T.round_from(k)`, `x.checked_add(y)`). Then `def` is the member of the
    /// representative type ([`crate::traits::MEMBERS`]), and only the form of
    /// its declaration may be read (its kind, `self`, the modes, `rt`, the
    /// effects), which is the same for every type of the bound. What depends
    /// on the type (its value, its types, the type in a message) is not read
    /// from it: the types stage reads the declaration at `of`, and lowering
    /// binds the use to the member of the instantiated type
    /// (`Lowerer::instance_target`).
    Method {
        def: DefId,
        of: Option<TyId>,
        inst: Option<InstId>,
    },
    /// A call through a function value (closure or `fn` value).
    Value,
}

/// The constructors of a `?` (§9.1), by their index: that of the value it
/// takes out, and that of the early return, which keeps its elements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TryArms {
    pub keep: u32,
    pub exit: u32,
}

/// Typed body of one function, test, or `const` initializer.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct BodyInfo {
    /// Type of every expression, fully resolved (variables substituted).
    pub expr_types: HashMap<ExprId, TyId>,
    pub locals: Vec<LocalInfo>,
    /// Path / field-chain / call expressions → what they refer to.
    pub targets: HashMap<ExprId, Target>,
    /// `PatKind::Bind` patterns → the local they introduce.
    pub pat_locals: HashMap<PatId, LocalId>,
    /// The constructor patterns of an enum (`S.Circle(r)`, `Self.Dot`,
    /// `None`) → the index of the constructor they name, as the names stage
    /// resolved their path: the lowering reads it (D-15).
    pub pat_ctors: HashMap<PatId, u32>,
    /// The constants of the patterns (`LIMIT`, `cfg.LIMIT`, `I64.MAX`), each
    /// a [`Target::Const`]: the lowering compares with them (§7, S-185).
    pub pat_consts: HashMap<PatId, Target>,
    pub instances: Vec<Instance>,
    /// Closure expression → outer locals it captures (by copy, §5.3).
    pub captures: HashMap<ExprId, Vec<LocalId>>,
    /// A hole of a string literal (§2.4), by the literal and the index of the
    /// hole in its segments → what the name its path ends at refers to.
    pub hole_targets: HashMap<(ExprId, u32), Target>,
    /// `-e` expressions whose operand, without parentheses, is a numeric literal:
    /// the `-` is a part of the literal's value (§4.7, S-184, S-227). The lowering
    /// folds exactly these (R-03); every other `-` negates a value.
    pub neg_literals: HashSet<ExprId>,
    /// The `?` expressions that passed the check → their constructors: the
    /// lowering reads them (S-71, D-15).
    pub tries: HashMap<ExprId, TryArms>,
    /// What diverges (§7), as the names stage recorded it.
    pub diverging: crate::tails::Diverging,
    /// The rows of the heads of the bindings (§5.4), and the marks of the
    /// static values, the literals that need no drop and the owned aggregate
    /// literals with their first element, settled with the states of the
    /// locals ([`crate::binding`]).
    pub heads: HashMap<Head, HeadRow>,
    pub lits: HashMap<ExprId, LitClass>,
    /// `false` when checking stopped at the first error (tables are partial).
    pub complete: bool,
    /// The body reads what the check does not read (§18.1, S-692: a name the
    /// names stage holds as an error, a member of a def a syntax error cut):
    /// the check went on, and a fix of the name can show an error it did not
    /// report. Its signature is not changed, so its users are not affected,
    /// except the callers of an rt function: a call on a value of the error
    /// type makes no edge of the rt recursion (`Analysis::reached`).
    pub read_unread: bool,
    /// The drop points (§12.2, R-32), each once, in the order the modes
    /// stage's walk that reports met them (a point no path reaches is none,
    /// S-873). Of an Affine value, a point where it may be live and is
    /// dropped; of a Dup one, where its owned reference may be let go: the
    /// count of `Alloc` (`crate::drop_alloc`, the one reader). Where the
    /// copies and the drops are put is Core's (D-15, W8-04), which reads
    /// these only to stop on a field taken out. Not of a flow's body. The
    /// note of an owned aggregate literal names its first element from
    /// [`BodyInfo::lits`] (`LitClass::Owned`, S-613, W6-03).
    pub drops: Vec<DropPoint>,
    /// The consumptions of a Dup value that copy it and do not move it, with
    /// why (§5.2, §5.4, S-1030, S-1035): a row for each binding dropped after
    /// it and each, by the binding ([`BodyInfo::copied_of`]). The modes stage
    /// writes them, and thins its drop points by them; the notes of the
    /// E0601 of a drop and Core (W8-04) read them. Not of a flow's body.
    pub copied: Vec<Copied>,
    /// The parts of the values the patterns and the `move _` parameters bind
    /// to no name (§5.4, S-1036, S-1044), with their types: the modes stage
    /// drops those of an owned head.
    pub discards: HashMap<Unbound, Discard>,
    /// How the effect row of each anonymous function was decided (§8.1): the
    /// notes of its E0601 read it (`crate::uses::Scope`, S-1041). Only the
    /// bodies of a package are recorded, so not in the base of std.
    #[serde(skip)]
    pub closure_rows: HashMap<ExprId, RowFrom>,
}

impl BodyInfo {
    /// The consumptions that copy the value of the binding `l` (its rows
    /// of [`BodyInfo::copied`]), in the order they are written.
    pub fn copied_of(&self, l: LocalId) -> &[Copied] {
        let start = self.copied.partition_point(|c| c.root < l);
        let end = start + self.copied[start..].partition_point(|c| c.root == l);
        &self.copied[start..end]
    }
}

/// A consumption `at` of a Dup value that copies it and does not move it,
/// so the binding `root` keeps its value (§5.2, §5.4, S-1035), and why.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Copied {
    pub root: LocalId,
    pub at: ExprId,
    pub why: CopiedWhy,
}

/// Why a consumption of a Dup value copies it (S-1035).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CopiedWhy {
    /// `root`, released (S-1030), is used after, at the place.
    After(Span),
    /// The next iteration of a loop uses it, at the place (written at or
    /// before the consumption).
    Loop(Span),
    /// Another argument of the same call borrows a place it overlaps, at the
    /// place (E0702's test, §5.2).
    InCall(Span),
    /// The value is a borrow binding of the head, derived from the whole
    /// of `root` (§5.4: `match o`, `for s in xs`).
    Head(Head),
}

/// Where the effect row of an anonymous function comes from (§8.1, §4.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowFrom {
    Written,
    /// The function type expected where it is written.
    Expected(TyId),
    /// No function type is expected there: the row is empty.
    NoneExpected,
    /// A later branch of a merge, which takes no row (S-1032 (ii-3)).
    Joining,
    /// The type expected there is not read (an error type): the row is not
    /// known, and its uses are not checked (§18.1, R-460).
    Unread,
}

/// What binds a part of a value to no name (§5.4, S-1036).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Unbound {
    /// A `_`, a literal or a constant (the part it matches), a struct
    /// pattern that ends in `_` (the fields the `_` leaves); not a variant
    /// with no payload (S-1044).
    Pat(PatId),
    /// The `move _` parameter `index` of the function, or of the anonymous
    /// function `closure`.
    Param { closure: Option<ExprId>, index: u32 },
}

/// Where it is written, and the types of the parts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Discard {
    pub at: Span,
    pub tys: Vec<TyId>,
}

/// A drop point of a body: where (`at`, by what it drops: of an `End` the
/// empty span at the end of the scope, of a `Rest` the expression that takes
/// out, of the others the exit, the end of a `for` its value), of what, and
/// whether the value is live on every path that reaches it (`sure`). Its
/// scope is the anonymous function around where its value is written
/// (`crate::uses::Closures::around`, the one place that decides it).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DropPoint {
    pub at: Span,
    pub what: Dropped,
    pub sure: bool,
}

/// What a drop point drops.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Dropped {
    /// An owned local at the end of its scope (a block, an arm, an iteration
    /// of a `for` and its pattern's bindings, a body and the parameters of a
    /// function or an anonymous function).
    End(LocalId),
    /// An owned local an exit leaves (`return`, `?`, `break`, `continue`).
    Exit(LocalId),
    /// What is left where a path of fields is taken out at `at` (S-85).
    Rest(Taken),
    /// The value of an operand an exit leaves before its consumer runs (A-1).
    Value(ExprId),
    /// The rest of the value `iter` an owned `for` iterates (S-1037): at its
    /// end its container; left `early` (a `break`, a `return`, a `?`), the
    /// elements not iterated too.
    IterRest { iter: ExprId, early: bool },
    /// A value made where nothing consumes it (R-32), dropped after what
    /// reads or borrows it (a call, an index, an operator) runs.
    Temp(ExprId),
    /// What is left of a value no binding owns where a path is taken out
    /// of it (S-85, R-32). Boxed, so that `Rest` alone holds a `Vec` and the
    /// drop points of a body stay as small as before (`DropPoint`, 48 bytes).
    TempRest(Box<Taken<ExprId>>),
    /// The value the place `target` held before it is assigned (R-32,
    /// S-1038: of a `var`, a `move` or an `inout` parameter alike).
    Overwrite(ExprId),
    /// What an owned head binds to no name (§5.4, S-1036).
    Discard(Unbound),
    /// The value of `e` in `[e; N]` whose length may be 0 (S-1045): put in no
    /// element, it is dropped there. `zero`: the length is 0 (not a const
    /// parameter).
    Unplaced { value: ExprId, zero: bool },
}

/// A path of fields taken out of the owned local `root` (S-85), or of a value.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Taken<R = LocalId> {
    pub root: R,
    /// Its steps: fields and tuple elements only.
    pub(crate) path: Vec<Proj>,
}
