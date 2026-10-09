//! The concrete syntax tree (R-86, plan D-02 as revised on 2026-10-05).
//!
//! The parser builds the CST; the AST is made from it in one stage
//! ([`crate::lower`]). The CST holds every token of the lexer, the trivia
//! included (whitespace, newlines, comments, doc comments), so walking its
//! leaves gives the source back byte for byte, also for a source with errors.
//!
//! - Nodes and tokens live in arenas and refer to each other by index. The
//!   children of a node are in source order; the leaves of the tree, in
//!   order, are the token list of the lexer.
//! - Trivia are tokens of their own. Every token the parser consumes is in
//!   the node open when it consumes it; where the tokens it skips go is
//!   decided in one place, [`build`]: before a node's first token they go
//!   outside the node, after its last token they leave it. The doc comments
//!   of an item are consumed by the parser into the item's `Docs` node.
//! - Whether a newline ended a statement shows in the tree: a statement
//!   newline is a child of a node that holds statements (`SourceFile`,
//!   `Block`, `ItemList`), a continuation newline is inside an expression.
//! - A node that a syntax error left unfinished has `complete == false`.
//!   It may be empty: then it sits right after the last token placed before
//!   it (before the trivia that follow), not at the token that failed; the
//!   position of the error is the position of the syntax diagnostic. Its
//!   kind is the one the parser gave when it opened it, which may be a
//!   provisional one (a `TypeParam` that would have become a `ConstParam` or
//!   an `EffectParam`, a `TupleExpr` that would have become a `ParenExpr`):
//!   only a complete node's kind is final. The tokens the recovery skipped
//!   are in an `Error` node (see [`NodeKind::Error`] for where).
//! - The position of a node ([`Cst::span`]) runs from its first to its last
//!   token that is not trivia: it is the span of the AST node made from it.
//!
//! The functions that walk the tree do not recurse (a deep input does not
//! use the stack here).

use std::ops::Range;

use onsa_diag::{FileId, Span};

use crate::token::{Token, TokenKind};

/// Index of a node in [`Cst`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

/// Index of a token in [`Cst::tokens`] (the full token list of the lexer).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TokenIdx(pub u32);

/// A child of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Elem {
    Node(NodeId),
    Token(TokenIdx),
}

/// The kinds of nodes. The children are listed as the parser writes them;
/// trivia may come between any two of them. Lists (`…List`, `…Args`,
/// `…Params`, `…Fields`, `MatchArms`, `UseNames`) hold the opening token, the
/// elements and their `,`, and the closing token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /// The file: `Item`, `Error`, then `Eof`.
    SourceFile,
    /// Tokens skipped by the recovery after a syntax error. It is in one of
    /// two places: the last child of the item the error stopped (`Item`, not
    /// complete), or a child of `SourceFile` for extra tokens after an item
    /// that parsed (`fn f() {} junk`).
    Error,
    /// The name a declaration introduces (an item, a field, a variant, a
    /// generic parameter, a parameter, `var`, the index of `par`): one token,
    /// an identifier (or `self` / `_` for a parameter).
    Name,

    // ------------------------------------------------------------ items
    /// `Docs`?, `Attr`*, `Vis`?, then one declaration node.
    Item,
    /// The doc comments the parser took for the item: from the first `///`
    /// to the last, with the blank lines and `//` between them.
    Docs,
    /// `@name AttrArgs?`
    Attr,
    /// `( (AttrNamedArg | Path | Str), ... )`
    AttrArgs,
    /// `key: Expr`
    AttrNamedArg,
    /// `pub`, `pub(pkg)`
    Vis,
    /// `rt? fn name GenericParams? ParamList (-> Type)? (uses EffectRow)? Block?`
    Fn,
    /// `flow name ParamList -> Type Block`
    Flow,
    /// `struct name GenericParams? (FieldList | TupleStructBody)`
    Struct,
    /// `{ Field, ... }`
    FieldList,
    /// `Vis? name: Type`
    Field,
    /// `( Type )`
    TupleStructBody,
    /// `enum name GenericParams? VariantList`
    Enum,
    /// `{ Variant, ... }`
    VariantList,
    /// `name VariantFields?`
    Variant,
    /// `( Type, ... )`
    VariantFields,
    /// `type name = Type`
    TypeAlias,
    /// `type name` (in `extern` or after `target`)
    OpaqueType,
    /// `trait name GenericParams? ItemList`
    Trait,
    /// `impl GenericParams? Type (for Type)? ItemList`
    Impl,
    /// `blocking? effect name ItemList`
    Effect,
    /// `handler name ParamList? : Path ItemList`
    Handler,
    /// `const name: Type (= Expr)?`
    Const,
    /// `use UseTree`
    Use,
    /// `name (. name)* (. UseNames)?`
    UseTree,
    /// `{ name, ... }`
    UseNames,
    /// `extern Str lib Str ItemList`
    Extern,
    /// `target (OpaqueType | Fn)`
    Target,
    /// `test Str Block`
    Test,
    /// `{ Item ... }` (the body of `trait`, `impl`, `effect`, `handler`, `extern`, an inline handler)
    ItemList,
    /// `[ (TypeParam | ConstParam | EffectParam), ... ]`
    GenericParams,
    /// `Name (: Bound (+ Bound)*)?`
    TypeParam,
    /// `const NAME: Type`
    ConstParam,
    /// `e` (a lowercase name: an effect-row variable)
    EffectParam,
    /// `?? Path`
    Bound,
    /// `( Param, ... )`
    ParamList,
    /// `Attr* (inout | move)? (mut)? (name | self | _) (: Type)?`
    Param,
    /// `{ Path, ... }` after `uses`
    EffectRow,
    /// `name (. name)*`
    Path,

    // ------------------------------------------------------------ types
    /// `Path TypeArgs?`
    PathType,
    /// `[ (Type | ConstArg), ... ]`
    TypeArgs,
    /// `Expr`: a constant expression that is not a type (§4.5)
    ConstArg,
    /// `( )`
    UnitType,
    /// `( Type, Type, ... )`
    TupleType,
    /// `( Type )`: a group, the type in it (§2.4, R-43)
    ParenType,
    /// `[ Type ; Expr ]`
    ArrayType,
    /// `rt? fn FnTypeParams (-> Type)? (uses EffectRow)?`
    FnType,
    /// `( (inout | move)? Type, ... )`
    FnTypeParams,

    // ------------------------------------------------------------ statements
    /// `{ statements }`: the statement nodes and the newlines between them.
    Block,
    /// `let Pat (: Type)? = Expr`
    LetStmt,
    /// `var name (: Type)? = Expr`
    VarStmt,
    /// `for Pat in move? Expr Block`
    ForStmt,
    /// `while Expr Block`
    WhileStmt,
    BreakStmt,
    ContinueStmt,
    /// `return Expr?`
    ReturnStmt,
    /// `assert Expr`
    AssertStmt,
    /// `Expr = Expr`
    AssignStmt,
    /// `Expr`
    ExprStmt,

    // ------------------------------------------------------------ expressions
    /// One literal token: `Int`, `Float`, `Char`, `Str`, `true`, `false`.
    Literal,
    /// `_`
    HoleExpr,
    /// One name token: an identifier, `self`, `Self`.
    PathExpr,
    /// `( Expr )`
    ParenExpr,
    /// `( )`, `( Expr, ... )`
    TupleExpr,
    /// `[ Expr, ... ]`
    ArrayExpr,
    /// `[ Expr ; Expr ]`
    RepeatExpr,
    /// `if Expr Block (else (IfExpr | Block))?`
    IfExpr,
    /// `match (MoveExpr | Expr) MatchArms`
    MatchExpr,
    /// `{ MatchArm, ... }`
    MatchArms,
    /// `Pat (if Expr)? => Expr`
    MatchArm,
    /// `fn ParamList (-> Type)? (uses EffectRow)? Block`
    ClosureExpr,
    /// `handle Block with Path (ItemList | ArgList)?`
    HandleExpr,
    /// `unsafe Block`
    UnsafeExpr,
    /// `par name in RangeExpr Block`
    ParExpr,
    /// `move Expr`
    MoveExpr,
    /// `Expr (op Expr)+` (a flat chain; groups are checked on the AST)
    BinaryExpr,
    /// `Expr (..< | ..=) Expr`
    RangeExpr,
    /// `Expr as Type`
    CastExpr,
    /// `- Expr`, `! Expr`
    PrefixExpr,
    /// `Expr (~ | !)? ArgList`
    CallExpr,
    /// `( Arg, ... )`
    ArgList,
    /// `(inout | move)? Expr`
    Arg,
    /// `Expr . name`
    FieldExpr,
    /// `Expr . Int`
    TupleIndexExpr,
    /// `(PathExpr | FieldExpr | TupleIndexExpr) :: TypeArgs` (§4.5)
    TypeArgsExpr,
    /// `Expr [ Expr ]`
    IndexExpr,
    /// `Expr ?`
    TryExpr,
    /// `(PathExpr | FieldExpr | TypeArgsExpr) StructLitFields`
    StructLit,
    /// `{ StructLitField, ... }`
    StructLitFields,
    /// `name : Expr`
    StructLitField,

    // ------------------------------------------------------------ patterns
    /// `_`
    WildPat,
    /// `Int`, `Char`, `Str`, `true`, `false`
    LitPat,
    /// `- Int`
    NegLitPat,
    /// `( Pat, Pat, ... )`
    TuplePat,
    /// `( Pat )`: a group, the pattern in it (§2.4, R-43)
    ParenPat,
    /// `Path` of one lowercase name: a binding
    BindPat,
    /// `Path`
    PathPat,
    /// `Path ( Pat, ... )`
    TupleStructPat,
    /// `Path { StructPatField, ... }`, with `StructPatRest` last
    StructPat,
    /// `name : Pat`
    StructPatField,
    /// `..`: the rest of a struct pattern (§7: E0020 where the fields are
    /// counted, S-109, S-366)
    StructPatRest,
    /// `Pat | Pat ...`
    OrPat,
}

impl NodeKind {
    pub fn name(self) -> &'static str {
        use NodeKind::*;
        match self {
            SourceFile => "SourceFile",
            Error => "Error",
            Name => "Name",
            Item => "Item",
            Docs => "Docs",
            Attr => "Attr",
            AttrArgs => "AttrArgs",
            AttrNamedArg => "AttrNamedArg",
            Vis => "Vis",
            Fn => "Fn",
            Flow => "Flow",
            Struct => "Struct",
            FieldList => "FieldList",
            Field => "Field",
            TupleStructBody => "TupleStructBody",
            Enum => "Enum",
            VariantList => "VariantList",
            Variant => "Variant",
            VariantFields => "VariantFields",
            TypeAlias => "TypeAlias",
            OpaqueType => "OpaqueType",
            Trait => "Trait",
            Impl => "Impl",
            Effect => "Effect",
            Handler => "Handler",
            Const => "Const",
            Use => "Use",
            UseTree => "UseTree",
            UseNames => "UseNames",
            Extern => "Extern",
            Target => "Target",
            Test => "Test",
            ItemList => "ItemList",
            GenericParams => "GenericParams",
            TypeParam => "TypeParam",
            ConstParam => "ConstParam",
            EffectParam => "EffectParam",
            Bound => "Bound",
            ParamList => "ParamList",
            Param => "Param",
            EffectRow => "EffectRow",
            Path => "Path",
            PathType => "PathType",
            TypeArgs => "TypeArgs",
            ConstArg => "ConstArg",
            UnitType => "UnitType",
            TupleType => "TupleType",
            ParenType => "ParenType",
            ArrayType => "ArrayType",
            FnType => "FnType",
            FnTypeParams => "FnTypeParams",
            Block => "Block",
            LetStmt => "LetStmt",
            VarStmt => "VarStmt",
            ForStmt => "ForStmt",
            WhileStmt => "WhileStmt",
            BreakStmt => "BreakStmt",
            ContinueStmt => "ContinueStmt",
            ReturnStmt => "ReturnStmt",
            AssertStmt => "AssertStmt",
            AssignStmt => "AssignStmt",
            ExprStmt => "ExprStmt",
            Literal => "Literal",
            HoleExpr => "HoleExpr",
            PathExpr => "PathExpr",
            ParenExpr => "ParenExpr",
            TupleExpr => "TupleExpr",
            ArrayExpr => "ArrayExpr",
            RepeatExpr => "RepeatExpr",
            IfExpr => "IfExpr",
            MatchExpr => "MatchExpr",
            MatchArms => "MatchArms",
            MatchArm => "MatchArm",
            ClosureExpr => "ClosureExpr",
            HandleExpr => "HandleExpr",
            UnsafeExpr => "UnsafeExpr",
            ParExpr => "ParExpr",
            MoveExpr => "MoveExpr",
            BinaryExpr => "BinaryExpr",
            RangeExpr => "RangeExpr",
            CastExpr => "CastExpr",
            PrefixExpr => "PrefixExpr",
            CallExpr => "CallExpr",
            ArgList => "ArgList",
            Arg => "Arg",
            FieldExpr => "FieldExpr",
            TupleIndexExpr => "TupleIndexExpr",
            TypeArgsExpr => "TypeArgsExpr",
            IndexExpr => "IndexExpr",
            TryExpr => "TryExpr",
            StructLit => "StructLit",
            StructLitFields => "StructLitFields",
            StructLitField => "StructLitField",
            WildPat => "WildPat",
            LitPat => "LitPat",
            NegLitPat => "NegLitPat",
            TuplePat => "TuplePat",
            ParenPat => "ParenPat",
            BindPat => "BindPat",
            PathPat => "PathPat",
            TupleStructPat => "TupleStructPat",
            StructPat => "StructPat",
            StructPatField => "StructPatField",
            StructPatRest => "StructPatRest",
            OrPat => "OrPat",
        }
    }
}

#[derive(Debug, Clone)]
struct NodeData {
    kind: NodeKind,
    parent: Option<NodeId>,
    children: Range<u32>,
    /// The tokens of the subtree (trivia included).
    tokens: Range<u32>,
    complete: bool,
}

/// The CST of one file.
#[derive(Debug, Clone)]
pub struct Cst {
    tokens: Vec<Token>,
    nodes: Vec<NodeData>,
    children: Vec<Elem>,
    token_parent: Vec<NodeId>,
}

/// A broken invariant of the tree ([`Cst::validate`]): where (the first
/// token, or the bytes, that disagree) and what.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CstError {
    pub span: Span,
    pub message: String,
}

// ---------------------------------------------------------------- events and the builder

/// What the parser emits ([`crate::parser`]); [`build`] makes the tree.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Event {
    /// A node opens. `forward_parent` points to the `Start` of a node that
    /// wraps this one (`precede`). `kind == None` is a start already taken
    /// by a chain.
    Start { kind: Option<NodeKind>, forward_parent: Option<u32> },
    /// The parser consumed the token (index in the full list).
    Token(u32),
    /// The innermost open node closes; `complete == false` when an error left it.
    Finish { complete: bool },
}

/// Build the tree from the events of the parser. The events open the root
/// (`SourceFile`) first and close it last.
///
/// The rule for the tokens the parser did not consume (trivia, and nothing
/// else): a node that opens takes its place in the tree only when its first
/// token comes (a `Token` event) or when it closes. The tokens not consumed
/// before that token go to the node that was open before it, so the trivia
/// before a node are outside it, and the trivia after a node's last token
/// leave it. Every token a `Token` event consumes is in the node that is
/// open at that event: what belongs to a node is decided by the parser alone
/// (a doc comment the parser takes for an item is in the item's `Docs`).
/// Every token not consumed by the end goes to the root.
pub(crate) fn build(tokens: Vec<Token>, mut events: Vec<Event>) -> Cst {
    let mut b = Builder {
        nodes: Vec::new(),
        children: Vec::new(),
        token_parent: vec![NodeId(u32::MAX); tokens.len()],
        stack: Vec::new(),
        waiting: Vec::new(),
        next_tok: 0,
        tokens: &tokens,
    };
    let mut chain = Vec::new();
    for i in 0..events.len() {
        match events[i] {
            Event::Start { kind: None, .. } => {}
            Event::Start { kind: Some(kind), forward_parent } => {
                chain.clear();
                chain.push(kind);
                let mut fp = forward_parent;
                while let Some(j) = fp {
                    match events[j as usize] {
                        Event::Start { kind: Some(k), forward_parent: next } => {
                            chain.push(k);
                            events[j as usize] = Event::Start { kind: None, forward_parent: None };
                            fp = next;
                        }
                        e => b.bug(None, format!("event {i}: forward_parent {j} points to {e:?}, not to a Start")),
                    }
                }
                b.waiting.extend(chain.iter().rev());
                if b.stack.is_empty() {
                    b.open_waiting();
                }
            }
            Event::Token(t) => {
                if t < b.next_tok || t as usize >= b.tokens.len() {
                    b.bug(Some(t), format!("event {i} consumes token {t}, already placed or past the end"));
                }
                b.attach_until(t);
                b.open_waiting();
                b.attach(t);
            }
            Event::Finish { complete } => {
                b.open_waiting();
                if b.stack.len() == 1 {
                    b.attach_until(b.tokens.len() as u32);
                }
                b.close(complete);
            }
        }
    }
    if !b.stack.is_empty() || !b.waiting.is_empty() {
        b.bug(None, "the events leave nodes open".to_string());
    }
    let (nodes, children, token_parent) = (b.nodes, b.children, b.token_parent);
    Cst { tokens, nodes, children, token_parent }
}

struct Builder<'t> {
    nodes: Vec<NodeData>,
    children: Vec<Elem>,
    token_parent: Vec<NodeId>,
    /// Open nodes with the children gathered so far.
    stack: Vec<(NodeId, Vec<Elem>)>,
    /// Nodes that opened and wait for their first token, outermost first.
    waiting: Vec<NodeKind>,
    next_tok: u32,
    tokens: &'t [Token],
}

impl Builder<'_> {
    /// An internal error at token `t` (or at the next token to place).
    fn bug(&self, t: Option<u32>, message: String) -> ! {
        let at = t.unwrap_or(self.next_tok) as usize;
        let span = self.tokens.get(at).or(self.tokens.last()).map(|t| t.span);
        onsa_diag::internal::bug(span, format!("building the CST: {message}"))
    }

    fn open_waiting(&mut self) {
        for kind in std::mem::take(&mut self.waiting) {
            let id = NodeId(self.nodes.len() as u32);
            let parent = self.stack.last().map(|(p, _)| *p);
            self.nodes.push(NodeData { kind, parent, children: 0..0, tokens: 0..0, complete: true });
            if let Some((_, kids)) = self.stack.last_mut() {
                kids.push(Elem::Node(id));
            }
            self.stack.push((id, Vec::new()));
        }
    }

    fn attach(&mut self, t: u32) {
        let Some((id, kids)) = self.stack.last_mut() else {
            self.bug(Some(t), format!("token {t} comes outside the root"));
        };
        kids.push(Elem::Token(TokenIdx(t)));
        self.token_parent[t as usize] = *id;
        self.next_tok = t + 1;
    }

    /// Attach the tokens not attached yet before `end` to the innermost open node.
    fn attach_until(&mut self, end: u32) {
        while self.next_tok < end.min(self.tokens.len() as u32) {
            self.attach(self.next_tok);
        }
    }

    fn close(&mut self, complete: bool) {
        let Some((id, kids)) = self.stack.pop() else {
            self.bug(None, "a Finish without an open node".to_string());
        };
        let start = self.children.len() as u32;
        let first = kids.iter().find_map(|e| match *e {
            Elem::Token(t) => Some(t.0),
            Elem::Node(n) => {
                let r = &self.nodes[n.index()].tokens;
                (r.start < r.end).then_some(r.start)
            }
        });
        let last = kids.iter().rev().find_map(|e| match *e {
            Elem::Token(t) => Some(t.0 + 1),
            Elem::Node(n) => {
                let r = &self.nodes[n.index()].tokens;
                (r.start < r.end).then_some(r.end)
            }
        });
        self.children.extend(kids);
        let end = self.children.len() as u32;
        let next = self.next_tok;
        let node = &mut self.nodes[id.index()];
        node.children = start..end;
        node.tokens = match (first, last) {
            (Some(a), Some(b)) => a..b,
            _ => next..next,
        };
        node.complete = complete;
    }
}

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl TokenIdx {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

// ---------------------------------------------------------------- queries

impl Cst {
    pub fn root(&self) -> NodeId {
        NodeId(0)
    }

    /// All tokens of the lexer, in source order.
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    pub fn token(&self, t: TokenIdx) -> Token {
        self.tokens[t.index()]
    }

    pub fn kind(&self, n: NodeId) -> NodeKind {
        self.nodes[n.index()].kind
    }

    /// False when a syntax error stopped the parser inside this node.
    pub fn is_complete(&self, n: NodeId) -> bool {
        self.nodes[n.index()].complete
    }

    pub fn parent(&self, n: NodeId) -> Option<NodeId> {
        self.nodes[n.index()].parent
    }

    /// The node that holds the token as a child.
    pub fn token_parent(&self, t: TokenIdx) -> NodeId {
        self.token_parent[t.index()]
    }

    pub fn children(&self, n: NodeId) -> &[Elem] {
        let r = &self.nodes[n.index()].children;
        &self.children[r.start as usize..r.end as usize]
    }

    pub fn child_nodes(&self, n: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.children(n).iter().filter_map(|e| match *e {
            Elem::Node(c) => Some(c),
            Elem::Token(_) => None,
        })
    }

    /// The tokens that are direct children of `n` and not trivia.
    pub fn child_tokens(&self, n: NodeId) -> impl Iterator<Item = TokenIdx> + '_ {
        self.children(n).iter().filter_map(move |e| match *e {
            Elem::Token(t) if !self.tokens[t.index()].kind.is_trivia() => Some(t),
            _ => None,
        })
    }

    /// The tokens of the subtree, trivia included.
    pub fn token_range(&self, n: NodeId) -> Range<usize> {
        let r = &self.nodes[n.index()].tokens;
        r.start as usize..r.end as usize
    }

    /// The first and the last token of the subtree that are not trivia.
    pub fn significant_tokens(&self, n: NodeId) -> Option<(TokenIdx, TokenIdx)> {
        let r = self.token_range(n);
        let first = r.clone().find(|&i| !self.tokens[i].kind.is_trivia())?;
        let last = r.rev().find(|&i| !self.tokens[i].kind.is_trivia())?;
        Some((TokenIdx(first as u32), TokenIdx(last as u32)))
    }

    /// From the first to the last token of the subtree that is not trivia:
    /// the span of the AST node made from it. An empty node, or one of
    /// trivia only, gets the empty span where it is.
    pub fn span(&self, n: NodeId) -> Span {
        match self.significant_tokens(n) {
            Some((a, b)) => Span::new(self.file(), self.tokens[a.index()].span.start, self.tokens[b.index()].span.end),
            None => {
                let r = self.token_range(n);
                let at = self.tokens.get(r.start).map_or(0, |t| t.span.start);
                Span::new(self.file(), at, at)
            }
        }
    }

    /// The span of every token of the subtree, trivia included.
    pub fn full_span(&self, n: NodeId) -> Span {
        let r = self.token_range(n);
        if r.is_empty() {
            return self.span(n);
        }
        Span::new(self.file(), self.tokens[r.start].span.start, self.tokens[r.end - 1].span.end)
    }

    fn file(&self) -> FileId {
        self.tokens.last().map_or(FileId(0), |t| t.span.file)
    }

    /// The token that holds byte `offset` (the `Eof` token at the end).
    pub fn token_at(&self, offset: u32) -> TokenIdx {
        let i = self.tokens.partition_point(|t| t.span.end <= offset);
        TokenIdx(i.min(self.tokens.len() - 1) as u32)
    }

    /// The nodes from `n` up to the root.
    pub fn ancestors(&self, n: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        std::iter::successors(Some(n), move |&m| self.parent(m))
    }

    /// The nodes whose span ([`Cst::span`]) contains `span`, from the
    /// innermost outward to the root. For the positions of the parts of the
    /// AST that are not arena nodes (`Ident`, `Path`, `Attr`, `Arg`, `Param`,
    /// `MatchArm`, `Field`, `Variant`, ...). Nodes with the same span (an
    /// `Arg` and its expression, an `Item` and its declaration, an
    /// `ExprStmt` and its expression) all come, the inner first: a caller
    /// that wants a kind takes the first of that kind.
    pub fn covering_nodes(&self, span: Span) -> impl Iterator<Item = NodeId> + '_ {
        let t = self.token_at(span.start);
        self.ancestors(self.token_parent(t)).filter(move |&n| {
            let s = self.span(n);
            s.start <= span.start && span.end <= s.end
        })
    }

    /// The innermost node whose span contains `span` (the first of
    /// [`Cst::covering_nodes`]; of nodes with the same span, the inner one).
    pub fn covering_node(&self, span: Span) -> NodeId {
        self.covering_nodes(span).next().unwrap_or(self.root())
    }

    /// The innermost node of `kind` whose span contains `span`.
    pub fn covering_node_of(&self, span: Span, kind: NodeKind) -> Option<NodeId> {
        self.covering_nodes(span).find(|&n| self.kind(n) == kind)
    }

    /// The tokens that lie inside `span`, trivia included: a token is inside
    /// when `span.start <= start` and `end <= span.end`. So the zero-width
    /// `Eof` is inside a span that reaches the end of the file
    /// (`tokens_in(span(root))` holds every token from the first that is not
    /// trivia to `Eof`), and an empty span between two tokens holds none.
    /// Because of the zero-width `Eof`, the tokens of a span that ends at
    /// the end of the file (the last item of a file without a final newline)
    /// include `Eof`, and those of the same item followed by a newline do not.
    pub fn tokens_in(&self, span: Span) -> Range<usize> {
        let a = self.tokens.partition_point(|t| t.span.start < span.start);
        let b = self.tokens.partition_point(|t| t.span.end <= span.end);
        a..b.max(a)
    }

    /// The number of nodes on the longest path from `n` down (1 for a node
    /// without child nodes). Without recursion.
    pub fn height(&self, n: NodeId) -> u32 {
        let mut best = 0;
        let mut stack = vec![(n, 1u32)];
        while let Some((m, d)) = stack.pop() {
            best = best.max(d);
            stack.extend(self.child_nodes(m).map(|c| (c, d + 1)));
        }
        best
    }

    /// The tokens of the tree, walked leaf by leaf (without recursion).
    pub fn leaves(&self) -> Vec<TokenIdx> {
        let mut out = Vec::with_capacity(self.tokens.len());
        let mut stack: Vec<(NodeId, usize)> = vec![(self.root(), 0)];
        while let Some(top) = stack.last_mut() {
            let (n, i) = *top;
            let kids = self.children(n);
            if i == kids.len() {
                stack.pop();
                continue;
            }
            top.1 += 1;
            match kids[i] {
                Elem::Token(t) => out.push(t),
                Elem::Node(c) => stack.push((c, 0)),
            }
        }
        out
    }

    /// The text of the tree: the source of its leaves, in order. For a valid
    /// tree it is the source byte for byte (the round trip of R-86).
    pub fn text(&self, src: &str) -> String {
        let mut out = String::with_capacity(src.len());
        for t in self.leaves() {
            let s = self.tokens[t.index()].span;
            out.push_str(&src[s.start as usize..s.end as usize]);
        }
        out
    }

    /// Check the invariants of the tree: the tokens cover `src` without gap
    /// or overlap, every token is a leaf exactly once and in order, the
    /// parent links agree with the children, the token ranges of the nodes
    /// are the union of their children, the root holds the `Eof` token last.
    pub fn validate(&self, src: &str) -> Result<(), CstError> {
        let file = self.file();
        let at_token = |i: usize, message: String| CstError {
            span: self.tokens.get(i).map_or(Span::new(file, 0, 0), |t| t.span),
            message,
        };
        let mut at = 0u32;
        for (i, t) in self.tokens.iter().enumerate() {
            if t.span.start != at || t.span.end < t.span.start {
                let message =
                    format!("token {i} ({:?}) at {}..{}, expected to start at {at}", t.kind, t.span.start, t.span.end);
                return Err(CstError { span: Span::new(file, at, at.max(t.span.start)), message });
            }
            at = t.span.end;
        }
        if at as usize != src.len() {
            let message = format!("the tokens end at {at}, the source at {}", src.len());
            return Err(CstError { span: Span::new(file, at, src.len() as u32), message });
        }
        match self.tokens.last() {
            Some(t) if t.kind == TokenKind::Eof => {}
            _ => return Err(at_token(self.tokens.len().saturating_sub(1), "the last token is not Eof".into())),
        }
        if self.nodes.is_empty() || self.kind(self.root()) != NodeKind::SourceFile || self.parent(self.root()).is_some()
        {
            return Err(at_token(0, "the root is not a SourceFile".into()));
        }
        let leaves = self.leaves();
        if leaves.len() != self.tokens.len() || leaves.iter().enumerate().any(|(i, t)| t.index() != i) {
            let bad = leaves.iter().enumerate().find(|(i, t)| t.index() != *i).map(|(i, _)| i).unwrap_or(leaves.len());
            let message = format!("the leaves are not the tokens in order (first difference at leaf {bad})");
            return Err(at_token(bad, message));
        }
        match self.children(self.root()).last() {
            Some(Elem::Token(t)) if t.index() == self.tokens.len() - 1 => {}
            _ => return Err(at_token(self.tokens.len() - 1, "the root does not end with the Eof token".into())),
        }
        let mut seen = vec![false; self.nodes.len()];
        seen[0] = true;
        for n in 0..self.nodes.len() {
            let id = NodeId(n as u32);
            let r = &self.nodes[n].tokens;
            let first = r.start as usize;
            let mut lo = None;
            let mut hi = None;
            for e in self.children(id) {
                match *e {
                    Elem::Token(t) => {
                        if self.token_parent(t) != id {
                            return Err(at_token(t.index(), format!("token {} has a wrong parent", t.0)));
                        }
                        lo.get_or_insert(t.0);
                        hi = Some(t.0 + 1);
                    }
                    Elem::Node(c) => {
                        if self.parent(c) != Some(id) || std::mem::replace(&mut seen[c.index()], true) {
                            let at = self.nodes[c.index()].tokens.start as usize;
                            return Err(at_token(at, format!("node {} has a wrong parent", c.0)));
                        }
                        let cr = &self.nodes[c.index()].tokens;
                        if cr.start < cr.end {
                            lo.get_or_insert(cr.start);
                            hi = Some(cr.end);
                        }
                    }
                }
            }
            if let (Some(a), Some(b)) = (lo, hi)
                && (r.start != a || r.end != b)
            {
                let message =
                    format!("node {n} ({:?}) has the token range {r:?}, its children {a}..{b}", self.kind(id));
                return Err(at_token(first.min(a as usize), message));
            }
        }
        if let Some(n) = seen.iter().position(|s| !s) {
            let at = self.nodes[n].tokens.start as usize;
            return Err(at_token(at, format!("node {n} is not a child of any node")));
        }
        Ok(())
    }

    /// The tree as indented lines (`onsa dump --cst --tree`): nodes as
    /// `Kind@start..end` (`!` when incomplete), tokens as `Kind@start..end "text"`.
    pub fn tree(&self, src: &str) -> String {
        let mut out = String::new();
        let mut stack: Vec<(NodeId, usize)> = vec![(self.root(), 0)];
        let s = self.full_span(self.root());
        out.push_str(&format!("{}@{}..{}\n", self.kind(self.root()).name(), s.start, s.end));
        while let Some(top) = stack.last_mut() {
            let (n, i) = *top;
            let kids = self.children(n);
            if i == kids.len() {
                stack.pop();
                continue;
            }
            top.1 += 1;
            let depth = stack.len();
            let indent = "  ".repeat(depth);
            match kids[i] {
                Elem::Token(t) => {
                    let tok = self.tokens[t.index()];
                    let text = &src[tok.span.start as usize..tok.span.end as usize];
                    out.push_str(&format!("{indent}{:?}@{}..{} {:?}\n", tok.kind, tok.span.start, tok.span.end, text));
                }
                Elem::Node(c) => {
                    let s = self.full_span(c);
                    let mark = if self.is_complete(c) { "" } else { "!" };
                    out.push_str(&format!("{indent}{}{mark}@{}..{}\n", self.kind(c).name(), s.start, s.end));
                    stack.push((c, 0));
                }
            }
        }
        out
    }
}
