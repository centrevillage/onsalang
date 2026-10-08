//! From the CST to the AST (R-86): one stage, after the parser.
//!
//! The parser has made every decision (which construct, which diagnostics);
//! the node kinds record them. This stage reads the tree: it takes the nodes
//! and tokens in their slots, reads the values of the literals (one function
//! each), and makes the AST nodes, children before parents. It reports no
//! diagnostic. An item a syntax error stopped is made from what was read
//! ([`Lower::failed_item`], S-59, R-71): its name and the parts of its heading
//! that were read whole, with [`Failed`] saying whether the heading was read;
//! a part that was not read is [`ExprKind::Error`] or [`TypeKind::Error`]. An
//! item whose name was not read has no AST (a unit of `crate::units` only).
//!
//! The span of an AST node is the span of the CST node it is made from
//! ([`Cst::span`]), except three spans kept from the parser before the CST
//! (marked `SPAN-QUIRK` below): an attribute written `#[...]` ends before
//! the `]`, the condition `true` made for `loop` has the span of `loop`, the
//! literal of a negative const argument has the span of its digits.

use onsa_diag::Span;

use crate::ast::*;
use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// From each AST node to the CST node it was made from (same indices as the
/// arenas of [`Ast`]). The parts of the AST that are not arena nodes (`Ident`,
/// `Path`, `Param`, ...) are found with [`Cst::covering_nodes`].
///
/// The node pointed at is not always a node of the same sort: the condition
/// `true` made for `loop` points at the `LoopStmt`; the literal and the
/// negation of a const argument and its type all point at the `ConstArg`; an
/// expression written `&x` (E0020) is the expression `x` and points at the
/// node of `x` (the `RefExpr` around it makes no AST node).
/// The parts that are not arena nodes may come from more than one kind too:
/// an `Attr` from an `Attr` or a `HashAttr` node.
#[derive(Debug, Default, Clone)]
pub struct AstMap {
    pub items: Vec<NodeId>,
    pub exprs: Vec<NodeId>,
    pub stmts: Vec<NodeId>,
    pub types: Vec<NodeId>,
    pub pats: Vec<NodeId>,
}

/// Make the AST of `cst` (the source is `text`).
pub(crate) fn lower(cst: &Cst, text: &str) -> (Ast, AstMap) {
    let mut l = Lower { cst, text, ast: Ast::default(), map: AstMap::default() };
    let root = cst.root();
    for n in cst.child_nodes(root) {
        if cst.kind(n) == NodeKind::Item
            && let Some(id) = l.any_item(n)
        {
            l.ast.root.push(id);
        }
    }
    (l.ast, l.map)
}

/// What an AST node made from a CST node of this kind is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Class {
    Expr,
    Type,
    Pat,
    Other,
}

pub(crate) fn class(kind: NodeKind) -> Class {
    use NodeKind::*;
    match kind {
        Literal | LeadingDotFloat | HoleExpr | PathExpr | ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | Block
        | IfExpr | MatchExpr | ClosureExpr | HandleExpr | UnsafeExpr | ParExpr | MoveExpr | BinaryExpr | RangeExpr
        | CastExpr | PrefixExpr | RefExpr | CallExpr | FieldExpr | TupleIndexExpr | IndexExpr | TryExpr | StructLit => {
            Class::Expr
        }
        PathType | ConstArg | UnitType | TupleType | ArrayType | FnType => Class::Type,
        WildPat | LitPat | NegLitPat | TuplePat | BindPat | PathPat | TupleStructPat | StructPat | OrPat => Class::Pat,
        SourceFile | Error | Name | Item | Docs | Attr | HashAttr | AttrArgs | AttrNamedArg | Vis | Fn | Flow
        | Struct | FieldList | Field | TupleStructBody | Enum | VariantList | Variant | VariantFields | TypeAlias
        | OpaqueType | Trait | Impl | Effect | Handler | Const | Use | UseTree | UseNames | Extern | Target | Test
        | ItemList | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList | Param | EffectRow
        | Path | TypeArgs | FnTypeParams | LetStmt | VarStmt | ForStmt | WhileStmt | LoopStmt | BreakStmt
        | ContinueStmt | ReturnStmt | AssertStmt | AssignStmt | ExprStmt | MatchArms | MatchArm | ArgList | Arg
        | StructLitFields | StructLitField | StructPatField => Class::Other,
    }
}

struct Lower<'a> {
    cst: &'a Cst,
    text: &'a str,
    ast: Ast,
    map: AstMap,
}

impl<'a> Lower<'a> {
    // ------------------------------------------------------------ reading the tree

    fn bug(&self, n: NodeId, what: &str) -> ! {
        onsa_diag::internal::bug(
            Some(self.cst.span(n)),
            format!("the CST node {} does not have {what}", self.cst.kind(n).name()),
        )
    }

    fn text_of(&self, t: TokenIdx) -> &'a str {
        let s = self.cst.token(t).span;
        &self.text[s.start as usize..s.end as usize]
    }

    fn kind_of(&self, t: TokenIdx) -> TokenKind {
        self.cst.token(t).kind
    }

    fn ident(&self, t: TokenIdx) -> Ident {
        Ident { name: self.text_of(t).to_string(), span: self.cst.token(t).span }
    }

    fn span(&self, n: NodeId) -> Span {
        self.cst.span(n)
    }

    fn nodes(&self, n: NodeId) -> Vec<NodeId> {
        self.cst.child_nodes(n).collect()
    }

    fn toks(&self, n: NodeId) -> Vec<TokenIdx> {
        self.cst.child_tokens(n).collect()
    }

    fn has(&self, n: NodeId, kind: TokenKind) -> bool {
        self.cst.child_tokens(n).any(|t| self.kind_of(t) == kind)
    }

    fn tok(&self, n: NodeId, kind: TokenKind) -> Option<TokenIdx> {
        self.cst.child_tokens(n).find(|&t| self.kind_of(t) == kind)
    }

    /// The first child node of `kind`.
    fn child(&self, n: NodeId, kind: NodeKind) -> Option<NodeId> {
        self.cst.child_nodes(n).find(|&c| self.cst.kind(c) == kind)
    }

    fn need(&self, n: NodeId, kind: NodeKind) -> NodeId {
        self.child(n, kind).unwrap_or_else(|| self.bug(n, kind.name()))
    }

    fn of_class(&self, n: NodeId, c: Class) -> Vec<NodeId> {
        self.cst.child_nodes(n).filter(|&k| class(self.cst.kind(k)) == c).collect()
    }

    /// The name a declaration introduces: the token of its `Name` node.
    fn name(&self, n: NodeId) -> Ident {
        self.ident(self.name_token(n))
    }

    fn name_token(&self, n: NodeId) -> TokenIdx {
        let name = self.need(n, NodeKind::Name);
        self.toks(name).first().copied().unwrap_or_else(|| self.bug(name, "a token"))
    }

    /// The identifier token of a node that holds one (an attribute name, a
    /// key, the field of a struct literal or pattern).
    fn first_ident(&self, n: NodeId) -> Ident {
        let t = self.tok(n, TokenKind::Ident).unwrap_or_else(|| self.bug(n, "an identifier"));
        self.ident(t)
    }

    fn first_type(&mut self, n: NodeId) -> Option<TypeId> {
        let c = self.of_class(n, Class::Type).into_iter().next()?;
        Some(self.ty(c))
    }

    fn first_expr(&self, n: NodeId) -> Option<NodeId> {
        self.of_class(n, Class::Expr).into_iter().next()
    }

    fn need_expr(&mut self, n: NodeId) -> ExprId {
        let c = self.first_expr(n).unwrap_or_else(|| self.bug(n, "an expression"));
        self.expr(c)
    }

    // ------------------------------------------------------------ adding

    fn add_item(&mut self, n: NodeId, item: Item) -> ItemId {
        self.map.items.push(n);
        self.ast.add_item(item)
    }

    fn add_expr(&mut self, n: NodeId, span: Span, kind: ExprKind) -> ExprId {
        self.map.exprs.push(n);
        self.ast.add_expr(Expr { span, kind })
    }

    fn add_stmt(&mut self, n: NodeId, kind: StmtKind) -> StmtId {
        self.map.stmts.push(n);
        let span = self.span(n);
        self.ast.add_stmt(Stmt { span, kind })
    }

    fn add_type(&mut self, n: NodeId, kind: TypeKind) -> TypeId {
        self.map.types.push(n);
        let span = self.span(n);
        self.ast.add_type(TypeExpr { span, kind })
    }

    fn add_pat(&mut self, n: NodeId, kind: PatKind) -> PatId {
        self.map.pats.push(n);
        let span = self.span(n);
        self.ast.add_pat(Pat { span, kind })
    }

    // ------------------------------------------------------------ items

    /// An `Item` node: the item, or the failed item when a syntax error
    /// stopped it (`None` when not even its name was read).
    fn any_item(&mut self, n: NodeId) -> Option<ItemId> {
        if self.cst.is_complete(n) { Some(self.item(n)) } else { self.failed_item(n) }
    }

    fn item(&mut self, n: NodeId) -> ItemId {
        let mut doc = Vec::new();
        let mut attrs = Vec::new();
        let mut vis = Vis::Private;
        let mut decl = None;
        for c in self.nodes(n) {
            match self.cst.kind(c) {
                // The doc comments the parser took for the item.
                NodeKind::Docs => {
                    for e in self.cst.children(c) {
                        if let Elem::Token(t) = *e
                            && self.kind_of(t) == TokenKind::DocComment
                        {
                            doc.push(self.cst.token(t).span);
                        }
                    }
                }
                NodeKind::Attr | NodeKind::HashAttr => attrs.push(self.attr(c)),
                NodeKind::Vis => vis = self.vis(c),
                _ => decl = Some(c),
            }
        }
        let decl = decl.unwrap_or_else(|| self.bug(n, "a declaration"));
        let kind = self.item_kind(decl);
        let span = self.span(n);
        self.add_item(n, Item { span, doc, attrs, vis, kind, failed: None })
    }

    /// An item a syntax error stopped (spec §18.1, S-59): its name and the
    /// parts of its heading that were read whole stay, so that the other
    /// units see it (R-71). The attributes and the visibility are kept when
    /// they were read whole. `None` when its name was not read, and for a
    /// failed `impl` heading and `use` (R-180: W5-04 and W4-03).
    fn failed_item(&mut self, n: NodeId) -> Option<ItemId> {
        let mut doc = Vec::new();
        let mut attrs = Vec::new();
        let mut vis = Vis::Private;
        let mut decl = None;
        for c in self.nodes(n) {
            let complete = self.cst.is_complete(c);
            match self.cst.kind(c) {
                NodeKind::Docs => {
                    for e in self.cst.children(c) {
                        if let Elem::Token(t) = *e
                            && self.kind_of(t) == TokenKind::DocComment
                        {
                            doc.push(self.cst.token(t).span);
                        }
                    }
                }
                NodeKind::Attr | NodeKind::HashAttr if complete => attrs.push(self.attr(c)),
                NodeKind::Vis if complete => vis = self.vis(c),
                NodeKind::Attr | NodeKind::HashAttr | NodeKind::Vis | NodeKind::Error => {}
                _ => decl = Some(c),
            }
        }
        let (kind, failed) = self.failed_kind(decl?)?;
        let span = self.span(n);
        Some(self.add_item(n, Item { span, doc, attrs, vis, kind, failed: Some(failed) }))
    }

    /// The name of a declaration when it was read whole.
    fn read_name(&self, n: NodeId) -> Option<Ident> {
        let name = self.child(n, NodeKind::Name)?;
        if !self.cst.is_complete(name) {
            return None;
        }
        self.toks(name).first().map(|&t| self.ident(t))
    }

    /// The generic parameters of a failed declaration; `heading` turns false
    /// when they were cut.
    fn failed_generics(&mut self, n: NodeId, heading: &mut bool) -> Vec<GenericParam> {
        match self.child(n, NodeKind::GenericParams) {
            Some(g) if !self.cst.is_complete(g) => {
                *heading = false;
                Vec::new()
            }
            _ => self.generics(n),
        }
    }

    /// The first type of a failed node (a return type, a `const`'s type);
    /// `heading` turns false when a type there was cut.
    fn failed_type(&mut self, n: NodeId, heading: &mut bool) -> Option<TypeId> {
        let types = self.of_class(n, Class::Type);
        if types.iter().any(|&t| !self.cst.is_complete(t)) {
            *heading = false;
            return None;
        }
        types.first().map(|&t| self.ty(t))
    }

    /// The type a syntax error left unread in the failed node `n`.
    fn error_type(&mut self, n: NodeId) -> TypeId {
        self.add_type(n, TypeKind::Error)
    }

    /// A body, a value: lowered when the node was finished, else an error.
    fn failed_expr(&mut self, n: NodeId) -> ExprId {
        if self.cst.is_complete(n) {
            if self.cst.kind(n) == NodeKind::Block { self.block(n) } else { self.expr(n) }
        } else {
            let span = self.span(n);
            self.add_expr(n, span, ExprKind::Error)
        }
    }

    /// The members of a failed declaration with a list of them: the members
    /// read whole and the failed ones whose name was read.
    fn failed_members(&mut self, n: NodeId, heading: &mut bool) -> Vec<ItemId> {
        match self.child(n, NodeKind::ItemList) {
            Some(_) => self.item_list(n),
            None => {
                *heading = false;
                Vec::new()
            }
        }
    }

    /// The parameters of a failed declaration; `heading` turns false when the
    /// list was cut or not reached.
    fn failed_params(&mut self, n: NodeId, heading: &mut bool) -> Vec<Param> {
        match self.child(n, NodeKind::ParamList) {
            Some(p) if self.cst.is_complete(p) => self.params(p),
            _ => {
                *heading = false;
                Vec::new()
            }
        }
    }

    /// The kind of a failed declaration node and how far it was read.
    fn failed_kind(&mut self, d: NodeId) -> Option<(ItemKind, Failed)> {
        if self.cst.is_complete(d) {
            return Some((self.item_kind(d), Failed::Unit));
        }
        let mut heading = true;
        let kind = match self.cst.kind(d) {
            NodeKind::Fn => {
                let rt = self.has(d, TokenKind::KwRt);
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let params = self.failed_params(d, &mut heading);
                let ret = self.failed_type(d, &mut heading);
                let effects = match self.child(d, NodeKind::EffectRow) {
                    Some(e) if self.cst.is_complete(e) => Some(self.effect_row(e)),
                    Some(_) => {
                        heading = false;
                        None
                    }
                    None => None,
                };
                // A body that was not reached: the heading may go on (`uses`).
                let body = match self.child(d, NodeKind::Block) {
                    Some(b) => Some(self.failed_expr(b)),
                    None => {
                        heading = false;
                        None
                    }
                };
                ItemKind::Fn(FnDecl { rt, name, generics, params, ret, effects, body })
            }
            NodeKind::Flow => {
                let name = self.read_name(d)?;
                let params = self.failed_params(d, &mut heading);
                let ret = match self.failed_type(d, &mut heading) {
                    Some(t) => t,
                    None => {
                        heading = false;
                        self.error_type(d)
                    }
                };
                let body = match self.child(d, NodeKind::Block) {
                    Some(b) => self.failed_expr(b),
                    None => {
                        heading = false;
                        let span = self.span(d);
                        self.add_expr(d, span, ExprKind::Error)
                    }
                };
                ItemKind::Flow(FlowDecl { name, params, ret, body })
            }
            NodeKind::Struct => {
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let kind = if let Some(b) = self.child(d, NodeKind::TupleStructBody) {
                    let ty = match self.of_class(b, Class::Type).first() {
                        Some(&t) if self.cst.is_complete(t) => self.ty(t),
                        _ => self.error_type(b),
                    };
                    StructKind::Tuple(ty)
                } else if let Some(list) = self.child(d, NodeKind::FieldList) {
                    let fields = self.nodes(list);
                    let fields =
                        fields.into_iter().filter(|&f| self.cst.is_complete(f)).map(|f| self.field(f)).collect();
                    StructKind::Named(fields)
                } else {
                    heading = false;
                    StructKind::Named(Vec::new())
                };
                ItemKind::Struct(StructDecl { name, generics, kind })
            }
            NodeKind::Enum => {
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let variants = match self.child(d, NodeKind::VariantList) {
                    Some(list) => {
                        let vs = self.nodes(list);
                        vs.into_iter().filter(|&v| self.cst.is_complete(v)).map(|v| self.variant(v)).collect()
                    }
                    None => {
                        heading = false;
                        Vec::new()
                    }
                };
                ItemKind::Enum(EnumDecl { name, generics, variants })
            }
            NodeKind::TypeAlias | NodeKind::OpaqueType => {
                let name = self.read_name(d)?;
                let ty = match self.failed_type(d, &mut heading) {
                    Some(t) => t,
                    None => {
                        heading = false;
                        self.error_type(d)
                    }
                };
                ItemKind::TypeAlias { name, ty }
            }
            NodeKind::Trait => {
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let items = self.failed_members(d, &mut heading);
                ItemKind::Trait(TraitDecl { name, generics, items })
            }
            NodeKind::Impl => {
                // R-180: the members of an `impl` whose heading was cut are not
                // seen (the type they belong to is not known; W5-04).
                let g = self.child(d, NodeKind::GenericParams);
                if g.is_some_and(|g| !self.cst.is_complete(g)) || self.child(d, NodeKind::ItemList).is_none() {
                    return None;
                }
                let types = self.of_class(d, Class::Type);
                let want = if self.has(d, TokenKind::KwFor) { 2 } else { 1 };
                if types.len() != want || types.iter().any(|&t| !self.cst.is_complete(t)) {
                    return None;
                }
                let generics = self.generics(d);
                let (trait_, self_ty) = if want == 2 {
                    let path = self.child(types[0], NodeKind::Path)?;
                    (Some(self.path(path)), self.ty(types[1]))
                } else {
                    (None, self.ty(types[0]))
                };
                let items = self.item_list(d);
                ItemKind::Impl(ImplDecl { generics, trait_, self_ty, items })
            }
            NodeKind::Effect => {
                let blocking = self.has(d, TokenKind::KwBlocking);
                let name = self.read_name(d)?;
                let ops = self.failed_members(d, &mut heading);
                ItemKind::Effect(EffectDecl { blocking, name, ops })
            }
            NodeKind::Handler => {
                let name = self.read_name(d)?;
                let params = match self.child(d, NodeKind::ParamList) {
                    Some(p) if self.cst.is_complete(p) => self.params(p),
                    Some(_) => return None,
                    None => Vec::new(),
                };
                let effect = self.child(d, NodeKind::Path).filter(|&p| self.cst.is_complete(p))?;
                let effect = self.path(effect);
                let items = self.failed_members(d, &mut heading);
                ItemKind::Handler(HandlerDecl { name, params, effect, items })
            }
            NodeKind::Const => {
                let name = self.read_name(d)?;
                let ty = match self.failed_type(d, &mut heading) {
                    Some(t) => t,
                    None => {
                        heading = false;
                        self.error_type(d)
                    }
                };
                // The parser finishes a `const` right after its value: a
                // failed one never has a finished value.
                let at = self.first_expr(d).unwrap_or(d);
                let span = self.span(at);
                let value = Some(self.add_expr(at, span, ExprKind::Error));
                ItemKind::Const(ConstDecl { name, ty, value })
            }
            NodeKind::Extern => {
                let strs: Vec<TokenIdx> =
                    self.toks(d).into_iter().filter(|&t| self.kind_of(t) == TokenKind::Str).collect();
                if strs.len() != 2 {
                    return None;
                }
                let abi = self.str_lit(strs[0]);
                let lib = self.str_lit(strs[1]);
                let items = self.failed_members(d, &mut heading);
                ItemKind::Extern(ExternDecl { abi, lib, items })
            }
            NodeKind::Target => {
                let inner = self.nodes(d).into_iter().next()?;
                let (kind, failed) = self.failed_kind(inner)?;
                return Some((ItemKind::Target(Box::new(kind)), failed));
            }
            NodeKind::Test => {
                let name = self.tok(d, TokenKind::Str)?;
                let name = self.str_lit(name);
                let body = match self.child(d, NodeKind::Block) {
                    Some(b) => self.failed_expr(b),
                    None => {
                        heading = false;
                        let span = self.span(d);
                        self.add_expr(d, span, ExprKind::Error)
                    }
                };
                ItemKind::Test { name, body }
            }
            // `use` (R-180: W4-03) and what is not a declaration.
            _ => return None,
        };
        Some((kind, if heading { Failed::Body } else { Failed::Heading }))
    }

    fn vis(&self, n: NodeId) -> Vis {
        if self.has(n, TokenKind::LParen) { Vis::Pkg } else { Vis::Pub }
    }

    fn attr(&mut self, n: NodeId) -> Attr {
        let name = self.first_ident(n);
        let mut args = Vec::new();
        if let Some(a) = self.child(n, NodeKind::AttrArgs) {
            for e in self.cst.children(a).to_vec() {
                match e {
                    Elem::Node(c) => match self.cst.kind(c) {
                        NodeKind::AttrNamedArg => {
                            let key = self.first_ident(c);
                            let value = self.need_expr(c);
                            args.push(AttrArg::Named { key, value });
                        }
                        NodeKind::Path => args.push(AttrArg::Path(self.path(c))),
                        _ => self.bug(a, "an attribute argument"),
                    },
                    Elem::Token(t) if self.kind_of(t) == TokenKind::Str => args.push(AttrArg::Str(self.str_lit(t))),
                    Elem::Token(_) => {}
                }
            }
        }
        let span = if self.cst.kind(n) == NodeKind::HashAttr {
            // SPAN-QUIRK: `#[name(...)]` (E0020) ends before the `]`, as the
            // parser before the CST gave it (W3-08 revisits attributes).
            let before_close = self.cst.token_range(n).rev().find(|&i| {
                let k = self.cst.tokens()[i].kind;
                !k.is_trivia() && k != TokenKind::RBracket
            });
            let s = self.span(n);
            let end = before_close.map_or(s.end, |i| self.cst.tokens()[i].span.end);
            Span::new(s.file, s.start, end)
        } else {
            self.span(n)
        };
        Attr { name, args, span }
    }

    fn item_kind(&mut self, n: NodeId) -> ItemKind {
        match self.cst.kind(n) {
            NodeKind::Fn => ItemKind::Fn(self.fn_decl(n)),
            NodeKind::Flow => {
                let name = self.name(n);
                let params = self.params(self.need(n, NodeKind::ParamList));
                let ret = self.first_type(n).unwrap_or_else(|| self.bug(n, "a return type"));
                let body = self.block(self.need(n, NodeKind::Block));
                ItemKind::Flow(FlowDecl { name, params, ret, body })
            }
            NodeKind::Struct => {
                let name = self.name(n);
                let generics = self.generics(n);
                let kind = if let Some(b) = self.child(n, NodeKind::TupleStructBody) {
                    StructKind::Tuple(self.first_type(b).unwrap_or_else(|| self.bug(b, "a type")))
                } else {
                    let list = self.need(n, NodeKind::FieldList);
                    let fields = self.nodes(list).into_iter().map(|f| self.field(f)).collect();
                    StructKind::Named(fields)
                };
                ItemKind::Struct(StructDecl { name, generics, kind })
            }
            NodeKind::Enum => {
                let name = self.name(n);
                let generics = self.generics(n);
                let list = self.need(n, NodeKind::VariantList);
                let variants = self.nodes(list).into_iter().map(|v| self.variant(v)).collect();
                ItemKind::Enum(EnumDecl { name, generics, variants })
            }
            NodeKind::TypeAlias => {
                let name = self.name(n);
                let ty = self.first_type(n).unwrap_or_else(|| self.bug(n, "a type"));
                ItemKind::TypeAlias { name, ty }
            }
            NodeKind::OpaqueType => ItemKind::OpaqueType { name: self.name(n) },
            NodeKind::Trait => {
                let name = self.name(n);
                let generics = self.generics(n);
                let items = self.item_list(n);
                ItemKind::Trait(TraitDecl { name, generics, items })
            }
            NodeKind::Impl => {
                let generics = self.generics(n);
                let types = self.of_class(n, Class::Type);
                let (trait_, self_ty) = if self.has(n, TokenKind::KwFor) {
                    let path = self.need(types[0], NodeKind::Path);
                    (Some(self.path(path)), self.ty(types[1]))
                } else {
                    (None, self.ty(types[0]))
                };
                let items = self.item_list(n);
                ItemKind::Impl(ImplDecl { generics, trait_, self_ty, items })
            }
            NodeKind::Effect => {
                let blocking = self.has(n, TokenKind::KwBlocking);
                let name = self.name(n);
                let ops = self.item_list(n);
                ItemKind::Effect(EffectDecl { blocking, name, ops })
            }
            NodeKind::Handler => {
                let name = self.name(n);
                let params = match self.child(n, NodeKind::ParamList) {
                    Some(p) => self.params(p),
                    None => Vec::new(),
                };
                let effect = self.path(self.need(n, NodeKind::Path));
                let items = self.item_list(n);
                ItemKind::Handler(HandlerDecl { name, params, effect, items })
            }
            NodeKind::Const => {
                let name = self.name(n);
                let ty = self.first_type(n).unwrap_or_else(|| self.bug(n, "a type"));
                let value = self.first_expr(n).map(|e| self.expr(e));
                ItemKind::Const(ConstDecl { name, ty, value })
            }
            NodeKind::Use => {
                let tree = self.need(n, NodeKind::UseTree);
                let segments = self
                    .toks(tree)
                    .into_iter()
                    .filter(|&t| !matches!(self.kind_of(t), TokenKind::Dot | TokenKind::ColonColon))
                    .map(|t| self.ident(t))
                    .collect();
                let path = Path { segments, span: self.span(tree) };
                let names = self.child(tree, NodeKind::UseNames).map(|u| {
                    self.toks(u)
                        .into_iter()
                        .filter(|&t| self.kind_of(t) == TokenKind::Ident)
                        .map(|t| self.ident(t))
                        .collect()
                });
                ItemKind::Use(UseDecl { path, names })
            }
            NodeKind::Extern => {
                let strs: Vec<TokenIdx> =
                    self.toks(n).into_iter().filter(|&t| self.kind_of(t) == TokenKind::Str).collect();
                if strs.len() != 2 {
                    self.bug(n, "an ABI and a library");
                }
                let abi = self.str_lit(strs[0]);
                let lib = self.str_lit(strs[1]);
                let items = self.item_list(n);
                ItemKind::Extern(ExternDecl { abi, lib, items })
            }
            NodeKind::Target => {
                let inner = self.nodes(n).into_iter().next().unwrap_or_else(|| self.bug(n, "a declaration"));
                ItemKind::Target(Box::new(self.item_kind(inner)))
            }
            NodeKind::Test => {
                let name = self.tok(n, TokenKind::Str).unwrap_or_else(|| self.bug(n, "a name"));
                let name = self.str_lit(name);
                let body = self.block(self.need(n, NodeKind::Block));
                ItemKind::Test { name, body }
            }
            _ => self.bug(n, "the kind of a declaration"),
        }
    }

    fn field(&mut self, f: NodeId) -> Field {
        let vis = self.child(f, NodeKind::Vis).map_or(Vis::Private, |v| self.vis(v));
        let name = self.name(f);
        let ty = self.first_type(f).unwrap_or_else(|| self.bug(f, "a type"));
        Field { vis, name, ty, span: self.span(f) }
    }

    fn variant(&mut self, v: NodeId) -> Variant {
        let name = self.name(v);
        let fields = match self.child(v, NodeKind::VariantFields) {
            Some(f) => self.of_class(f, Class::Type).into_iter().map(|t| self.ty(t)).collect(),
            None => Vec::new(),
        };
        Variant { name, fields, span: self.span(v) }
    }

    fn fn_decl(&mut self, n: NodeId) -> FnDecl {
        let rt = self.has(n, TokenKind::KwRt);
        let name = self.name(n);
        let generics = self.generics(n);
        let params = self.params(self.need(n, NodeKind::ParamList));
        let ret = self.first_type(n);
        let effects = self.child(n, NodeKind::EffectRow).map(|e| self.effect_row(e));
        let body = self.child(n, NodeKind::Block).map(|b| self.block(b));
        FnDecl { rt, name, generics, params, ret, effects, body }
    }

    /// The members of a declaration's list: the members read whole and the
    /// failed ones whose name was read (each member is a unit, S-59).
    fn item_list(&mut self, n: NodeId) -> Vec<ItemId> {
        let list = self.need(n, NodeKind::ItemList);
        let members: Vec<NodeId> =
            self.nodes(list).into_iter().filter(|&i| self.cst.kind(i) == NodeKind::Item).collect();
        members.into_iter().filter_map(|i| self.any_item(i)).collect()
    }

    fn generics(&mut self, n: NodeId) -> Vec<GenericParam> {
        let Some(g) = self.child(n, NodeKind::GenericParams) else {
            return Vec::new();
        };
        self.nodes(g)
            .into_iter()
            .map(|p| {
                let name = self.name(p);
                match self.cst.kind(p) {
                    NodeKind::TypeParam => {
                        let bounds = self
                            .of_kind(p, NodeKind::Bound)
                            .into_iter()
                            .map(|b| Bound {
                                relaxed: self.has(b, TokenKind::Question),
                                path: self.path(self.need(b, NodeKind::Path)),
                            })
                            .collect();
                        GenericParam::Type { name, bounds }
                    }
                    NodeKind::ConstParam => {
                        let ty = self.first_type(p).unwrap_or_else(|| self.bug(p, "a type"));
                        GenericParam::Const { name, ty }
                    }
                    NodeKind::EffectParam => GenericParam::Effect { name },
                    _ => self.bug(g, "a generic parameter"),
                }
            })
            .collect()
    }

    fn mode(&self, n: NodeId) -> Mode {
        if self.has(n, TokenKind::KwInout) {
            Mode::Inout
        } else if self.has(n, TokenKind::KwMove) {
            Mode::Move
        } else {
            Mode::Borrow
        }
    }

    fn params(&mut self, list: NodeId) -> Vec<Param> {
        self.nodes(list)
            .into_iter()
            .map(|p| {
                let attrs = self
                    .nodes(p)
                    .into_iter()
                    .filter(|&a| matches!(self.cst.kind(a), NodeKind::Attr | NodeKind::HashAttr))
                    .map(|a| self.attr(a))
                    .collect();
                // The name is in the `Name` node; an identifier outside it is
                // the `mut` of `mut self` (E0020), read as `inout self`.
                let mode = if self.has(p, TokenKind::Ident) { Mode::Inout } else { self.mode(p) };
                let t = self.name_token(p);
                let name = match self.kind_of(t) {
                    TokenKind::KwSelf => ParamName::SelfParam(self.cst.token(t).span),
                    TokenKind::Underscore => ParamName::Wild(self.cst.token(t).span),
                    _ => ParamName::Ident(self.ident(t)),
                };
                let ty = self.first_type(p);
                Param { attrs, mode, name, ty, span: self.span(p) }
            })
            .collect()
    }

    fn of_kind(&self, n: NodeId, kind: NodeKind) -> Vec<NodeId> {
        self.cst.child_nodes(n).filter(|&c| self.cst.kind(c) == kind).collect()
    }

    fn effect_row(&mut self, n: NodeId) -> EffectRow {
        let effects = self.nodes(n).into_iter().map(|p| self.path(p)).collect();
        EffectRow { effects, span: self.span(n) }
    }

    fn path(&self, n: NodeId) -> Path {
        let segments = self
            .toks(n)
            .into_iter()
            .filter(|&t| !matches!(self.kind_of(t), TokenKind::Dot | TokenKind::ColonColon))
            .map(|t| self.ident(t))
            .collect();
        Path { segments, span: self.span(n) }
    }

    // ------------------------------------------------------------ types

    fn ty(&mut self, n: NodeId) -> TypeId {
        let kind = match self.cst.kind(n) {
            NodeKind::PathType => {
                let path = self.path(self.need(n, NodeKind::Path));
                let args = match self.child(n, NodeKind::TypeArgs) {
                    Some(a) => self.of_class(a, Class::Type).into_iter().map(|t| self.ty(t)).collect(),
                    None => Vec::new(),
                };
                TypeKind::Path { path, args }
            }
            NodeKind::ConstArg => {
                let int = self.tok(n, TokenKind::Int).unwrap_or_else(|| self.bug(n, "an integer"));
                // SPAN-QUIRK: the literal has the span of its digits, also after a `-`.
                let lit_span = self.cst.token(int).span;
                let lit = self.int_lit(int);
                let mut e = self.add_expr(n, lit_span, ExprKind::Lit(lit));
                if self.has(n, TokenKind::Minus) {
                    let span = self.span(n);
                    e = self.add_expr(n, span, ExprKind::Unary { op: UnOp::Neg, expr: e });
                }
                TypeKind::ConstArg(e)
            }
            NodeKind::UnitType => TypeKind::Unit,
            NodeKind::TupleType => {
                TypeKind::Tuple(self.of_class(n, Class::Type).into_iter().map(|t| self.ty(t)).collect())
            }
            NodeKind::ArrayType => {
                let elem = self.first_type(n).unwrap_or_else(|| self.bug(n, "an element type"));
                let len = self.need_expr(n);
                TypeKind::Array { elem, len }
            }
            NodeKind::FnType => {
                let rt = self.has(n, TokenKind::KwRt);
                let list = self.need(n, NodeKind::FnTypeParams);
                let mut params = Vec::new();
                let mut mode = Mode::Borrow;
                for e in self.cst.children(list).to_vec() {
                    match e {
                        Elem::Token(t) => match self.kind_of(t) {
                            TokenKind::KwInout => mode = Mode::Inout,
                            TokenKind::KwMove => mode = Mode::Move,
                            _ => {}
                        },
                        Elem::Node(c) => {
                            let ty = self.ty(c);
                            params.push((std::mem::replace(&mut mode, Mode::Borrow), ty));
                        }
                    }
                }
                let ret = self.first_type(n);
                let effects = self.child(n, NodeKind::EffectRow).map(|e| self.effect_row(e));
                TypeKind::Fn { rt, params, ret, effects }
            }
            _ => self.bug(n, "the kind of a type"),
        };
        self.add_type(n, kind)
    }

    // ------------------------------------------------------------ blocks and statements

    fn block(&mut self, n: NodeId) -> ExprId {
        let block = self.block_body(n);
        let span = self.span(n);
        self.add_expr(n, span, ExprKind::Block(block))
    }

    fn block_body(&mut self, n: NodeId) -> Block {
        let mut stmts: Vec<(NodeId, StmtKind)> = Vec::new();
        for s in self.nodes(n) {
            let kind = self.stmt_kind(s);
            stmts.push((s, kind));
        }
        // The block value is the last statement when it is an expression (§6.1).
        let tail = match stmts.last() {
            Some((_, StmtKind::Expr(e))) => {
                let e = *e;
                stmts.pop();
                Some(e)
            }
            _ => None,
        };
        let stmts = stmts.into_iter().map(|(s, kind)| self.add_stmt(s, kind)).collect();
        Block { stmts, tail }
    }

    fn stmt_kind(&mut self, n: NodeId) -> StmtKind {
        match self.cst.kind(n) {
            NodeKind::LetStmt => {
                let pat = self.of_class(n, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(n, "a pattern"));
                let pat = self.pat(pat);
                let ty = self.first_type(n);
                let init = self.need_expr(n);
                StmtKind::Let { pat, ty, init }
            }
            NodeKind::VarStmt => {
                let name = self.name(n);
                let ty = self.first_type(n);
                let init = self.need_expr(n);
                StmtKind::Var { name, ty, init }
            }
            NodeKind::ForStmt => {
                let pat = self.of_class(n, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(n, "a pattern"));
                let pat = self.pat(pat);
                let moved = self.has(n, TokenKind::KwMove);
                let exprs = self.of_class(n, Class::Expr);
                let iter = self.expr(exprs[0]);
                let body = self.expr(exprs[1]);
                StmtKind::For { pat, moved, iter, body }
            }
            NodeKind::WhileStmt => {
                let exprs = self.of_class(n, Class::Expr);
                let cond = self.expr(exprs[0]);
                let body = self.expr(exprs[1]);
                StmtKind::While { cond, body }
            }
            NodeKind::LoopStmt => {
                // `loop { }` (E0020) is read as `while true { }`.
                // SPAN-QUIRK: the condition has the span of `loop`.
                let kw = self.toks(n)[0];
                let span = self.cst.token(kw).span;
                let cond = self.add_expr(n, span, ExprKind::Lit(Lit::Bool(true)));
                let body = self.block(self.need(n, NodeKind::Block));
                StmtKind::While { cond, body }
            }
            NodeKind::BreakStmt => StmtKind::Break,
            NodeKind::ContinueStmt => StmtKind::Continue,
            NodeKind::ReturnStmt => StmtKind::Return(self.first_expr(n).map(|e| self.expr(e))),
            NodeKind::AssertStmt => StmtKind::Assert(self.need_expr(n)),
            NodeKind::AssignStmt => {
                let exprs = self.of_class(n, Class::Expr);
                let target = self.expr(exprs[0]);
                let value = self.expr(exprs[1]);
                StmtKind::Assign { target, value }
            }
            NodeKind::ExprStmt => StmtKind::Expr(self.need_expr(n)),
            _ => self.bug(n, "the kind of a statement"),
        }
    }

    // ------------------------------------------------------------ expressions

    fn exprs(&mut self, n: NodeId) -> Vec<ExprId> {
        self.of_class(n, Class::Expr).into_iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, n: NodeId) -> ExprId {
        let kind = match self.cst.kind(n) {
            NodeKind::Literal => {
                let t = self.toks(n)[0];
                ExprKind::Lit(self.lit(t))
            }
            NodeKind::LeadingDotFloat => {
                let int = self.tok(n, TokenKind::Int).unwrap_or_else(|| self.bug(n, "digits"));
                ExprKind::Lit(Lit::Float { text: format!("0.{}", self.text_of(int)) })
            }
            NodeKind::HoleExpr => ExprKind::Hole,
            NodeKind::PathExpr => {
                let t = self.toks(n)[0];
                let ident = self.ident(t);
                let span = ident.span;
                ExprKind::Path(Path { segments: vec![ident], span })
            }
            NodeKind::ParenExpr => ExprKind::Paren(self.need_expr(n)),
            NodeKind::TupleExpr => ExprKind::Tuple(self.exprs(n)),
            NodeKind::ArrayExpr => ExprKind::Array(self.exprs(n)),
            NodeKind::RepeatExpr => {
                let e = self.exprs(n);
                ExprKind::Repeat { elem: e[0], len: e[1] }
            }
            NodeKind::Block => ExprKind::Block(self.block_body(n)),
            NodeKind::IfExpr => {
                let e = self.exprs(n);
                ExprKind::If { cond: e[0], then: e[1], else_: e.get(2).copied() }
            }
            NodeKind::MatchExpr => {
                let scrutinee = self.need_expr(n);
                let list = self.need(n, NodeKind::MatchArms);
                let arms = self
                    .nodes(list)
                    .into_iter()
                    .map(|a| {
                        let p =
                            self.of_class(a, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(a, "a pattern"));
                        let pat = self.pat(p);
                        let e = self.exprs(a);
                        let guard = if self.has(a, TokenKind::KwIf) { Some(e[0]) } else { None };
                        let body = *e.last().unwrap_or_else(|| self.bug(a, "a body"));
                        MatchArm { pat, guard, body, span: self.span(a) }
                    })
                    .collect();
                ExprKind::Match { scrutinee, arms }
            }
            NodeKind::ClosureExpr => {
                let params = self.params(self.need(n, NodeKind::ParamList));
                let ret = self.first_type(n);
                let effects = self.child(n, NodeKind::EffectRow).map(|e| self.effect_row(e));
                let body = self.block(self.need(n, NodeKind::Block));
                ExprKind::Closure { params, ret, effects, body }
            }
            NodeKind::HandleExpr => {
                let body = self.block(self.need(n, NodeKind::Block));
                let path = self.path(self.need(n, NodeKind::Path));
                let with = if self.child(n, NodeKind::ItemList).is_some() {
                    HandlerRef::Inline { effect: path, items: self.item_list(n) }
                } else if let Some(a) = self.child(n, NodeKind::ArgList) {
                    HandlerRef::Named { path, args: self.args(a) }
                } else {
                    HandlerRef::Named { path, args: Vec::new() }
                };
                ExprKind::Handle { body, with }
            }
            NodeKind::UnsafeExpr => ExprKind::Unsafe(self.block(self.need(n, NodeKind::Block))),
            NodeKind::ParExpr => {
                let var = self.name(n);
                let range = self.need(n, NodeKind::RangeExpr);
                let bounds = self.exprs(range);
                let body = self.block(self.need(n, NodeKind::Block));
                ExprKind::Par { var, from: bounds[0], to: bounds[1], body }
            }
            NodeKind::MoveExpr => ExprKind::Move(self.need_expr(n)),
            NodeKind::BinaryExpr => {
                let mut operands = Vec::new();
                let mut ops = Vec::new();
                for e in self.cst.children(n).to_vec() {
                    match e {
                        Elem::Node(c) => operands.push(self.expr(c)),
                        Elem::Token(t) => {
                            if let Some(op) = binop(self.kind_of(t)) {
                                ops.push((op, self.cst.token(t).span));
                            }
                        }
                    }
                }
                ExprKind::Binary { operands, ops }
            }
            NodeKind::RangeExpr => {
                let e = self.exprs(n);
                ExprKind::Range { lo: e[0], hi: e[1] }
            }
            NodeKind::CastExpr => {
                let expr = self.need_expr(n);
                let ty = self.first_type(n).unwrap_or_else(|| self.bug(n, "a type"));
                ExprKind::Cast { expr, ty }
            }
            NodeKind::PrefixExpr => {
                let op = if self.has(n, TokenKind::Minus) { UnOp::Neg } else { UnOp::Not };
                ExprKind::Unary { op, expr: self.need_expr(n) }
            }
            // `&x` (E0020): the AST holds `x`.
            NodeKind::RefExpr => return self.need_expr(n),
            NodeKind::CallExpr => {
                let callee = self.need_expr(n);
                let kind = if self.has(n, TokenKind::Tilde) {
                    CallKind::Flow
                } else if self.has(n, TokenKind::Bang) {
                    CallKind::Bang
                } else {
                    CallKind::Plain
                };
                let args = self.args(self.need(n, NodeKind::ArgList));
                ExprKind::Call { callee, kind, args }
            }
            NodeKind::FieldExpr => {
                let base = self.need_expr(n);
                let t = *self.toks(n).last().unwrap_or_else(|| self.bug(n, "a name"));
                ExprKind::Field { base, name: self.ident(t) }
            }
            NodeKind::TupleIndexExpr => {
                let base = self.need_expr(n);
                let t = self.tok(n, TokenKind::Int).unwrap_or_else(|| self.bug(n, "an index"));
                let index = tuple_index_value(self.text_of(t)).unwrap_or(u32::MAX);
                ExprKind::TupleIndex { base, index, index_span: self.cst.token(t).span }
            }
            NodeKind::IndexExpr => {
                let e = self.exprs(n);
                ExprKind::Index { base: e[0], index: e[1] }
            }
            NodeKind::TryExpr => ExprKind::Try(self.need_expr(n)),
            NodeKind::StructLit => {
                let callee = self.first_expr(n).unwrap_or_else(|| self.bug(n, "a path"));
                let path = self.struct_lit_path(callee);
                let list = self.need(n, NodeKind::StructLitFields);
                let fields = self
                    .nodes(list)
                    .into_iter()
                    .map(|f| {
                        let name = self.first_ident(f);
                        let value = self.need_expr(f);
                        (name, value)
                    })
                    .collect();
                ExprKind::Struct { path, fields }
            }
            _ => self.bug(n, "the kind of an expression"),
        };
        let span = self.span(n);
        self.add_expr(n, span, kind)
    }

    /// The path of a struct literal from the names of its callee (`a.b.C`).
    fn struct_lit_path(&self, callee: NodeId) -> Path {
        let mut segments = Vec::new();
        let mut cur = callee;
        loop {
            let t = *self.toks(cur).last().unwrap_or_else(|| self.bug(cur, "a name"));
            segments.push(self.ident(t));
            match self.cst.kind(cur) {
                NodeKind::FieldExpr => cur = self.first_expr(cur).unwrap_or_else(|| self.bug(cur, "a base")),
                NodeKind::PathExpr => break,
                _ => self.bug(callee, "a chain of names"),
            }
        }
        segments.reverse();
        Path { segments, span: self.span(callee) }
    }

    fn args(&mut self, list: NodeId) -> Vec<Arg> {
        self.nodes(list)
            .into_iter()
            .map(|a| {
                let mode = self.mode(a);
                let expr = self.need_expr(a);
                Arg { mode, expr, span: self.span(a) }
            })
            .collect()
    }

    // ------------------------------------------------------------ patterns

    fn pat(&mut self, n: NodeId) -> PatId {
        let kind = match self.cst.kind(n) {
            NodeKind::WildPat => PatKind::Wild,
            NodeKind::LitPat => {
                let t = self.toks(n)[0];
                PatKind::Lit(self.lit(t))
            }
            NodeKind::NegLitPat => {
                let t = self.tok(n, TokenKind::Int).unwrap_or_else(|| self.bug(n, "an integer"));
                PatKind::Neg(self.int_lit(t))
            }
            NodeKind::TuplePat => PatKind::Tuple(self.pats(n)),
            NodeKind::BindPat => {
                let p = self.need(n, NodeKind::Path);
                let t = self.toks(p)[0];
                PatKind::Bind(self.ident(t))
            }
            NodeKind::PathPat => PatKind::Path(self.path(self.need(n, NodeKind::Path))),
            NodeKind::TupleStructPat => {
                let path = self.path(self.need(n, NodeKind::Path));
                PatKind::TupleStruct { path, elems: self.pats(n) }
            }
            NodeKind::StructPat => {
                let path = self.path(self.need(n, NodeKind::Path));
                let fields = self
                    .of_kind(n, NodeKind::StructPatField)
                    .into_iter()
                    .map(|f| {
                        let name = self.first_ident(f);
                        let p =
                            self.of_class(f, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(f, "a pattern"));
                        (name, self.pat(p))
                    })
                    .collect();
                PatKind::Struct { path, fields }
            }
            NodeKind::OrPat => PatKind::Or(self.pats(n)),
            _ => self.bug(n, "the kind of a pattern"),
        };
        self.add_pat(n, kind)
    }

    fn pats(&mut self, n: NodeId) -> Vec<PatId> {
        self.of_class(n, Class::Pat).into_iter().map(|p| self.pat(p)).collect()
    }

    // ------------------------------------------------------------ literals

    fn lit(&self, t: TokenIdx) -> Lit {
        match self.kind_of(t) {
            TokenKind::Int => self.int_lit(t),
            TokenKind::Float => Lit::Float { text: self.text_of(t).to_string() },
            TokenKind::Char => Lit::Char(char_value(self.text_of(t))),
            TokenKind::Str => Lit::Str(self.str_lit(t)),
            TokenKind::KwTrue => Lit::Bool(true),
            TokenKind::KwFalse => Lit::Bool(false),
            k => onsa_diag::internal::bug(Some(self.cst.token(t).span), format!("{k:?} is not a literal")),
        }
    }

    /// An integer literal. A value above `u64::MAX` was reported (E0408) by
    /// the parser and reads as `u64::MAX`.
    fn int_lit(&self, t: TokenIdx) -> Lit {
        let text = self.text_of(t);
        Lit::Int { value: int_value(text).unwrap_or(u64::MAX), text: text.to_string() }
    }

    fn str_lit(&self, t: TokenIdx) -> StrLit {
        let tok = self.cst.token(t);
        str_lit(self.text_of(t), tok.span)
    }
}

/// The value of an integer literal (`1_000`, `0xFF`, `0b1010`), or `None`
/// when it is larger than `u64::MAX` (E0408).
pub(crate) fn int_value(text: &str) -> Option<u64> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    let parsed = if let Some(h) = digits.strip_prefix("0x") {
        u64::from_str_radix(h, 16)
    } else if let Some(b) = digits.strip_prefix("0b") {
        u64::from_str_radix(b, 2)
    } else {
        digits.parse::<u64>()
    };
    parsed.ok()
}

/// The value of a tuple index (`t.0`), or `None` when it is too large (E0408).
pub(crate) fn tuple_index_value(text: &str) -> Option<u32> {
    text.parse::<u32>().ok()
}

/// The character of a char literal (`'a'`, `'\n'`).
fn char_value(text: &str) -> char {
    let inner = &text[1..];
    let inner = inner.strip_suffix('\'').unwrap_or(inner);
    let mut chars = inner.chars();
    match chars.next() {
        Some('\\') => unescape(&mut chars).unwrap_or('\u{FFFD}'),
        Some(c) => c,
        None => '\u{FFFD}',
    }
}

/// A string literal with its interpolations split out (§2.4). The parser
/// counts the levels of the holes with it (spec §2.5).
pub(crate) fn str_lit(raw: &str, span: Span) -> StrLit {
    let inner = raw.strip_prefix('"').unwrap_or(raw);
    let inner = inner.strip_suffix('"').unwrap_or(inner);
    let base = span.start + 1;
    let mut segments = Vec::new();
    let mut text = String::new();
    let mut chars = inner.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' => {
                let mut rest = inner[i + 1..].chars();
                if let Some(ch) = unescape(&mut rest) {
                    text.push(ch);
                    let consumed = inner[i + 1..].len() - rest.as_str().len();
                    for _ in inner[i + 1..i + 1 + consumed].chars() {
                        chars.next();
                    }
                }
            }
            '{' if chars.peek().is_some_and(|&(_, n)| n == '{') => {
                chars.next();
                text.push('{');
            }
            '}' if chars.peek().is_some_and(|&(_, n)| n == '}') => {
                chars.next();
                text.push('}');
            }
            '{' => {
                if !text.is_empty() {
                    segments.push(StrSeg::Text(std::mem::take(&mut text)));
                }
                let path_start = i + 1;
                let mut path_end = path_start;
                for (j, n) in chars.by_ref() {
                    if n == '}' {
                        path_end = j;
                        break;
                    }
                }
                let path_text = &inner[path_start..path_end];
                let mut offset = base + path_start as u32;
                let mut seg_spans = Vec::new();
                for seg in path_text.split('.') {
                    let span = Span::new(span.file, offset, offset + seg.len() as u32);
                    seg_spans.push(Ident { name: seg.to_string(), span });
                    offset += seg.len() as u32 + 1;
                }
                let pspan = Span::new(span.file, base + path_start as u32, base + path_end as u32);
                segments.push(StrSeg::Interp(Path { segments: seg_spans, span: pspan }));
            }
            _ => text.push(c),
        }
    }
    if !text.is_empty() || segments.is_empty() {
        segments.push(StrSeg::Text(text));
    }
    StrLit { segments, span }
}

/// `\n` etc. after the backslash has been consumed (S-19).
fn unescape(chars: &mut std::str::Chars) -> Option<char> {
    match chars.next()? {
        'n' => Some('\n'),
        't' => Some('\t'),
        'r' => Some('\r'),
        '0' => Some('\0'),
        '\\' => Some('\\'),
        '"' => Some('"'),
        '\'' => Some('\''),
        'u' => {
            let rest = chars.as_str();
            let rest = rest.strip_prefix('{')?;
            let end = rest.find('}')?;
            let ch = u32::from_str_radix(&rest[..end], 16).ok().and_then(char::from_u32)?;
            for _ in 0..end + 2 {
                chars.next();
            }
            Some(ch)
        }
        _ => None,
    }
}

/// The binary operator of a token (§3.1), if it is one.
pub(crate) fn binop(kind: TokenKind) -> Option<BinOp> {
    use TokenKind::*;
    Some(match kind {
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Rem,
        PlusPercent => BinOp::WrapAdd,
        MinusPercent => BinOp::WrapSub,
        StarPercent => BinOp::WrapMul,
        PlusPipe => BinOp::SatAdd,
        MinusPipe => BinOp::SatSub,
        StarPipe => BinOp::SatMul,
        EqEq => BinOp::Eq,
        NotEq => BinOp::Ne,
        Lt => BinOp::Lt,
        LtEq => BinOp::Le,
        Gt => BinOp::Gt,
        GtEq => BinOp::Ge,
        AndAnd => BinOp::And,
        OrOr => BinOp::Or,
        Amp => BinOp::BitAnd,
        Pipe => BinOp::BitOr,
        Caret => BinOp::BitXor,
        Shl => BinOp::Shl,
        Shr => BinOp::Shr,
        _ => return None,
    })
}
