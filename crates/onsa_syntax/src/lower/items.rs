//! The items read whole and their parts: the visibility, the derives, the
//! attributes, the kinds of the items, the fields, the variants, the
//! signatures, the generics, the parameters, the effect rows and the paths.

use super::*;

impl<'a> Lower<'a> {
    // ------------------------------------------------------------ items

    /// An `Item` node: the item, or the failed item when a syntax error
    /// stopped it (`None` when not even its name was read).
    pub(super) fn any_item(&mut self, n: NodeId) -> Option<ItemId> {
        if self.cst.is_complete(n) { Some(self.item(n)) } else { self.failed_item(n) }
    }

    pub(super) fn item(&mut self, n: NodeId) -> ItemId {
        let head = self.head(n);
        let decl = head.decl.unwrap_or_else(|| self.bug(n, "a declaration"));
        let kind = self.item_kind(decl);
        self.add_head_item(n, head, kind, None)
    }

    pub(super) fn vis(&self, n: NodeId) -> Vis {
        if self.has(n, TokenKind::KwPriv) { Vis::Priv } else { Vis::Pub }
    }

    /// The traits at the head of a struct or an enum (§6.4).
    pub(super) fn derives(&mut self, n: NodeId) -> Derives {
        let Some(d) = self.child(n, NodeKind::Derives) else { return Derives::Listed(Vec::new()) };
        let paths =
            self.of_kind(d, NodeKind::Bound).into_iter().map(|b| self.path(self.need(b, NodeKind::Path))).collect();
        Derives::Listed(paths)
    }

    pub(super) fn attr(&mut self, n: NodeId) -> Attr {
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
        Attr { name, args, span: self.span(n) }
    }

    pub(super) fn item_kind(&mut self, n: NodeId) -> ItemKind {
        match self.cst.kind(n) {
            NodeKind::Fn => ItemKind::Fn(self.fn_decl(n)),
            NodeKind::Flow => {
                let name = self.name(n);
                let params = self.params(self.need(n, NodeKind::ParamList));
                let ret = self.first_type(n).unwrap_or_else(|| self.bug(n, "a return type"));
                let ret_clock = self.clock(n);
                let body = self.block(self.need(n, NodeKind::Block));
                ItemKind::Flow(FlowDecl { name, params, ret, ret_clock, body })
            }
            NodeKind::Struct => {
                let name = self.name(n);
                let generics = self.generics(n);
                let derives = self.derives(n);
                let list = self.need(n, NodeKind::FieldList);
                let fields = self.nodes(list).into_iter().map(|f| self.field(f)).collect();
                ItemKind::Struct(StructDecl { name, generics, derives, repr: Repr::Onsa, fields })
            }
            NodeKind::Enum => {
                let name = self.name(n);
                let generics = self.generics(n);
                let derives = self.derives(n);
                let list = self.need(n, NodeKind::VariantList);
                let variants = self.nodes(list).into_iter().map(|v| self.variant(v)).collect();
                ItemKind::Enum(EnumDecl { name, generics, derives, variants })
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
                ItemKind::Use(self.use_decl(tree))
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

    pub(super) fn field(&mut self, f: NodeId) -> Field {
        let vis = self.child(f, NodeKind::Vis).map_or(Vis::Default, |v| self.vis(v));
        let name = self.name(f);
        let ty = self.first_type(f).unwrap_or_else(|| self.bug(f, "a type"));
        Field { vis, name, ty, span: self.span(f) }
    }

    pub(super) fn variant(&mut self, v: NodeId) -> Variant {
        let name = self.name(v);
        let fields = match self.child(v, NodeKind::VariantFields) {
            Some(f) => self.of_class(f, Class::Type).into_iter().map(|t| self.ty(t)).collect(),
            None => Vec::new(),
        };
        Variant { name, fields, span: self.span(v) }
    }

    pub(super) fn fn_decl(&mut self, n: NodeId) -> FnDecl {
        let rt = self.has(n, TokenKind::KwRt);
        let name = self.name(n);
        let generics = self.generics(n);
        let params = self.params(self.need(n, NodeKind::ParamList));
        let ret = self.first_type(n);
        let ret_clock = self.clock(n);
        let effects = self.child(n, NodeKind::EffectRow).map(|e| self.effect_row(e));
        let body = self.child(n, NodeKind::Block).map(|b| self.block(b));
        FnDecl { rt, name, generics, params, ret, ret_clock, effects, body }
    }

    /// The members of a declaration's list: the members read whole and the
    /// failed ones whose name was read (each member is a unit, S-59).
    pub(super) fn item_list(&mut self, n: NodeId) -> Vec<ItemId> {
        let list = self.need(n, NodeKind::ItemList);
        let members: Vec<NodeId> =
            self.nodes(list).into_iter().filter(|&i| self.cst.kind(i) == NodeKind::Item).collect();
        members.into_iter().filter_map(|i| self.any_item(i)).collect()
    }

    pub(super) fn generics(&mut self, n: NodeId) -> Vec<GenericParam> {
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

    pub(super) fn mode(&self, n: NodeId) -> Mode {
        if self.has(n, TokenKind::KwInout) {
            Mode::Inout
        } else if self.has(n, TokenKind::KwMove) {
            Mode::Move
        } else {
            Mode::Borrow
        }
    }

    pub(super) fn params(&mut self, list: NodeId) -> Vec<Param> {
        self.nodes(list)
            .into_iter()
            .map(|p| {
                let attrs = self
                    .nodes(p)
                    .into_iter()
                    .filter(|&a| self.cst.kind(a) == NodeKind::Attr)
                    .map(|a| self.attr(a))
                    .collect();
                let mode = self.mode(p);
                let t = self.name_token(p);
                let name = match self.kind_of(t) {
                    TokenKind::KwSelf => ParamName::SelfParam(self.cst.token(t).span),
                    TokenKind::Underscore => ParamName::Wild(self.cst.token(t).span),
                    _ => ParamName::Ident(self.ident(t)),
                };
                let ty = self.first_type(p);
                let clock = self.clock(p);
                Param { attrs, mode, name, ty, clock, span: self.span(p) }
            })
            .collect()
    }

    /// The rest `r` of the struct pattern `n`, with the `,` before it when
    /// only blanks are between them ([`StructRest`]).
    pub(super) fn struct_rest(&self, n: NodeId, r: NodeId) -> StructRest {
        let span = self.span(r);
        let before = self.cst.children(n).iter().take_while(|&&e| e != Elem::Node(r));
        let mut removal = span;
        for e in before.collect::<Vec<_>>().into_iter().rev() {
            let Elem::Token(t) = *e else { break };
            let tok = self.cst.token(t);
            match tok.kind {
                TokenKind::Whitespace | TokenKind::Newline => {}
                TokenKind::Comma => {
                    removal = Span::new(span.file, tok.span.start, span.end);
                    break;
                }
                _ => break,
            }
        }
        StructRest { span, removal }
    }

    pub(super) fn of_kind(&self, n: NodeId, kind: NodeKind) -> Vec<NodeId> {
        self.cst.child_nodes(n).filter(|&c| self.cst.kind(c) == kind).collect()
    }

    pub(super) fn effect_row(&mut self, n: NodeId) -> EffectRow {
        let effects = self.nodes(n).into_iter().map(|p| self.path(p)).collect();
        EffectRow { effects, span: self.span(n) }
    }

    pub(super) fn path(&self, n: NodeId) -> Path {
        let segments =
            self.toks(n).into_iter().filter(|&t| self.kind_of(t) != TokenKind::Dot).map(|t| self.ident(t)).collect();
        Path { segments, span: self.span(n) }
    }

    /// The `UseTree` `tree` of a `use`, read whole or cut (R-180): its path
    /// and the names of its list read, a keyword among them (R-272).
    pub(super) fn use_decl(&self, tree: NodeId) -> UseDecl {
        let names = self.child(tree, NodeKind::UseNames).map(|u| {
            let names = self
                .toks(u)
                .into_iter()
                .filter(|&t| self.kind_of(t) == TokenKind::Ident || self.kind_of(t).is_keyword());
            names.map(|t| self.ident(t)).collect()
        });
        UseDecl { path: self.path(tree), names }
    }
}
