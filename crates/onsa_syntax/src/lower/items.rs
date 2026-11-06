//! The items read whole and their parts: the visibility, the derives, the
//! attributes, the kind of an item read whole (`decls::read_kind` reads
//! it), the fields, the variants, the signatures, the generics, the
//! parameters, the effect rows and the paths.

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

    /// The kind of the declaration `n` read whole ([`Lower::read_kind`]).
    pub(super) fn item_kind(&mut self, n: NodeId) -> ItemKind {
        match self.read_kind(n, false) {
            Some((kind, true)) => kind,
            _ => self.bug(n, "a heading read whole"),
        }
    }

    pub(super) fn field(&mut self, f: NodeId) -> Field {
        let vis = self.child(f, NodeKind::Vis).map_or(Vis::Default, |v| self.vis(v));
        let name = self.name(f);
        let ty = self.first_type(f).unwrap_or_else(|| self.bug(f, "a type"));
        let default = self.child(f, NodeKind::FieldDefault).map(|d| self.field_default(d));
        Field { vis, name, ty, default, span: self.span(f) }
    }

    /// The default `d` of a field: an item, for its unit (§18.1), that is in
    /// no list of items ([`Ast::root`]). The parser finishes a `Field` right
    /// after it, so that a field read whole has its default read whole.
    fn field_default(&mut self, d: NodeId) -> ItemId {
        let value = self.need_expr(d);
        let kind = ItemKind::FieldDefault { value };
        let span = self.span(d);
        let (vis, mem_attr) = (Vis::Default, self.first_mem(d));
        self.add_item(d, Item { span, attrs: Vec::new(), vis, vis_span: None, kind, failed: None, mem_attr })
    }

    pub(super) fn variant(&mut self, v: NodeId) -> Variant {
        let name = self.name(v);
        let fields = match self.child(v, NodeKind::VariantFields) {
            Some(f) => self.of_class(f, Class::Type).into_iter().map(|t| self.ty(t)).collect(),
            None => Vec::new(),
        };
        Variant { name, fields, span: self.span(v) }
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

    /// The rest `r` of the struct pattern or the fields of a literal `n`,
    /// with the `,` before it when only blanks are between them
    /// ([`StructRest`]).
    pub(super) fn struct_rest(&self, n: NodeId, r: NodeId) -> StructRest {
        let span = self.span(r);
        let of_token = |t| match self.cst.token(t).kind {
            TokenKind::DotDot => RestMark::Dots,
            TokenKind::DotDotDot => RestMark::Fill,
            _ => RestMark::Underscore,
        };
        let mark = self.cst.child_tokens(r).next().map_or(RestMark::Underscore, of_token);
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
        StructRest { mark, span, removal }
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
            let names = self.toks(u).into_iter().filter(|&t| crate::starts::names_a_member(self.kind_of(t)));
            names.map(|t| self.ident(t)).collect()
        });
        UseDecl { path: self.path(tree), names }
    }
}
