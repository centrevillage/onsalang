//! The heads of the items, and the items a syntax error stopped (S-59,
//! R-71): what was read of their headings.

use super::*;

impl<'a> Lower<'a> {
    /// An item a syntax error stopped (spec §18.1, S-59): its name and the
    /// parts of its heading that were read whole stay, so that the other
    /// units see it (R-71). The attributes and the visibility are kept when
    /// they were read whole. `None` when its name was not read, and for a
    /// failed `impl` heading (R-180: W5-04). A `use` cut keeps what it read.
    pub(super) fn failed_item(&mut self, n: NodeId) -> Option<ItemId> {
        let head = self.head(n);
        let (kind, failed) = self.failed_kind(head.decl?)?;
        Some(self.add_head_item(n, head, kind, Some(failed)))
    }

    /// The head of the `Item` node `n`, up to its declaration node (the
    /// `Error` nodes after it are tokens the recovery skipped): the doc
    /// comments the parser took for the item, the attributes read whole (one
    /// that was not read, or that the table refused, is incomplete: no
    /// attribute), the visibility and the modifiers written (§18.1).
    pub(super) fn head(&mut self, n: NodeId) -> Head {
        let mut head = Head { attrs: Vec::new(), vis: Vis::Default, rt: false, unread_attr: false, decl: None };
        let mut words: Vec<Vis> = Vec::new();
        let mut vis_form = false;
        for c in self.nodes(n) {
            let complete = self.cst.is_complete(c);
            match self.cst.kind(c) {
                // The AST has no doc comments (D-02): `crate::docs::doc_comments` reads them on the CST.
                NodeKind::Docs => {}
                NodeKind::Attr if complete => head.attrs.push(self.attr(c)),
                NodeKind::Attr => head.unread_attr = true,
                NodeKind::Vis if complete => words.push(self.vis(c)),
                NodeKind::Vis => vis_form = true,
                // The modifiers the parser read on after (S-464): out of
                // order, with words of other languages, before a keyword.
                NodeKind::Error => {
                    for t in self.toks(c) {
                        match self.kind_of(t) {
                            TokenKind::KwPub => words.push(Vis::Pub),
                            TokenKind::KwPriv => words.push(Vis::Priv),
                            TokenKind::KwRt => head.rt = true,
                            _ => {}
                        }
                    }
                }
                _ => {
                    head.decl = Some(c);
                    break;
                }
            }
        }
        // SPEC-GAP(S-482): the visibility written right is kept when the head
        // was read on after another form; a visibility of another language,
        // and `pub` with `priv`, are the default.
        if !vis_form
            && let Some(&first) = words.first()
            && words.iter().all(|&w| w == first)
        {
            head.vis = first;
        }
        head
    }

    /// Add the item `n` of `head` and `kind`: an `rt` written out of order is
    /// the function's (S-464), and a struct or an enum with an attribute that
    /// was not read has its derives and its layout unknown (§18.1, S-460).
    pub(super) fn add_head_item(
        &mut self,
        n: NodeId,
        head: Head,
        mut kind: ItemKind,
        failed: Option<Failed>,
    ) -> ItemId {
        let Head { attrs, vis, rt, unread_attr, .. } = head;
        match &mut kind {
            ItemKind::Fn(f) => f.rt |= rt,
            ItemKind::Struct(s) if unread_attr => {
                s.derives = Derives::Unknown;
                s.repr = Repr::Unknown;
            }
            ItemKind::Struct(s) if attrs.iter().any(|a| a.is(crate::attrs::REPR, crate::attrs::C)) => s.repr = Repr::C,
            ItemKind::Enum(e) if unread_attr => e.derives = Derives::Unknown,
            _ => {}
        }
        let span = self.span(n);
        self.add_item(n, Item { span, attrs, vis, kind, failed })
    }

    /// The name of a declaration when it was read whole.
    pub(super) fn read_name(&self, n: NodeId) -> Option<Ident> {
        let name = self.child(n, NodeKind::Name)?;
        if !self.cst.is_complete(name) {
            return None;
        }
        self.toks(name).first().map(|&t| self.ident(t))
    }

    /// The generic parameters of a failed declaration; `heading` turns false
    /// when they were cut.
    pub(super) fn failed_generics(&mut self, n: NodeId, heading: &mut bool) -> Vec<GenericParam> {
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
    pub(super) fn failed_type(&mut self, n: NodeId, heading: &mut bool) -> Option<TypeId> {
        let types = self.of_class(n, Class::Type);
        if types.iter().any(|&t| !self.cst.is_complete(t)) {
            *heading = false;
            return None;
        }
        types.first().map(|&t| self.ty(t))
    }

    /// The type a syntax error left unread in the failed node `n`.
    pub(super) fn error_type(&mut self, n: NodeId) -> TypeId {
        self.add_type(n, TypeKind::Error)
    }

    /// A body, a value: lowered when the node was finished, else an error.
    pub(super) fn failed_expr(&mut self, n: NodeId) -> ExprId {
        if self.cst.is_complete(n) {
            if self.cst.kind(n) == NodeKind::Block { self.block(n) } else { self.expr(n) }
        } else {
            let span = self.span(n);
            self.add_expr(n, span, ExprKind::Error)
        }
    }

    /// The members of a failed declaration with a list of them: the members
    /// read whole and the failed ones whose name was read.
    pub(super) fn failed_members(&mut self, n: NodeId, heading: &mut bool) -> Vec<ItemId> {
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
    pub(super) fn failed_params(&mut self, n: NodeId, heading: &mut bool) -> Vec<Param> {
        match self.child(n, NodeKind::ParamList) {
            Some(p) if self.cst.is_complete(p) => self.params(p),
            _ => {
                *heading = false;
                Vec::new()
            }
        }
    }

    /// The kind of a failed declaration node and how far it was read.
    pub(super) fn failed_kind(&mut self, d: NodeId) -> Option<(ItemKind, Failed)> {
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
                let ret_clock = self.clock(d);
                ItemKind::Fn(FnDecl { rt, name, generics, params, ret, ret_clock, effects, body })
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
                let ret_clock = self.clock(d);
                let body = match self.child(d, NodeKind::Block) {
                    Some(b) => self.failed_expr(b),
                    None => {
                        heading = false;
                        let span = self.span(d);
                        self.add_expr(d, span, ExprKind::Error)
                    }
                };
                ItemKind::Flow(FlowDecl { name, params, ret, ret_clock, body })
            }
            NodeKind::Struct => {
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let derives = self.failed_derives(d, &mut heading);
                let fields = match self.child(d, NodeKind::FieldList) {
                    // A list cut at its `{` is no list (a tuple struct, S-39): the
                    // fields were not read, and their uses get no diagnostic (S-260).
                    Some(list) => {
                        let fields = self.nodes(list);
                        fields.into_iter().filter(|&f| self.cst.is_complete(f)).map(|f| self.field(f)).collect()
                    }
                    None => {
                        heading = false;
                        Vec::new()
                    }
                };
                ItemKind::Struct(StructDecl { name, generics, derives, repr: Repr::Onsa, fields })
            }
            NodeKind::Enum => {
                let name = self.read_name(d)?;
                let generics = self.failed_generics(d, &mut heading);
                let derives = self.failed_derives(d, &mut heading);
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
                ItemKind::Enum(EnumDecl { name, generics, derives, variants })
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
            // A `use` cut before its names were all read (R-180): the path and
            // the names of its list read so far.
            NodeKind::Use => {
                let tree = self.child(d, NodeKind::UseTree)?;
                let segments =
                    self.toks(tree).into_iter().filter(|&t| self.kind_of(t) != TokenKind::Dot).map(|t| self.ident(t));
                let path = Path { segments: segments.collect(), span: self.span(tree) };
                let names = self.child(tree, NodeKind::UseNames).map(|u| {
                    let names = self.toks(u).into_iter().filter(|&t| self.kind_of(t) == TokenKind::Ident);
                    names.map(|t| self.ident(t)).collect()
                });
                return Some((ItemKind::Use(UseDecl { path, names }), Failed::Heading));
            }
            // What is not a declaration.
            _ => return None,
        };
        Some((kind, if heading { Failed::Body } else { Failed::Heading }))
    }

    /// The traits at the head of a failed struct or enum; `heading` turns
    /// false when they were cut.
    pub(super) fn failed_derives(&mut self, n: NodeId, heading: &mut bool) -> Derives {
        match self.child(n, NodeKind::Derives) {
            Some(d) if !self.cst.is_complete(d) => {
                *heading = false;
                Derives::Listed(Vec::new())
            }
            _ => self.derives(n),
        }
    }
}

/// The head of an item as [`Lower::head`] read it.
pub(super) struct Head {
    attrs: Vec<Attr>,
    vis: Vis,
    /// An `rt` written out of order before the declaration's keyword.
    rt: bool,
    /// An attribute that was not read (S-460).
    unread_attr: bool,
    pub(super) decl: Option<NodeId>,
}
