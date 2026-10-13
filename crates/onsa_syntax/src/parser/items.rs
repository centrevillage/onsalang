//! The declarations: their doc comments, attributes and visibility, the
//! dispatch on [`DECLARATIONS`] and the parser of each declaration.

use super::*;

impl<'a> Parser<'a> {
    // ------------------------------------------------------------ items

    /// Skip the blank lines and plain comments before an item; return the
    /// first and the last doc comment directly before it (blank lines and
    /// plain comments may come between the doc comments). This is where a
    /// doc comment is taken for the item (the `Docs` node). A `//!` there is
    /// taken too: it is not at the head of the file, and its E0004 has the
    /// candidate `///` where a `///` is taken (§2.1, [`crate::docs`]).
    pub(super) fn collect_docs(&mut self) -> Option<(usize, usize)> {
        let mut docs = None;
        loop {
            let t = self.tokens[self.pos];
            match t.kind {
                TokenKind::Newline | TokenKind::Comment => self.pos += 1,
                // SPEC-GAP(S-444): a doc comment after code on its line
                // documents nothing (its E0004, [`crate::docs`]).
                TokenKind::DocComment | TokenKind::ModuleDoc if !self.starts_its_line(self.pos) => self.pos += 1,
                TokenKind::DocComment | TokenKind::ModuleDoc => {
                    let first = docs.map_or(self.pos, |(f, _)| f);
                    docs = Some((first, self.pos));
                    self.pos += 1;
                }
                _ => break,
            }
        }
        docs
    }

    /// The doc comments before the next element of a list in which a line
    /// break is a blank (a field, a variant, an input of a flow, §2.1), as
    /// [`Parser::collect_docs`] takes them before an item.
    pub(super) fn element_docs(&mut self) -> Option<(usize, usize)> {
        let next = self.peek_index();
        let mut docs = (self.pos..next).filter(|&k| self.tokens[k].kind.is_doc() && self.starts_its_line(k));
        let first = docs.next()?;
        let last = docs.next_back().unwrap_or(first);
        self.pos = last + 1;
        Some((first, last))
    }

    /// Whether `tokens[k]` has no code before it on its line (S-444: a doc
    /// comment that does not is attached to nothing).
    fn starts_its_line(&self, k: usize) -> bool {
        k == 0 || self.tokens[k - 1].kind == TokenKind::Newline
    }

    /// The `Docs` node of the doc comments `docs` (from
    /// [`Parser::collect_docs`] or [`Parser::element_docs`]), in the node
    /// open: the one place a doc comment is attached (§2.1, S-51).
    pub(super) fn attach_docs(&mut self, docs: Option<(usize, usize)>) {
        if let Some((first, last)) = docs {
            let d = self.enter_unit(NodeKind::Docs, self.tokens[first].span.start);
            for k in first..=last {
                self.events.push(Event::Token(self.full[k]));
            }
            self.complete(d, NodeKind::Docs);
        }
    }

    /// The `//!` at the head of the file, before its first item and the doc
    /// comments of that item (§2.1): the `ModuleDocs` node, the documentation
    /// of the module.
    pub(super) fn module_docs(&mut self) {
        let mut docs = None;
        let mut k = self.pos;
        loop {
            match self.tokens[k].kind {
                TokenKind::Newline | TokenKind::Comment => {}
                TokenKind::ModuleDoc => docs = Some((docs.map_or(k, |(f, _)| f), k)),
                _ => break,
            }
            k += 1;
        }
        if let Some((first, last)) = docs {
            self.pos = last + 1;
            let d = self.enter_unit(NodeKind::ModuleDocs, self.tokens[first].span.start);
            for k in first..=last {
                self.events.push(Event::Token(self.full[k]));
            }
            self.complete(d, NodeKind::ModuleDocs);
        }
    }

    /// Open the `Item` node; its doc comments (from `collect_docs`) are its
    /// first child, `Docs`. The trivia before them belong to the enclosing list.
    pub(super) fn start_item(&mut self, docs: Option<(usize, usize)>) -> Marker {
        let start = self.peek().span.start;
        let m = self.enter_unit(NodeKind::Item, start);
        self.attach_docs(docs);
        m
    }

    /// The attributes before a declaration or a parameter; returns how many.
    pub(super) fn parse_attrs(&mut self) -> PResult<usize> {
        let mut n = 0;
        loop {
            self.skip_newlines_if_followed_by(|k| k == TokenKind::At);
            if self.at(TokenKind::At) {
                self.parse_attr()?;
                n += 1;
            } else {
                break;
            }
        }
        Ok(n)
    }

    /// In a significant context, skip newlines only when the next real token satisfies `f`.
    fn skip_newlines_if_followed_by(&mut self, f: impl Fn(TokenKind) -> bool) {
        if self.at(TokenKind::Newline) && f(self.peek_past_newlines().kind) {
            self.skip_newlines();
        }
    }

    fn parse_attr(&mut self) -> PResult<()> {
        let m = self.start(NodeKind::Attr)?;
        self.expect(TokenKind::At)?;
        self.parse_attr_body()?;
        self.complete(m, NodeKind::Attr);
        Ok(())
    }

    fn parse_attr_body(&mut self) -> PResult<()> {
        self.parse_ident("attribute name")?;
        if self.touches(TokenKind::LParen, true, false) {
            let m = self.start(NodeKind::AttrArgs)?;
            self.bump();
            self.with_nl(false, |p| {
                while !p.at(TokenKind::RParen) {
                    if p.at(TokenKind::Ident) && p.peek2().kind == TokenKind::Colon {
                        let a = p.start(NodeKind::AttrNamedArg)?;
                        p.parse_ident("key")?;
                        p.bump();
                        p.parse_expr()?;
                        p.complete(a, NodeKind::AttrNamedArg);
                    } else if p.at(TokenKind::Str) {
                        p.expect(TokenKind::Str)?;
                    } else {
                        p.parse_path("attribute argument")?;
                    }
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.close_list(NodeKind::AttrArgs, TokenKind::RParen)
            })?;
            self.complete(m, NodeKind::AttrArgs);
        }
        Ok(())
    }

    fn parse_vis(&mut self) -> PResult<()> {
        if !self.at(TokenKind::KwPub) {
            return Ok(());
        }
        let m = self.start(NodeKind::Vis)?;
        self.bump();
        // `pub(pkg)` (S-36: W3-08 makes it E0020 too) and `pub(crate)` (the
        // table's `pub_crate`) are each one form with the blanks in them
        // (S-248): a blank before the `(` is read across, so that the form's
        // row reports it once.
        let words = |p: &Self| ["pkg", "crate"].iter().any(|w| p.is_ident(p.peek2(), w));
        if self.at(TokenKind::LParen) && (!self.peek_gap().is_some() || words(self)) {
            self.bump();
            let t = self.peek();
            if !self.is_ident(t, "pkg") {
                return Err(self.unexpected("`pkg`"));
            }
            self.bump();
            self.expect(TokenKind::RParen)?;
        }
        self.complete(m, NodeKind::Vis);
        Ok(())
    }

    /// The item whose node `m` is open (doc comments, attributes, visibility, declaration).
    pub(super) fn parse_item(&mut self, ctx: ItemCtx, m: Marker) -> PResult<Completed> {
        if self.parse_attrs()? > 0 {
            self.skip_newlines();
        }
        self.parse_vis()?;
        let t = self.peek();
        if let Some((_, _, places)) = DECLARATIONS.iter().find(|(k, _, _)| *k == t.kind)
            && !places.contains(&ctx)
        {
            return Err(self.not_a_member(t, ctx));
        }
        if let Some((_, parse, _)) = DECLARATIONS.iter().find(|(k, _, _)| *k == t.kind) {
            parse(self, ctx)?;
            // A constant ends with an expression and a type alias with a
            // type, which a symbol on the next line may go on with.
            if !matches!(t.kind, TokenKind::KwConst | TokenKind::KwType) {
                self.end_no_operand();
            }
        } else {
            return Err(self.unexpected("a declaration"));
        }
        Ok(self.complete(m, NodeKind::Item))
    }

    /// E0002 for the declaration at `t` in the list of declarations of
    /// `ctx`, where it is not a member: the members are a closed list
    /// (§18.1: methods and associated constants; the operations of an
    /// `effect`, the functions of a `handler` and of an `extern`, and the
    /// opaque types of an `extern`, §14.1). A declaration with a list of its
    /// own is never a member, so declarations do not nest without bound
    /// (they count no level, spec §2.5).
    // SPEC-GAP(S-263): the closed list of the declarations a declaration holds is not written in the spec; the conservative reading of §18.1, §8.1 and §14.1.
    fn not_a_member(&mut self, t: Token, ctx: ItemCtx) -> ParseError {
        let (owner, members) = match ctx {
            ItemCtx::Trait => ("a `trait`", "functions and `const`s"),
            ItemCtx::Impl => ("an `impl`", "functions and `const`s"),
            ItemCtx::Effect => ("an `effect`", "its operations, declared as functions"),
            ItemCtx::Handler | ItemCtx::InlineHandler => ("a handler", "functions"),
            ItemCtx::Extern => ("an `extern` block", "functions and opaque `type`s"),
            ItemCtx::Top => onsa_diag::internal::bug(Some(t.span), "a declaration of the top level is refused there"),
        };
        let word = self.token_text(t).to_string();
        let d = Diagnostic::new(
            Stage::Syntax,
            Code::E0002,
            t.span,
            format!("`{word}` cannot be declared in {owner}; declare it at the top level of the module"),
        )
        .with_found(word)
        .with_rule(format!("the members of {owner} are {members} (§18.1)"));
        self.report(d);
        ParseError
    }

    pub(super) fn parse_flow(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Flow)?;
        self.bump();
        self.parse_name("flow name")?;
        self.parse_params(true, true)?;
        self.expect(TokenKind::Arrow)?;
        self.parse_type()?;
        self.parse_body()?;
        self.complete(m, NodeKind::Flow);
        Ok(())
    }

    /// `[rt] fn name[generics](params) [-> T] [uses {..}] [body]`
    pub(super) fn parse_fn(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Fn)?;
        self.eat(TokenKind::KwRt);
        self.expect(TokenKind::KwFn)?;
        self.parse_name("function name")?;
        self.parse_generics_opt()?;
        self.parse_params(true, false)?;
        if self.at_line_end(TokenKind::Arrow) {
            self.bump();
            self.parse_type()?;
        }
        self.parse_effect_row_opt()?;
        match ctx {
            ItemCtx::Effect | ItemCtx::Extern => {
                if self.at(TokenKind::LBrace) {
                    let t = self.peek();
                    return Err(self.error(Code::E0002, t.span, "this declaration is a signature and takes no body"));
                }
            }
            ItemCtx::Trait => {
                if self.e0003_unless_on_the_line(TokenKind::LBrace) {
                    self.parse_block_expr()?;
                }
            }
            _ => {
                if !self.e0003_unless_on_the_line(TokenKind::LBrace) {
                    return Err(self.unexpected("`{` (a function body)"));
                }
                self.parse_block_expr()?;
            }
        }
        self.complete(m, NodeKind::Fn);
        Ok(())
    }

    pub(super) fn parse_struct(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Struct)?;
        self.expect(TokenKind::KwStruct)?;
        self.parse_name("struct name")?;
        self.parse_generics_opt()?;
        if self.at(TokenKind::LParen) {
            let b = self.start(NodeKind::TupleStructBody)?;
            self.bump();
            self.with_nl(false, |p| {
                p.parse_type()?;
                p.expect(TokenKind::RParen)?;
                Ok(())
            })?;
            self.complete(b, NodeKind::TupleStructBody);
        } else {
            let l = self.start(NodeKind::FieldList)?;
            self.e0003_unless_on_the_line(TokenKind::LBrace);
            self.expect(TokenKind::LBrace)?;
            self.with_nl(false, |p| {
                while !p.at(TokenKind::RBrace) {
                    let docs = p.element_docs();
                    let f = p.start(NodeKind::Field)?;
                    p.attach_docs(docs);
                    p.parse_vis()?;
                    p.parse_name("field name")?;
                    p.expect(TokenKind::Colon)?;
                    p.parse_type()?;
                    p.complete(f, NodeKind::Field);
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.close_list(NodeKind::FieldList, TokenKind::RBrace)?;
                Ok(())
            })?;
            self.complete(l, NodeKind::FieldList);
        }
        self.complete(m, NodeKind::Struct);
        Ok(())
    }

    pub(super) fn parse_enum(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Enum)?;
        self.expect(TokenKind::KwEnum)?;
        self.parse_name("enum name")?;
        self.parse_generics_opt()?;
        let l = self.start(NodeKind::VariantList)?;
        self.e0003_unless_on_the_line(TokenKind::LBrace);
        self.expect(TokenKind::LBrace)?;
        self.with_nl(false, |p| {
            while !p.at(TokenKind::RBrace) {
                let docs = p.element_docs();
                let v = p.start(NodeKind::Variant)?;
                p.attach_docs(docs);
                p.parse_name("variant name")?;
                // S-412: the `(` of the fields of a variant follows the
                // rule of the postfix `(` (a blank before it is E0020).
                if p.touches(TokenKind::LParen, true, false) {
                    let f = p.start(NodeKind::VariantFields)?;
                    p.bump();
                    while !p.at(TokenKind::RParen) {
                        p.parse_type()?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::VariantFields, TokenKind::RParen)?;
                    p.complete(f, NodeKind::VariantFields);
                } else if p.at(TokenKind::LBrace) {
                    let t = p.peek();
                    return Err(p.error(
                        Code::E0002,
                        t.span,
                        "enum variants are tuple-like or unit; wrap named fields in a struct (§4.4)",
                    ));
                }
                p.complete(v, NodeKind::Variant);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.close_list(NodeKind::VariantList, TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(l, NodeKind::VariantList);
        self.complete(m, NodeKind::Enum);
        Ok(())
    }

    /// `type Name = T` (alias) or `type Name` (opaque, in `extern` / `target`).
    pub(super) fn parse_type_item(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::TypeAlias)?;
        self.expect(TokenKind::KwType)?;
        let name = self.parse_name("type name")?;
        if self.eat(TokenKind::Eq).is_some() {
            if ctx == ItemCtx::Extern {
                return Err(self.error(Code::E0002, name.span, "an opaque type in `extern` has no definition"));
            }
            self.parse_type()?;
            self.complete(m, NodeKind::TypeAlias);
            Ok(())
        } else if ctx == ItemCtx::Extern {
            self.complete(m, NodeKind::OpaqueType);
            Ok(())
        } else {
            Err(self.unexpected("`=` (a type alias needs a definition)"))
        }
    }

    pub(super) fn parse_trait(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Trait)?;
        self.expect(TokenKind::KwTrait)?;
        self.parse_name("trait name")?;
        self.parse_generics_opt()?;
        self.parse_item_body(ItemCtx::Trait)?;
        self.complete(m, NodeKind::Trait);
        Ok(())
    }

    pub(super) fn parse_impl(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Impl)?;
        self.expect(TokenKind::KwImpl)?;
        self.parse_generics_opt()?;
        // The type parameters of `impl` after a blank (`impl [T] P[T]`, S-412)
        // are not read as an array type: a `[` with no `;` in it is the
        // list `touches` did not read.
        let at = self.peek_index();
        if self.detached.is_some_and(|d| d.at == at)
            && crate::scan::bracket_contents(&self.tokens, at).is_some_and(|(_, _, semi)| !semi)
        {
            return Err(self.unexpected("a type"));
        }
        let (first, args) = self.parse_type_ex()?;
        self.parse_clock_opt()?;
        if self.eat(TokenKind::KwFor).is_some() {
            if !(first.kind == NodeKind::PathType && args == 0) {
                return Err(self.error(Code::E0002, first.span, "expected a trait name before `for`"));
            }
            self.parse_type()?;
        }
        self.parse_item_body(ItemCtx::Impl)?;
        self.complete(m, NodeKind::Impl);
        Ok(())
    }

    pub(super) fn parse_effect(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Effect)?;
        self.eat(TokenKind::KwBlocking);
        self.expect(TokenKind::KwEffect)?;
        self.parse_name("effect name")?;
        self.parse_item_body(ItemCtx::Effect)?;
        self.complete(m, NodeKind::Effect);
        Ok(())
    }

    pub(super) fn parse_handler(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Handler)?;
        self.expect(TokenKind::KwHandler)?;
        self.parse_name("handler name")?;
        if self.at(TokenKind::LParen) {
            self.parse_params(true, false)?;
        }
        self.expect(TokenKind::Colon)?;
        self.parse_path("effect name")?;
        self.parse_item_body(ItemCtx::Handler)?;
        self.complete(m, NodeKind::Handler);
        Ok(())
    }

    pub(super) fn parse_const(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Const)?;
        self.expect(TokenKind::KwConst)?;
        self.parse_name("constant name")?;
        self.expect(TokenKind::Colon)?;
        self.parse_type()?;
        if self.eat(TokenKind::Eq).is_some() {
            self.parse_expr()?;
        } else if ctx != ItemCtx::Trait {
            return Err(self.unexpected("`=` (a constant needs a value)"));
        }
        self.complete(m, NodeKind::Const);
        Ok(())
    }

    pub(super) fn parse_use(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Use)?;
        self.expect(TokenKind::KwUse)?;
        let tree = self.start(NodeKind::UseTree)?;
        // The head of the path of a `use` reads a keyword as a name, as
        // after a `.` (S-20, S-37, S-371: `use test.{Gen}` in std).
        // SPEC-GAP(S-443): a reserved word there too (`use clock.{x}`).
        self.parse_name_after_dot("module path")?;
        loop {
            if self.dot_apart() {
                return Err(self.fail(Want::Postfix, "a member `.` without spaces around it"));
            }
            if self.eat(TokenKind::Dot).is_none() {
                break;
            }
            if self.at(TokenKind::LBrace) {
                let n = self.start(NodeKind::UseNames)?;
                self.bump();
                self.with_nl(false, |p| {
                    while !p.at(TokenKind::RBrace) {
                        p.parse_ident("imported name")?;
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.close_list(NodeKind::UseNames, TokenKind::RBrace)?;
                    Ok(())
                })?;
                self.complete(n, NodeKind::UseNames);
                break;
            }
            if self.at(TokenKind::Star) {
                let t = self.peek();
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "there is no glob import; list the names in `{ }` (§15.1)",
                ));
            }
            self.parse_name_after_dot("module path")?;
        }
        self.complete(tree, NodeKind::UseTree);
        self.complete(m, NodeKind::Use);
        Ok(())
    }

    pub(super) fn parse_extern(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Extern)?;
        self.expect(TokenKind::KwExtern)?;
        self.expect(TokenKind::Str)?;
        let t = self.peek();
        if !self.is_ident(t, "lib") {
            return Err(self.unexpected("`lib`"));
        }
        self.bump();
        self.expect(TokenKind::Str)?;
        self.parse_item_body(ItemCtx::Extern)?;
        self.complete(m, NodeKind::Extern);
        Ok(())
    }

    pub(super) fn parse_target(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Target)?;
        self.expect(TokenKind::KwTarget)?;
        match self.peek_kind() {
            TokenKind::KwType => {
                let o = self.start(NodeKind::OpaqueType)?;
                self.bump();
                self.parse_name("type name")?;
                self.complete(o, NodeKind::OpaqueType);
            }
            TokenKind::KwFn | TokenKind::KwRt => self.parse_fn(ItemCtx::Extern)?,
            _ => return Err(self.unexpected("`fn` or `type` after `target`")),
        }
        self.complete(m, NodeKind::Target);
        Ok(())
    }

    pub(super) fn parse_test(&mut self, _: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::Test)?;
        self.expect(TokenKind::KwTest)?;
        let name = self.expect(TokenKind::Str)?;
        self.check_test_name(name);
        self.parse_body()?;
        self.complete(m, NodeKind::Test);
        Ok(())
    }

    /// The name of a `test` (spec §11.8, S-244): a string literal with no
    /// interpolation, not empty, and with no control character, line
    /// separator or bidirectional control in its value
    /// ([`crate::test_name::problem`]). A name that breaks the rule is E0002
    /// of the syntax stage at the literal, with the rule as a note and no fix.
    /// The error does not stop the unit: the body is read, and the item is a
    /// failed one whose body is not checked (S-59).
    ///
    /// A hole is an interpolation whatever its form: the lexer's E0001 on the
    /// form of a hole (`{X}`, which is about the interpolation of an
    /// expression) gives way to the name's E0002. Any other error of the
    /// lexer in the literal (an escape, a hole without its `}`) makes the
    /// literal itself wrong, and the name is not checked further.
    fn check_test_name(&mut self, t: Token) {
        // The holes of this literal, found by a binary search.
        let holes: Vec<Span> = self.literals.holes_in(t.span).iter().map(|h| h.span).collect();
        // The places of the lexer's reports of a reserved word at the head of
        // a hole ([`crate::literal::Hole::reserved_head`]).
        let reserved: Vec<Span> = self.literals.holes_in(t.span).iter().filter_map(|h| h.reserved_head).collect();
        let problem = if holes.is_empty() {
            if !self.literals.ok(t.span) {
                return;
            }
            let lit = crate::literal::str_lit(self.text, t.span, &[]);
            let Some(value) = crate::test_name::value(&lit) else {
                onsa_diag::internal::bug(Some(t.span), "a literal without holes read as one with an interpolation")
            };
            match crate::test_name::problem(&value) {
                Some(p) => p,
                None => return,
            }
        } else {
            let before = self.diagnostics.len();
            let mut i = 0;
            self.diagnostics.retain(|d| {
                let lexer = i < self.lexed;
                i += 1;
                // The E0001 of the form of a hole (its span is the hole's),
                // and the report of a reserved word at its head.
                let of_hole = (d.code == Code::E0001 && holes.contains(&d.span)) || reserved.contains(&d.span);
                !(lexer && of_hole)
            });
            self.lexed -= before - self.diagnostics.len();
            // `literals` keeps their spans: they lie in this literal, which
            // no other name shares.
            "the name of a test cannot hold an interpolation".to_string()
        };
        let d = Diagnostic::new(Stage::Syntax, Code::E0002, t.span, problem)
            .with_found(self.src(t.span).to_string())
            .with_rule(crate::test_name::RULE);
        self.report(d);
    }

    /// `{ item NL item NL ... }` for trait / impl / effect / handler / extern bodies.
    pub(super) fn parse_item_body(&mut self, ctx: ItemCtx) -> PResult<()> {
        let m = self.start(NodeKind::ItemList)?;
        self.e0003_unless_on_the_line(TokenKind::LBrace);
        self.expect(TokenKind::LBrace)?;
        let base = self.braces.len();
        self.with_nl(true, |p| {
            loop {
                let doc = p.collect_docs();
                if p.at(TokenKind::RBrace) {
                    break;
                }
                if p.at(TokenKind::Eof) {
                    return Err(p.unexpected("`}`"));
                }
                // The `{` of the list is never closed, and an item starts on a
                // line indented as much as or less than the line of the `{`:
                // the list ends there, and the item is the next of the file
                // (§18.1). The top-level recovery reports the `{`. A correct
                // program closes every `{`, so its reading does not change.
                if ctx != ItemCtx::InlineHandler && p.list_ends_unclosed(base) {
                    return Err(ParseError);
                }
                let start = p.peek().span.start;
                let depth = p.open.len();
                let item = p.start_item(doc);
                if let Err(e) = p.parse_item(ctx, item) {
                    // A member is a unit of its own (spec §18.1, S-59): the
                    // list goes on after it. The handler written inside an
                    // expression is part of the unit around it.
                    if ctx == ItemCtx::InlineHandler {
                        return Err(e);
                    }
                    p.close_open(depth + 1);
                    p.skip_unit(start, base, true, false);
                    p.close_open(depth);
                    continue;
                }
                match p.peek_kind() {
                    TokenKind::Newline | TokenKind::RBrace => {}
                    _ if ctx == ItemCtx::InlineHandler => return Err(p.unexpected("newline or `}`")),
                    _ => {
                        // The tokens after the member on its line are of its
                        // unit (`crate::units`, S-274).
                        let _ = p.unexpected("newline or `}`");
                        p.skip_unit(start, base, true, true);
                    }
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(())
        })?;
        self.complete(m, NodeKind::ItemList);
        Ok(())
    }
}
