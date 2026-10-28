//! The nodes of the parser: the trial readings, and the nodes of the CST
//! that it opens and closes with the levels they count (§2.5, E0006).

use super::*;

impl<'a> Parser<'a> {
    /// The state before a trial reading: a reading that fails is undone with
    /// [`Parser::restore`] (its events and diagnostics are dropped). A trial
    /// opens and closes only nodes of its own (no `precede` of a node read
    /// before it).
    pub(super) fn snapshot(&mut self) -> Snapshot {
        self.trials += 1;
        Snapshot {
            pos: self.pos,
            last_end: self.last_end,
            events: self.events.len(),
            diagnostics: self.diagnostics.len(),
            open: self.open.clone(),
            closed: self.closed.clone(),
            braces: self.braces.clone(),
            nl: self.nl.clone(),
            no_struct_lit: self.no_struct_lit,
            detached: self.detached,
            ends: self.ends.len(),
            prefixed: self.prefixed.len(),
        }
    }

    /// Undo the reading since `s`.
    pub(super) fn restore(&mut self, s: Snapshot) {
        self.end_trial();
        self.pos = s.pos;
        self.last_end = s.last_end;
        self.events.truncate(s.events);
        self.diagnostics.truncate(s.diagnostics);
        self.open = s.open;
        self.closed = s.closed;
        self.braces = s.braces;
        self.nl = s.nl;
        self.no_struct_lit = s.no_struct_lit;
        self.detached = s.detached;
        self.ends.truncate(s.ends);
        self.prefixed.truncate(s.prefixed);
    }

    /// Keep the reading since the snapshot.
    pub(super) fn end_trial(&mut self) {
        self.trials -= 1;
    }

    // ------------------------------------------------------------ nodes

    /// The one place where nodes open (`start`, `precede`, the recovery,
    /// the doc comments of an item). `children` is the height of what the
    /// node wraps already (for `precede`). A node whose subtree reaches a
    /// level over [`NESTING_LIMIT`] is E0006 at the next token, the token that
    /// makes the level (spec §2.5); nothing is opened then.
    pub(super) fn enter(&mut self, kind: NodeKind, start: u32, children: u32) -> PResult<Marker> {
        let base = self.level();
        self.limit(base + Self::height(kind, children), self.peek().span, kind)?;
        let event = self.events.len() as u32;
        self.events.push(Event::Start { kind: Some(kind), forward_parent: None });
        self.open.push(Open { event, start, children, level: base + Self::height(kind, 0) });
        Ok(Marker { event, start })
    }

    /// Open a node of no level (an item, its doc comments, the skipped
    /// tokens of the recovery, the file): it never reaches the limit.
    pub(super) fn enter_unit(&mut self, kind: NodeKind, start: u32) -> Marker {
        debug_assert_eq!(Self::height(kind, 0), 0, "{kind:?} is not a node of no level");
        self.enter(kind, start, 0).unwrap_or_else(|ParseError| {
            onsa_diag::internal::bug(Some(self.peek().span), format!("{kind:?} counts a level"))
        })
    }

    /// Open a node at the next token.
    pub(super) fn start(&mut self, kind: NodeKind) -> PResult<Marker> {
        let start = self.peek().span.start;
        self.enter(kind, start, 0)
    }

    /// Whether the parser reads inside a type (a const argument or the
    /// length of an array type): an expression there has no `::[…]` (R-196).
    pub(super) fn in_type(&self) -> bool {
        self.open.iter().any(|o| {
            matches!(self.events[o.event as usize], Event::Start { kind: Some(k), .. }
                if k.class() == Class::Type)
        })
    }

    /// The level of the innermost open node (0 outside every node).
    pub(super) fn level(&self) -> u32 {
        self.open.last().map_or(0, |o| o.level)
    }

    /// The height of the subtree of a node of `kind` whose highest child has
    /// height `children`: the one function that counts the depth of the
    /// syntax (spec §2.5, S-221). Each form of an expression, a type or a
    /// pattern and each block is one level; names, literals, `_`, lists,
    /// statements and the headers of declarations are none, so a node of no
    /// level never nests in another without a node of one level between
    /// them. No wildcard: a new kind of node decides its level here.
    pub(crate) fn height(kind: NodeKind, children: u32) -> u32 {
        use NodeKind::*;
        let level = match kind {
            // The file, the items and their headers: a unit starts from 0.
            SourceFile | Error | Name | Item | Docs | ModuleDocs | Attr | AttrArgs | AttrNamedArg | Vis | Fn | Flow
            | Struct | FieldList | Field | Derives | Enum | VariantList | Variant | VariantFields | TypeAlias
            | OpaqueType | Trait | Impl | Effect | Handler | Const | Use | UseTree | UseNames | Extern | Target
            | Test | ItemList | GenericParams | TypeParam | ConstParam | EffectParam | Bound | ParamList | Param
            | EffectRow | Path => 0,
            // Types: a type with arguments counts at its `[` (the `TypeArgs`), a name none.
            PathType | ConstArg | FnTypeParams => 0,
            TypeArgs | UnitType | TupleType | ParenType | ArrayType | FnType => 1,
            // Statements are none, the loops one (and their blocks one more).
            LetStmt | VarStmt | BreakStmt | ContinueStmt | ReturnStmt | AssertStmt | AssignStmt | ExprStmt => 0,
            ForStmt | WhileStmt | Block => 1,
            // Expressions. A binary chain is flat in the tree: its height is
            // the one of the tree of §3.1, one level per operator ([`ChainHeight`]).
            // A `::[…]` counts at its `[` (the `TypeArgs`), as a type with arguments.
            Literal | HoleExpr | PathExpr | BinaryExpr | MatchArms | MatchArm | ArgList | Arg | StructLitFields
            | StructLitField | TypeArgsExpr | FeedbackExpr => 0,
            // SPEC-GAP(S-361): the clock of an input or output counts no level
            // (the heading counts none); in an expression it is in an `AtExpr`.
            Clock => 0,
            ParenExpr | TupleExpr | ArrayExpr | RepeatExpr | IfExpr | MatchExpr | ClosureExpr | HandleExpr
            | UnsafeExpr | ParExpr | MoveExpr | RangeExpr | CastExpr | AtExpr | PrefixExpr | CallExpr | FieldExpr
            | TupleIndexExpr | IndexExpr | TryExpr | StructLit => 1,
            // Patterns: `|` is one level for all its alternatives.
            WildPat | LitPat | NegLitPat | BindPat | PathPat | StructPatField | StructPatRest => 0,
            TuplePat | ParenPat | TupleStructPat | StructPat | OrPat => 1,
        };
        children + level
    }

    /// E0006 when a form whose subtree reaches level `total` is over the
    /// limit; `at` is the token that makes its level.
    pub(super) fn limit(&mut self, total: u32, at: Span, kind: NodeKind) -> PResult<()> {
        if total <= NESTING_LIMIT {
            return Ok(());
        }
        Err(self.too_deep(at, kind))
    }

    /// E0006 at `at`, the token of a form of `kind` over the limit (spec §2.5).
    /// The note says how to split the form: an expression into a `let`, a
    /// type into a named `struct` (an alias expands to the same depth,
    /// §4.4), a block into a function. The unit is not
    /// read further: the error goes up to the recovery.
    pub(super) fn too_deep(&mut self, at: Span, kind: NodeKind) -> ParseError {
        use NodeKind::*;
        let split = match (kind, kind.class()) {
            (Block | ForStmt | WhileStmt, _) => {
                "move the inner blocks into a function and call it; a function starts again from level 0"
            }
            (TypeArgs | FnTypeParams, _) | (_, Class::Type) => {
                "name an inner part of the type with a `struct`; a `type` alias expands to the same depth"
            }
            (StructPatField, _) | (_, Class::Pat) => "bind an inner part to a name and match that name on its own",
            _ => "bind an inner part to a name with `let`, or move it into a function",
        };
        let message =
            format!("the syntax is nested deeper than {NESTING_LIMIT} levels, counted from the declaration (§2.5)");
        let d = Diagnostic::new(Stage::Syntax, Code::E0006, at, message)
            .with_found(self.src(at).to_string())
            .with_rule(split);
        self.report(d);
        ParseError
    }

    /// The innermost open node becomes a node of `kind` at the next token: a
    /// pattern that starts with a name is an enum or struct pattern from its
    /// `(` or `{` on (spec §2.5: the level is made by the bracket after the name).
    pub(super) fn reshape(&mut self, kind: NodeKind) -> PResult<()> {
        let n = self.open.len();
        let Some(top) = self.open.last().copied() else {
            onsa_diag::internal::bug(Some(self.peek().span), "the parser reshapes a node it did not open");
        };
        let base = if n >= 2 { self.open[n - 2].level } else { 0 };
        self.limit(base + Self::height(kind, top.children), self.peek().span, kind)?;
        if let Event::Start { kind: k, .. } = &mut self.events[top.event as usize] {
            *k = Some(kind);
        }
        self.open[n - 1].level = base + Self::height(kind, 0);
        Ok(())
    }

    /// Count a form written without a node of its own (`move x` as an
    /// argument or the iterated value of `for`, spec §5.2: the form `move`)
    /// at the token `at`: what `f` reads is one form of `kind` deeper.
    pub(super) fn without_node(
        &mut self,
        kind: NodeKind,
        at: Span,
        f: impl FnOnce(&mut Self) -> PResult<Completed>,
    ) -> PResult<Completed> {
        let n = self.open.len();
        let saved = self.open[n - 1].level;
        self.limit(saved + Self::height(kind, 0), at, kind)?;
        self.open[n - 1].level = saved + Self::height(kind, 0);
        let inner = f(self)?;
        self.open[n - 1].level = saved;
        let top = &mut self.open[n - 1];
        top.children = top.children.max(Self::height(kind, inner.height));
        Ok(inner)
    }

    /// Close the innermost open node; its height goes to its parent.
    pub(super) fn finish(&mut self, kind: Option<NodeKind>, complete: bool) -> (u32, u32) {
        let Some(top) = self.open.pop() else {
            onsa_diag::internal::bug(Some(self.peek().span), "the parser closes a node it did not open");
        };
        if let Some(kind) = kind
            && let Event::Start { kind: k, .. } = &mut self.events[top.event as usize]
        {
            *k = Some(kind);
        }
        let kind = match self.events[top.event as usize] {
            Event::Start { kind: Some(k), .. } => k,
            _ => NodeKind::Error,
        };
        let h = Self::height(kind, top.children);
        if kind == NodeKind::Item {
            self.items.push((top.start, h));
        }
        match self.open.last_mut() {
            Some(parent) => parent.children = parent.children.max(h),
            None => self.height = h,
        }
        self.events.push(Event::Finish { complete });
        (top.event, h)
    }

    /// Close the innermost open node `m` as `kind`; a statement or a
    /// declaration records what it ends with ([`End::of`], [`Parser::ends`]).
    pub(super) fn complete(&mut self, m: Marker, kind: NodeKind) -> Completed {
        debug_assert_eq!(self.open.last().map(|o| o.event), Some(m.event), "nodes close in order");
        if let Some(end) = End::of(kind) {
            self.end_with(end);
        }
        let (event, height) = self.finish(Some(kind), true);
        self.closed.push((kind, m.start));
        Completed { kind, event, start: m.start, span: self.span_from(m.start), height }
    }

    /// The last token read, its last code token (not a comment), ends a
    /// statement or a declaration with `end` ([`Parser::ends`]).
    fn end_with(&mut self, end: End) {
        if let Some(last) = (0..self.pos).rev().find(|&k| self.tokens[k].kind.is_code()) {
            // In order (the table searches them): a statement ends after the
            // ones before it, and a declaration after its own statements.
            debug_assert!(self.ends.last().is_none_or(|e| e.0 <= last), "the ends out of order");
            if self.ends.last().is_some_and(|e| e.0 == last) {
                // A declaration ends where its last statement did (`fn f() { for … { } }`
                // does not end there): the outer one says what follows.
                self.ends.pop();
            }
            self.ends.push((last, end));
        }
    }

    /// Open a node that wraps the closed node `c` (a postfix, a chain, a
    /// cast): the left of a chain is counted too, so the first postfix that
    /// makes the chain too deep is the E0006, before the chain is read on.
    pub(super) fn precede(&mut self, c: Completed, kind: NodeKind) -> PResult<Marker> {
        let m = self.enter(kind, c.start, c.height)?;
        if let Event::Start { forward_parent, .. } = &mut self.events[c.event as usize] {
            *forward_parent = Some(m.event);
        }
        Ok(m)
    }

    /// Close every node opened above `depth` as incomplete (after an error).
    pub(super) fn close_open(&mut self, depth: usize) {
        while self.open.len() > depth {
            self.finish(None, false);
        }
    }
}
