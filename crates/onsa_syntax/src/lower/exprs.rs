//! The blocks, the statements and the expressions, with the binary chains
//! of §3.1.

use super::*;

impl<'a> Lower<'a> {
    // ------------------------------------------------------------ blocks and statements

    pub(super) fn block(&mut self, n: NodeId) -> ExprId {
        let block = self.block_body(n);
        let span = self.span(n);
        self.add_expr(n, span, ExprKind::Block(block))
    }

    pub(super) fn block_body(&mut self, n: NodeId) -> Block {
        let mut stmts: Vec<(NodeId, StmtKind)> = Vec::new();
        for s in self.nodes(n) {
            // The attributes before a statement that takes none: its E0005
            // was reported where it was read (`Parser::parse_stmt`).
            if self.cst.kind(s) == NodeKind::Attr {
                continue;
            }
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

    pub(super) fn stmt_kind(&mut self, n: NodeId) -> StmtKind {
        match self.cst.kind(n) {
            NodeKind::LetStmt => {
                let pat = self.of_class(n, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(n, "a pattern"));
                let pat = self.pat(pat);
                let ty = self.first_type(n);
                let init = self.need_expr(n);
                let attrs = self.of_kind(n, NodeKind::Attr);
                let attrs = attrs.into_iter().filter(|&a| self.cst.is_complete(a)).map(|a| self.attr(a)).collect();
                StmtKind::Let { attrs, pat, ty, init }
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

    pub(super) fn exprs(&mut self, n: NodeId) -> Vec<ExprId> {
        self.of_class(n, Class::Expr).into_iter().map(|e| self.expr(e)).collect()
    }

    pub(super) fn expr(&mut self, n: NodeId) -> ExprId {
        let kind = match self.cst.kind(n) {
            NodeKind::Literal => {
                let t = self.toks(n)[0];
                ExprKind::Lit(self.lit(t))
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
                let tilde = self.tok(n, TokenKind::Tilde).map(|t| self.cst.token(t).span);
                ExprKind::If { cond: e[0], then: e[1], else_: e.get(2).copied(), tilde }
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
                let tilde = self.tok(n, TokenKind::Tilde).map(|t| self.cst.token(t).span);
                ExprKind::Match { scrutinee, arms, tilde }
            }
            NodeKind::ClosureExpr => {
                let params = self.params(self.need(n, NodeKind::ParamList));
                let ret = self.first_type(n);
                let ret_clock = self.clock(n);
                let effects = self.child(n, NodeKind::EffectRow).map(|e| self.effect_row(e));
                let body = self.block(self.need(n, NodeKind::Block));
                ExprKind::Closure { params, ret, ret_clock, effects, body }
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
                let range = self.range_head(range);
                let body = self.block(self.need(n, NodeKind::Block));
                ExprKind::Par { var, range, body }
            }
            NodeKind::MoveExpr => ExprKind::Move(self.need_expr(n)),
            NodeKind::BinaryExpr => return self.chain(n),
            NodeKind::RangeExpr => ExprKind::Range(self.range_head(n)),
            NodeKind::CastExpr => {
                let expr = self.need_expr(n);
                let ty = self.first_type(n).unwrap_or_else(|| self.bug(n, "a type"));
                ExprKind::Cast { expr, ty }
            }
            NodeKind::AtExpr => {
                let expr = self.need_expr(n);
                let clock = self.clock(n).unwrap_or_else(|| self.bug(n, "a clock"));
                ExprKind::At { expr, clock }
            }
            NodeKind::FeedbackExpr => {
                let t = self.tok(n, TokenKind::Ident).unwrap_or_else(|| self.bug(n, "a name"));
                ExprKind::Feedback(self.ident(t))
            }
            NodeKind::PrefixExpr => {
                let op = if self.has(n, TokenKind::Minus) { UnOp::Neg } else { UnOp::Not };
                ExprKind::Unary { op, expr: self.need_expr(n) }
            }
            NodeKind::CallExpr => {
                let callee = self.need_expr(n);
                let kind = if self.has(n, TokenKind::Tilde) {
                    CallKind::Flow
                } else if self.has(n, TokenKind::Bang) {
                    CallKind::Bang
                } else if let Some(dot) = self.tok(n, TokenKind::Dot) {
                    CallKind::Value { dot: self.cst.token(dot).span }
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
            NodeKind::TypeArgsExpr => {
                let base = self.need_expr(n);
                ExprKind::TypeArgs { base, args: self.type_arg_list(n) }
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
                let (path, type_args) = self.struct_lit_path(callee);
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
                ExprKind::Struct { path, type_args, fields }
            }
            _ => self.bug(n, "the kind of an expression"),
        };
        let span = self.span(n);
        self.add_expr(n, span, kind)
    }

    /// A chain of binary operators (flat in the CST) as the tree of §3.1:
    /// one node per operator, each spanning its operands.
    pub(super) fn chain(&mut self, n: NodeId) -> ExprId {
        let tighter = |o: (BinOp, Span), w: (BinOp, Span)| o.0.group().stronger(w.0.group());
        let mut chain: Option<Chain<ExprId, (BinOp, Span)>> = None;
        for e in self.cst.children(n).to_vec() {
            match e {
                Elem::Node(c) => {
                    let operand = self.expr(c);
                    match &mut chain {
                        None => chain = Some(Chain::new(operand)),
                        Some(ch) => ch.operand(operand),
                    }
                }
                Elem::Token(t) => {
                    if let Some(op) = self.kind_of(t).binop() {
                        let span = self.cst.token(t).span;
                        let Some(ch) = &mut chain else { self.bug(n, "an operand") };
                        ch.operator((op, span), tighter, |l, o, r| self.binary(n, l, o, r));
                    }
                }
            }
        }
        let chain = chain.unwrap_or_else(|| self.bug(n, "an operand"));
        chain.finish(|l, o, r| self.binary(n, l, o, r))
    }

    pub(super) fn binary(&mut self, n: NodeId, lhs: ExprId, (op, op_span): (BinOp, Span), rhs: ExprId) -> ExprId {
        let (l, r) = (self.ast.expr(lhs).span, self.ast.expr(rhs).span);
        self.add_expr(n, Span::new(l.file, l.start, r.end), ExprKind::Binary { op, op_span, lhs, rhs })
    }

    /// The path of a struct literal from the names of its callee (`a.b.C`),
    /// and the type arguments written after its names (`E::[I32].V`): the
    /// index of the name each list follows.
    pub(super) fn struct_lit_path(&mut self, callee: NodeId) -> (Path, Vec<(usize, TypeArgList)>) {
        let mut segments = Vec::new();
        // The lists, with the number of names after the one each follows.
        let mut lists = Vec::new();
        let mut cur = callee;
        loop {
            if self.cst.kind(cur) == NodeKind::TypeArgsExpr {
                lists.push((segments.len(), self.type_arg_list(cur)));
                cur = self.first_expr(cur).unwrap_or_else(|| self.bug(cur, "a base"));
                continue;
            }
            let t = *self.toks(cur).last().unwrap_or_else(|| self.bug(cur, "a name"));
            segments.push(self.ident(t));
            match self.cst.kind(cur) {
                NodeKind::FieldExpr => cur = self.first_expr(cur).unwrap_or_else(|| self.bug(cur, "a base")),
                NodeKind::PathExpr => break,
                _ => self.bug(callee, "a chain of names"),
            }
        }
        segments.reverse();
        let last = segments.len() - 1;
        let mut lists: Vec<(usize, TypeArgList)> = lists.into_iter().map(|(after, l)| (last - after, l)).collect();
        lists.reverse();
        (Path { segments, span: self.span(callee) }, lists)
    }

    /// The list of a `::[…]` (a `TypeArgsExpr`): from its `::` to its `]`.
    pub(super) fn type_arg_list(&mut self, n: NodeId) -> TypeArgList {
        let list = self.need(n, NodeKind::TypeArgs);
        let args = self.of_class(list, Class::Type).into_iter().map(|t| self.ty(t)).collect();
        let colons = self.tok(n, TokenKind::ColonColon).unwrap_or_else(|| self.bug(n, "a `::`"));
        TypeArgList { args, span: self.cst.token(colons).span.to(self.span(list)) }
    }

    pub(super) fn args(&mut self, list: NodeId) -> Vec<Arg> {
        self.nodes(list)
            .into_iter()
            .map(|a| {
                let mode = self.mode(a);
                let expr = self.need_expr(a);
                Arg { mode, expr, span: self.span(a) }
            })
            .collect()
    }
}
