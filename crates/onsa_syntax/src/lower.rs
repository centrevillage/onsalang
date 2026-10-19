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
//! ([`Cst::span`]); an operator inside a chain (the tree of §3.1 made from
//! one flat `BinaryExpr`) spans its operands.
//!
//! Where the code is: this module holds the reading of the tree, the
//! adding of the nodes, the types, the patterns and the literals;
//! `items` the items read whole, `failed` the heads of the items and the
//! items a syntax error stopped, and `exprs` the blocks, the statements
//! and the expressions.

use onsa_diag::Span;

use crate::ast::*;
use crate::cst::{Class, Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::literal::{Literals, char_value, int_value, str_lit, tuple_index_value};
use crate::token::TokenKind;

mod exprs;
mod failed;
mod items;

/// From each AST node to the CST node it was made from (same indices as the
/// arenas of [`Ast`]). The parts of the AST that are not arena nodes (`Ident`,
/// `Path`, `Param`, ...) are found with [`Cst::covering_nodes`].
#[derive(Debug, Default, Clone)]
pub struct AstMap {
    pub items: Vec<NodeId>,
    pub exprs: Vec<NodeId>,
    pub stmts: Vec<NodeId>,
    pub types: Vec<NodeId>,
    pub pats: Vec<NodeId>,
}

impl AstMap {
    /// The kind of the CST node the expression `e` was made from.
    pub(crate) fn expr_kind(&self, cst: &Cst, e: crate::ast::ExprId) -> NodeKind {
        cst.kind(self.exprs[e.0 as usize])
    }
}

/// Make the AST of `cst` (the source is `text`, the facts of its literals
/// `literals`, the lexer's).
pub(crate) fn lower(cst: &Cst, text: &str, literals: &Literals) -> (Ast, AstMap) {
    let mut l = Lower { cst, text, literals, ast: Ast::default(), map: AstMap::default() };
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

struct Lower<'a> {
    cst: &'a Cst,
    text: &'a str,
    literals: &'a Literals,
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

    /// The range `n`: the parser makes a range only of `..<` and `..=` (the
    /// other symbols fail, S-257).
    fn range_head(&mut self, n: NodeId) -> RangeHead {
        let end = self.cst.child_tokens(n).find_map(|t| self.kind_of(t).range_end());
        let end = end.unwrap_or_else(|| self.bug(n, "a range symbol `..<` or `..=`"));
        let e = self.exprs(n);
        RangeHead { lo: e[0], hi: e[1], end }
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
        self.cst.child_nodes(n).filter(|&k| self.cst.kind(k).class() == c).collect()
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

    /// The clock written after the type of `n` (a parameter, a function, a
    /// flow, an anonymous function, §11.3), when it was read whole. A clock
    /// anywhere else is not in the AST: it is an E0020 of its unit (S-356).
    fn clock(&self, n: NodeId) -> Option<Clock> {
        let c = self.child(n, NodeKind::Clock).filter(|&c| self.cst.is_complete(c))?;
        let t = self.tok(c, TokenKind::Ident)?;
        Some(Clock { name: self.ident(t), span: self.span(c) })
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
        self.ast.add_type(TypeExpr { span, kind, parens: 0 })
    }

    fn add_pat(&mut self, n: NodeId, kind: PatKind) -> PatId {
        self.map.pats.push(n);
        let span = self.span(n);
        self.ast.add_pat(Pat { span, kind, parens: 0 })
    }

    // ------------------------------------------------------------ types

    fn ty(&mut self, n: NodeId) -> TypeId {
        let kind = match self.cst.kind(n) {
            // `(T)` is `T` (§2.4, R-43); the parentheses are kept for fmt.
            NodeKind::ParenType => {
                let t = self.first_type(n).unwrap_or_else(|| self.bug(n, "a type"));
                self.ast.types[t.index()].parens += 1;
                return t;
            }
            NodeKind::PathType => {
                let path = self.path(self.need(n, NodeKind::Path));
                let args = match self.child(n, NodeKind::TypeArgs) {
                    Some(a) => self.of_class(a, Class::Type).into_iter().map(|t| self.ty(t)).collect(),
                    None => Vec::new(),
                };
                TypeKind::Path { path, args }
            }
            NodeKind::ConstArg => TypeKind::ConstArg(self.need_expr(n)),
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
                        // A clock in the list is an E0020 of its unit (S-356).
                        Elem::Node(c) if self.cst.kind(c).class() == Class::Type => {
                            let ty = self.ty(c);
                            params.push((std::mem::replace(&mut mode, Mode::Borrow), ty));
                        }
                        Elem::Node(_) => {}
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

    // ------------------------------------------------------------ patterns

    fn pat(&mut self, n: NodeId) -> PatId {
        let kind = match self.cst.kind(n) {
            // `(p)` is `p` (§2.4, R-43); the parentheses are kept for fmt.
            NodeKind::ParenPat => {
                let c = self.of_class(n, Class::Pat).into_iter().next().unwrap_or_else(|| self.bug(n, "a pattern"));
                let p = self.pat(c);
                self.ast.pats[p.index()].parens += 1;
                return p;
            }
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
                let rest = self.of_kind(n, NodeKind::StructPatRest).first().map(|&r| self.struct_rest(n, r));
                PatKind::Struct { path, fields, rest }
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
        str_lit(self.text, tok.span, self.literals.holes_in(tok.span))
    }
}
