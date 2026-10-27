//! The scopes of a body: the tree of the scopes, the declaration of a
//! binding, the lookup of a local name and the captures of the anonymous
//! functions (§5.1, §5.3).

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Edit, Fix, Stage};
use onsa_syntax::ast::{Ast, ExprId, Ident, PatId, PatKind};

use super::{Binding, BindingId, BindingKind, BodyNames, Fail, Origin, ScopeId, ScopeInfo, Stop, W, Walker};
use crate::names::clash::hides;

/// A name a declaration hid, and the binding it named before (none if none).
type Hidden = (String, Option<BindingId>);

/// The state of the scopes while a body is walked.
#[derive(Default)]
pub(super) struct Scopes {
    /// The bindings visible here, by name.
    visible: HashMap<String, BindingId>,
    /// The open scopes, innermost last, each with what its declarations hid
    /// (a name declared again while visible, the E0304 of a `let` of a flow
    /// body declared ahead of it), to give back when it closes.
    open: Vec<(ScopeId, Vec<Hidden>)>,
    /// The open anonymous functions, innermost last, with the number of the
    /// bindings declared before each (those are outside it) and the bindings
    /// it captures so far.
    closures: Vec<(ExprId, u32, HashSet<BindingId>)>,
}

impl Walker<'_> {
    pub(super) fn open_scope(&mut self) {
        let parent = self.scopes.open.last().map(|(s, _)| *s);
        let id = ScopeId(self.out.scopes.len() as u32);
        self.out.scopes.push(ScopeInfo { parent, bindings: Vec::new() });
        self.scopes.open.push((id, Vec::new()));
    }

    pub(super) fn close_scope(&mut self) {
        let (_, hidden) = self.scopes.open.pop().expect("an open scope");
        for (name, prev) in hidden.into_iter().rev() {
            match prev {
                Some(b) => self.scopes.visible.insert(name, b),
                None => self.scopes.visible.remove(&name),
            };
        }
    }

    /// Declare a binding in the innermost scope, `site` the pattern that
    /// binds it: E0304 when it hides a name it sees (§5.1, no shadowing: a
    /// local or a parameter of the heading visible here, a name of the
    /// module, a builtin name of a flow for an input, a `let` and the index
    /// of a `par` of a flow;
    /// [`hides`]), which stops the walk ([`Walker::fail_at_let`]).
    pub(super) fn declare(
        &mut self,
        name: &Ident,
        kind: BindingKind,
        origin: Origin,
        site: Option<PatId>,
    ) -> Result<BindingId, Stop> {
        let local = self.scopes.visible.get(&name.name).map(|b| self.out.bindings[b.0 as usize].span);
        let visible = local.or_else(|| self.generics.iter().find(|g| g.name == name.name).map(|g| g.span));
        let flow = match kind {
            BindingKind::FlowInput | BindingKind::FlowLet => true,
            BindingKind::ParVar => self.flow,
            _ => false,
        };
        if let Some(d) = hides(self.a, self.m, name, visible, flow) {
            self.fail_at_let(Fail::Report(d))?;
        }
        let (scope, hidden) = self.scopes.open.last_mut().expect("an open scope");
        let id = BindingId(self.out.bindings.len() as u32);
        self.out.bindings.push(Binding {
            name: name.name.clone(),
            span: name.span,
            kind,
            sites: site.into_iter().collect(),
            origin,
            scope: *scope,
            reads: 0,
        });
        self.out.scopes[scope.0 as usize].bindings.push(id);
        let prev = self.scopes.visible.insert(name.name.clone(), id);
        hidden.push((name.name.clone(), prev));
        Ok(id)
    }

    /// Check the names `declare` declares before the walk reads what is
    /// after them in the text and before them in the walk (the value of a
    /// `let` or a `var`, the iterated value of a `for`, the range of a
    /// `par`): the first error of a unit is the first in the text (§18.1,
    /// R-289). They are declared in a scope of their own and taken back with
    /// their records; the walk declares them again after the value.
    pub(super) fn ahead(&mut self, declare: impl FnOnce(&mut Self) -> W) -> W {
        let (bindings, scopes) = (self.out.bindings.len(), self.out.scopes.len());
        self.open_scope();
        declare(self)?;
        self.close_scope();
        for b in self.out.bindings.drain(bindings..) {
            for p in b.sites {
                self.out.pats.remove(&p);
            }
        }
        self.out.scopes.truncate(scopes);
        Ok(())
    }

    /// The bindings visible here, from the outermost scope (a typed hole).
    pub(super) fn visible(&self) -> Vec<BindingId> {
        let scopes = self.scopes.open.iter().map(|(s, _)| &self.out.scopes[s.0 as usize].bindings);
        scopes.flat_map(|bs| bs.iter().copied()).collect()
    }

    /// The local binding `name` names here, read: the read counts for
    /// E0309 and, for a binding outside the open anonymous functions, is a
    /// capture of each of them. A binding an open function captures already
    /// is captured by those around it that it is outside of, so the marking
    /// stops at the first that has it.
    pub(super) fn lookup(&mut self, name: &str) -> Option<BindingId> {
        let id = *self.scopes.visible.get(name)?;
        self.out.bindings[id.0 as usize].reads += 1;
        for (closure, base, seen) in self.scopes.closures.iter_mut().rev() {
            if id.0 >= *base || !seen.insert(id) {
                break;
            }
            self.out.captures.entry(*closure).or_default().push(id);
        }
        Some(id)
    }

    /// Take back the read of the binding `name` names here, which was the
    /// root of the target of an assignment (no read, §5.1).
    pub(super) fn unread(&mut self, name: &str) {
        if let Some(id) = self.scopes.visible.get(name) {
            let b = &mut self.out.bindings[id.0 as usize];
            b.reads = b.reads.saturating_sub(1);
        }
    }

    /// Enter the anonymous function `e` (before its parameters).
    pub(super) fn open_closure(&mut self, e: ExprId) {
        self.out.captures.entry(e).or_default();
        self.scopes.closures.push((e, self.out.bindings.len() as u32, HashSet::new()));
    }

    pub(super) fn close_closure(&mut self) {
        self.scopes.closures.pop();
    }
}

/// The E0309 of every binding of the complete record `out` of a body of the
/// fn world that is never read (§5.1, S-129): a `let`, a `var`, a `for` and
/// a pattern of an arm, no parameter. It is of the last stage (§18.1,
/// S-726): the unit reports the first, and none when it has another error.
/// At the name where it is first bound; the candidate renames every site
/// to `_` (each branch of a choice), and a `var` has none (`var _` is no
/// form, S-714).
pub(super) fn unused<'a>(out: &'a BodyNames, ast: &'a Ast) -> impl Iterator<Item = Diagnostic> + 'a {
    let counted = |k: BindingKind| {
        matches!(k, BindingKind::Let | BindingKind::Var | BindingKind::For { .. } | BindingKind::MatchBind)
    };
    out.bindings.iter().filter(move |b| b.reads == 0 && counted(b.kind)).map(move |b| {
        let message = format!("`{}` is bound and never read; a value that is not used is bound to `_` (§5.1)", b.name);
        let d = Diagnostic::new(Stage::Unused, Code::E0309, b.span, message).with_found(b.name.clone());
        if b.kind == BindingKind::Var {
            return d.with_rule("a `var` cannot be named `_`: write `let _ = e` for a value that is not used");
        }
        let names = b.sites.iter().filter_map(|&p| match &ast.pat(p).kind {
            PatKind::Bind(name) => Some(Edit::replace(name.span, "_")),
            _ => None,
        });
        d.with_fix(Fix::new("rename to `_`", names.collect()))
    })
}
