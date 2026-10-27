//! The scopes of a body: the tree of the scopes, the declaration of a
//! binding, the lookup of a local name and the captures of the anonymous
//! functions (§5.1, §5.3).

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Stage};
use onsa_syntax::ast::{ExprId, Ident, PatId};

use super::{Binding, BindingId, BindingKind, Fail, Origin, ScopeId, ScopeInfo, Stop, Walker};

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
    /// binds it: E0304 when its name is visible (§5.1, no shadowing), which
    /// stops the walk ([`Walker::fail_at_let`]).
    pub(super) fn declare(
        &mut self,
        name: &Ident,
        kind: BindingKind,
        origin: Origin,
        site: Option<PatId>,
    ) -> Result<BindingId, Stop> {
        if name.name != "_"
            && let Some(prev) = self.scopes.visible.get(&name.name)
        {
            let msg = format!("`{}` is already bound and visible here; Onsa has no shadowing (§5.1)", name.name);
            let d = Diagnostic::new(Stage::Names, Code::E0304, name.span, msg)
                .with_found(name.name.clone())
                .with_note(self.out.bindings[prev.0 as usize].span, "first bound here");
            self.fail_at_let(Fail::Report(d), true)?;
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
