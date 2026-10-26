//! The clashes of names (spec §15.1, §5.1, §2.2, S-611): E0304 for two names
//! of one space. The spaces are the body of a module (its items, the names
//! its `use` bound, the prelude and the builtin types), the namespace of a
//! module (its items and its child modules), and the heads of the paths of
//! `use` (the modules under the root and the packages depended on). Two items
//! of a module are an E0304 (E0305 with a flow) where they are declared
//! (`super::collect`).
//!
//! The name of an E0304 is an error in its space (§18.1, S-675): a use of it
//! reads neither side ([`crate::resolve::Clashed`], `Modules::clashed_heads`).
//! The side reported (§15.1) is the declaration of the module against a name
//! from outside the source, the `use` against an item, and the later of two
//! of a kind; the side not reported is checked.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Span, Stage};

use crate::def::{DefId, ModId};
use crate::sig::Sema;

/// Why a `use` cannot bind a name, whatever it takes (§15.1, §2.2).
pub(crate) enum Unbindable {
    /// A keyword or a reserved word: the syntax stage's E0002 or E0200
    /// (R-266, R-275), of the one table [`onsa_syntax::token::not_a_name`].
    NotAName,
    /// A builtin name of a flow, which a flow body sees: E0304 (S-542).
    FlowBuiltin,
}

/// Whether a `use` can bind `name`: the one test of the names a `use` takes
/// (`super::imports`), of the E0304 here and of the candidates that add a
/// `use` (`super::lookup`).
pub(crate) fn unbindable(name: &str) -> Option<Unbindable> {
    if onsa_syntax::token::not_a_name(name).is_some() {
        Some(Unbindable::NotAName)
    } else {
        crate::flow_names::is_builtin(name).then_some(Unbindable::FlowBuiltin)
    }
}

impl<'p> Sema<'p> {
    /// The E0304 of the items and of the heads, before any `use` is resolved
    /// (a `use` reads the namespaces and the heads).
    pub(crate) fn check_item_clashes(&mut self) {
        for i in 0..self.a.modules.mods.len() {
            self.item_clashes(ModId(i as u32));
        }
        self.head_clashes();
    }

    /// The E0304 of the names the `use` bound, once every `use` is resolved.
    pub(crate) fn check_use_clashes(&mut self) {
        for i in 0..self.a.modules.mods.len() {
            self.use_clashes(ModId(i as u32));
            self.drop_clashed_deps(ModId(i as u32));
        }
    }

    /// The names of an E0304 or an E0305 in the body of `m` make no
    /// dependency (§15.1, §18.1, S-688): of each `use` that binds one, the
    /// side reported or not; the other names of the `use` make theirs (S-685).
    fn drop_clashed_deps(&mut self, m: ModId) {
        let info = self.a.modules.get_mut(m);
        let clashed: HashSet<Span> =
            info.bound.iter().filter(|(name, _)| info.clashed.body.contains(name)).map(|&(_, span)| span).collect();
        info.deps.retain(|d| !clashed.contains(&d.name));
    }

    /// The items of `m` of a name of the prelude or a builtin name of a
    /// flow (the body), or of the name of a child module (the namespace).
    fn item_clashes(&mut self, m: ModId) {
        let info = self.a.modules.get(m);
        let mut items: Vec<DefId> = info.items.values().copied().collect();
        items.sort();
        for d in items {
            let def = self.a.def(d);
            let (name, span) = (def.name.clone(), def.name_span);
            // An item of `std.core` is itself the name of the prelude (S-659).
            let own = self.a.prelude.get(&name) == Some(&crate::resolve::Entity::Def(d));
            let body = if own { None } else { self.body_clash(&name, span, "an item") };
            let child = self.a.modules.get(m).children.get(&name).copied().map(|c| {
                clash(span, &name, format!("`{name}` is also the name of a child module"))
                    .with_note(self.module_head(c), "the child module")
            });
            let clashed = &mut self.a.modules.get_mut(m).clashed;
            if body.is_some() {
                clashed.body.insert(name.clone());
            }
            if child.is_some() {
                clashed.namespace.insert(name);
            }
            if let Some(diag) = body.or(child) {
                self.report(d, diag);
            }
        }
    }

    /// The names the `use` of `m` bound, in the order written: of a name of
    /// the prelude or a builtin name of a flow, of an item of `m` (§15.1:
    /// the `use`, whichever is written first, S-676), or of a name bound
    /// before.
    fn use_clashes(&mut self, m: ModId) {
        let bound = self.a.modules.get(m).bound.clone();
        let mut first: HashMap<&str, Span> = HashMap::new();
        for (name, span) in &bound {
            match self.use_clash(m, name, *span, first.get(name.as_str()).copied()) {
                Some(diag) => {
                    self.a.modules.get_mut(m).clashed.body.insert(name.clone());
                    self.report_mod(diag);
                }
                None => {
                    first.insert(name, *span);
                }
            }
        }
    }

    /// The E0304 of `name` a `use` of `m` binds at `span`: of the prelude or
    /// a builtin name of a flow, of an item of `m`, or of the name bound
    /// `first` before.
    pub(super) fn use_clash(&self, m: ModId, name: &str, span: Span, first: Option<Span>) -> Option<Diagnostic> {
        if let Some(diag) = self.body_clash(name, span, "a `use`") {
            return Some(diag);
        }
        if let Some(&d) = self.a.modules.get(m).items.get(name) {
            return Some(already(span, name).with_note(self.a.def(d).name_span, "declared here"));
        }
        first.map(|at| already(span, name).with_note(at, "first bound here"))
    }

    /// A name of the body of a module (`what` binds it at `span`) that the
    /// prelude or the builtin names of a flow have (§5.1, §2.2).
    fn body_clash(&self, name: &str, span: Span, what: &str) -> Option<Diagnostic> {
        if self.a.prelude.contains_key(name) {
            let msg = format!("`{name}` is a name of the prelude, which {what} does not take (§5.1, §15.1)");
            return Some(clash(span, name, msg));
        }
        if let Some(Unbindable::FlowBuiltin) = unbindable(name) {
            let msg = format!("`{name}` is a builtin name of a flow, which {what} does not take (§2.2)");
            let rule = "a flow body sees the items and the `use` of its module, and no binding it sees \
                        hides a builtin name (§5.1, §11.4)";
            return Some(clash(span, name, msg).with_rule(rule));
        }
        None
    }

    /// The modules under the root of each package of the name of a package
    /// it depends on (§15.1, S-246): at the head of the module, outside every
    /// unit. The heads of `use` name the package
    /// ([`crate::resolve::Modules::heads`]).
    // SPEC-GAP(S-645): at the head of one file (`Sema::module_head`), outside
    // every unit.
    fn head_clashes(&mut self) {
        for (pkg, p) in self.flat.clone().into_iter().enumerate() {
            let root = self.a.modules.roots[pkg];
            let mut names: Vec<(String, ModId)> =
                self.a.modules.get(root).children.iter().map(|(n, &c)| (n.clone(), c)).collect();
            names.sort();
            for (name, c) in names {
                if p.deps.iter().any(|d| d.name == name) {
                    self.a.modules.clashed_heads[pkg].insert(name.clone());
                    let msg = format!(
                        "the module `{name}` under the root has the name of the package `{name}` this package \
                         depends on (§15.1)"
                    );
                    let d = Diagnostic::new(Stage::Names, Code::E0304, self.module_head(c), msg)
                        .with_rule(format!("a path that starts with `{name}` names the package; rename the module"));
                    self.a.path_diagnostics.push(d);
                }
            }
        }
    }

    /// The head of the file of `m`, or of a module with no file of its own
    /// (a directory), the head of the first `.onsa` under it in the order of
    /// the diagnostics (the paths of the files, as the E0320 of a directory,
    /// S-313, S-666).
    // SPEC-GAP(S-645): the E0304 of a directory is on its first file alone, so
    // a `check` of another file under it does not show it.
    fn module_head(&self, m: ModId) -> Span {
        if let Some(file) = self.a.modules.get(m).file {
            return Span::empty(file, 0);
        }
        let mut first: Option<(String, Span)> = None;
        let mut stack = vec![m];
        while let Some(at) = stack.pop() {
            let info = self.a.modules.get(at);
            if let Some(file) = info.file {
                let key = self.file_key(at);
                if first.as_ref().is_none_or(|(k, _)| key < *k) {
                    first = Some((key, Span::empty(file, 0)));
                }
            }
            stack.extend(info.children.values().copied());
        }
        match first {
            Some((_, span)) => span,
            None => onsa_diag::internal::bug(None, "a module with no file under it"),
        }
    }
}

fn clash(span: Span, name: &str, msg: String) -> Diagnostic {
    Diagnostic::new(Stage::Names, Code::E0304, span, msg).with_found(name.to_string())
}

fn already(span: Span, name: &str) -> Diagnostic {
    clash(span, name, format!("`{name}` is already in scope; a name is bound once per module (§15.1)"))
}

#[cfg(test)]
mod tests {
    use super::{Unbindable, unbindable};

    #[test]
    fn a_use_binds_no_keyword_and_no_builtin_name_of_a_flow() {
        for name in ["match", "test", "clock", "ser", "static"] {
            assert!(matches!(unbindable(name), Some(Unbindable::NotAName)), "{name}");
        }
        for name in ["prev", "delay", "vdelay", "sample_rate", "sample_tick"] {
            assert!(matches!(unbindable(name), Some(Unbindable::FlowBuiltin)), "{name}");
        }
        for name in ["util", "gain", "previous", "Option"] {
            assert!(unbindable(name).is_none(), "{name}");
        }
    }
}
