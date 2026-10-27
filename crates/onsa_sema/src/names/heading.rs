//! The names of a heading (spec §5.1, §4.4, §4.5): the type, const and
//! effect parameters of an item, which are bindings in it (S-649), and the
//! fields of a struct and the variants of an enum, each name once in its
//! list (R-40). Their E0304 is in the unit of the item (§18.1).

use std::collections::HashMap;

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{GenericParam, Ident};

use super::clash::hides;
use crate::def::{DefId, GenericDef, ModId};
use crate::sig::Sema;

/// The name a parameter of a heading declares.
pub(crate) fn param_name(g: &GenericParam) -> &Ident {
    match g {
        GenericParam::Type { name, .. } | GenericParam::Const { name, .. } | GenericParam::Effect { name } => name,
    }
}

impl Sema<'_> {
    /// The E0304 of the parameters `list` of the heading of `def` in `m`
    /// (§5.1, S-649), each through the one test of a declaration
    /// ([`hides`]): of the names before it in the list, of the list of the
    /// `impl` around it (`outer`), then of the body of the module. The error
    /// is on the later (inner) name; the name it clashes with is no error
    /// elsewhere (§18.1).
    pub(crate) fn heading_clashes(&mut self, def: DefId, m: ModId, list: &[GenericParam], outer: &[GenericDef]) {
        let names: Vec<&Ident> = list.iter().map(param_name).collect();
        for (k, name) in names.iter().enumerate() {
            let before = names[..k].iter().find(|n| n.name == name.name).map(|n| n.span);
            let visible = before.or_else(|| outer.iter().find(|g| g.name == name.name).map(|g| g.span));
            if let Some(d) = hides(self.a, m, name, visible, false) {
                self.report(def, d);
            }
        }
    }

    /// The E0304 of a name of a field of a struct or of a variant of an enum
    /// (`what`) written twice in its list (§4.4, R-40): on the later, with
    /// the first in the note.
    pub(crate) fn member_clashes<'n>(&mut self, def: DefId, what: &str, names: impl Iterator<Item = &'n Ident>) {
        let mut first: HashMap<&str, Span> = HashMap::new();
        for n in names {
            let Some(&at) = first.get(n.name.as_str()) else {
                first.insert(&n.name, n.span);
                continue;
            };
            let msg = format!("`{}` is already the name of a {what} here (§4.4)", n.name);
            let d = Diagnostic::new(Stage::Names, Code::E0304, n.span, msg).with_found(n.name.clone());
            self.report(def, d.with_note(at, format!("the first {what} `{}`", n.name)));
        }
    }
}
