//! The names of the state of a flow (§11.6, S-1138, S-1136, S-148): the
//! one place that makes them. A node has a name inside the part of the body
//! that holds it ([`Owner`]) and a path, its name after the scope of that
//! part: `a.prev_0`, `_out.lp_0`, `m.par_0.lp_0`, or the name of the `let`
//! whose whole value it is. Every name the processor makes is of a form no
//! user writes (`_` first or a `.` in it, §2.3), so none is reserved.

use onsa_diag::hash::HashMap;
use onsa_syntax::ast::{Ast, ExprId};

use super::super::PendingLet;
use super::{Owner, Part, PlanKind, PlanNode};
use crate::body::{BodyInfo, LocalId};
use crate::flow_names::{OUTPUT_SCOPE, PAR};

/// `<kind>_<n>`: the name of the node `n` of a kind in a scope (`prev_0`,
/// `lp_1`, `par_0`), and of the hoisted field `n` (`_hoist_0` of
/// [`crate::flow_names::HOIST`]).
pub(in crate::flow) fn local(kind: &str, n: u32) -> String {
    format!("{kind}_{n}")
}

/// `<scope>.<name>` (`a.prev_0`).
pub(in crate::flow) fn qualify(scope: &str, name: &str) -> String {
    format!("{scope}.{name}")
}

/// The field of the part `p` of a node whose own field is `field`:
/// `<field>.buf`, `<field>.w`, `<field>.init`.
pub(in crate::flow) fn part(field: &str, p: Part) -> String {
    match p {
        Part::Own => field.to_string(),
        Part::Init => format!("{field}.init"),
        Part::Buf => format!("{field}.buf"),
        Part::W => format!("{field}.w"),
    }
}

/// The own field of the node `n` in the struct that holds it: its name in
/// the replica of a `par~` (the replica is the scope), else its path.
pub(in crate::flow) fn field(n: &PlanNode) -> &str {
    match n.owner {
        Owner::Par(_) => &n.name,
        Owner::Let(_) | Owner::Output => &n.path,
    }
}

/// The scope of the nodes of each `let` (§11.6, S-1136), of the first name
/// each binds in its pattern: that name, or `_<m>` when it binds none, `m`
/// counting those `let`s in their order from 0.
fn let_scopes<'a>(first: impl Iterator<Item = Option<&'a str>>) -> Vec<String> {
    let mut unnamed = 0;
    let mut scope = |name: Option<&str>| match name {
        Some(name) => name.to_string(),
        None => {
            unnamed += 1;
            format!("_{}", unnamed - 1)
        }
    };
    first.map(&mut scope).collect()
}

/// The scopes of the `let`s whose locals are `locals`, in their order
/// ([`let_scopes`]): of the nodes and of the hoisted fields.
pub(in crate::flow) fn scopes<'a>(locals: impl Iterator<Item = &'a [LocalId]>, body: &BodyInfo) -> Vec<String> {
    let first = locals.map(|l| match crate::flow::binds_none(l) {
        true => None,
        false => Some(body.locals[l[0].0 as usize].name.as_str()),
    });
    let_scopes(first)
}

/// The names of the nodes of a flow body while the walk records them, in
/// the order the names of their calls come in the text (the outer call
/// first): numbered by part of the body and kind (§11.6).
// SPEC-GAP(S-1141): the body of each `par~` counts by itself from 0, apart
// from the `let` or the output that holds the `par~`.
// SPEC-GAP(S-1142): a `par~` with no state, which has no field, takes a
// number of the kind `par` too.
pub(in crate::flow) struct Namer {
    numbers: HashMap<(Owner, String), u32>,
    /// The scope of the nodes of each `let`.
    scopes: Vec<String>,
    /// The initializer of each `let` of a single name, through its
    /// parentheses, and that name (S-148).
    // SPEC-GAP(S-1143): a value in parentheses is the call itself (`let a =
    // (prev~(x))` is `a`); one under `at` is not (`let b = prev~(x) at
    // sample` is `b.prev_0`).
    whole: HashMap<ExprId, String>,
}

impl Namer {
    pub(in crate::flow) fn new(pending: &[PendingLet], ast: &Ast, body: &BodyInfo) -> Namer {
        let whole = pending.iter().filter_map(|p| Some((ast.without_parens(p.init), p.name.clone()?))).collect();
        let scopes = scopes(pending.iter().map(|p| p.locals.as_slice()), body);
        Namer { numbers: HashMap::default(), scopes, whole }
    }

    /// Whether the node `e` is the whole value of a `let` of a single name
    /// and takes its name (S-148): the one place of the judgement.
    pub(in crate::flow) fn whole(&self, e: ExprId) -> bool {
        self.whole.contains_key(&e)
    }

    /// The name and the path of the node `e` of `kind` in `owner`; `par`
    /// is the path of the `par~` that owns it. `None` of a part the body
    /// has not.
    pub(in crate::flow) fn name(
        &mut self,
        e: ExprId,
        owner: Owner,
        kind: &str,
        par: Option<&str>,
    ) -> Option<(String, String)> {
        if let Some(n) = self.whole.get(&e) {
            return Some((n.clone(), n.clone()));
        }
        let scope = match owner {
            Owner::Let(k) => self.scopes.get(k as usize)?.as_str(),
            Owner::Output => OUTPUT_SCOPE,
            Owner::Par(_) => par?,
        };
        let n = self.numbers.entry((owner, kind.to_string())).or_insert(0);
        *n += 1;
        let name = local(kind, *n - 1);
        let path = qualify(scope, &name);
        Some((name, path))
    }
}

/// The kind of a node of a delay or an instance (§11.6): the name of the
/// delay, or of the flow without its path.
pub(in crate::flow) fn kind<'a>(a: &'a crate::Analysis, k: &PlanKind) -> &'a str {
    match (k, k.delay()) {
        (_, Some(d)) => d.name(),
        (PlanKind::Instance { callee, .. }, None) => &a.def(*callee).name,
        (_, None) => PAR,
    }
}

#[cfg(test)]
mod tests;
