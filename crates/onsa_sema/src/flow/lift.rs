//! The candidate that lifts a thing with state out of a place that is not
//! evaluated on every sample into a new `let` before its statement (§11.5,
//! S-1172): the E0811 of a branch, a guard and a later condition of a chain,
//! and the E0806 of the right of `&&` / `||`. Made of the AST and the names
//! of the body alone (a check of the names stage could make it too).

use onsa_diag::hash::HashSet;
use onsa_diag::{Edit, Fix};
use onsa_syntax::ast::{Ast, ExprId, ExprKind, Ident};

use crate::names::body::{BindingKind, BodyNames, PathRes};
use crate::{Analysis, DefId};

/// What the candidate reads of the flow `def`: its module's AST and text,
/// and the record of the names of its body.
pub(in crate::flow) struct Body<'a> {
    pub(in crate::flow) a: &'a Analysis,
    pub(in crate::flow) def: DefId,
    pub(in crate::flow) ast: &'a Ast,
    pub(in crate::flow) text: &'a str,
    pub(in crate::flow) names: &'a BodyNames,
}

/// The statement of the body that holds a thing: the initializer of a `let`
/// or the output (`root`), and the start of the statement (`start`).
#[derive(Debug, Clone, Copy)]
pub(in crate::flow) struct Stmt {
    pub(in crate::flow) root: ExprId,
    pub(in crate::flow) start: u32,
}

/// The candidate that moves the thing with state `thing`, the outermost in
/// its place (the walk reports that one: a node before its arguments, a
/// `par~` before its body; of two side by side the first, S-1190), into a
/// new `let` right before `stmt`, at the indent of its line, and writes the
/// name of that `let` in its place. The name is `<kind>_<n>` (`kind` the kind
/// of its node, §11.6), the first `n` that no binding of the body, parameter
/// of the heading or name of the module has (§5.1), and `per` the tick it is
/// computed on (§11.9). None when the thing is
/// in the body of a replication or reads a binding of an arm (§11.5: the
/// `let` would be outside them), or any binding the statement does not see.
/// Linear in the statement and the names of the body.
// SPEC-GAP(S-1190): of two things with state side by side, the one at the
// place of the diagnostic only is moved; the other stays, the error of the
// next round (provisional).
pub(in crate::flow) fn lift(b: &Body, thing: ExprId, kind: &str, stmt: Stmt, per: &str) -> Option<Fix> {
    let (ast, span) = (b.ast, b.ast.expr(thing).span);
    if under_par(ast, stmt.root, thing)? || !reads_seen(b, thing) {
        return None;
    }
    let name = free_name(b, kind, span);
    let src = span.text_in(b.text);
    let line = b.text[..stmt.start as usize].rfind('\n').map_or(0, |k| k + 1);
    let indent: String = b.text[line..stmt.start as usize].chars().take_while(|c| matches!(c, ' ' | '\t')).collect();
    let head = format!("let {name} = ");
    let moved = (head.len() as u32, (head.len() + src.len()) as u32);
    let edits = vec![
        Edit::insert(span.file, stmt.start, format!("{head}{src}\n{indent}")).with_writers(&[moved]),
        Edit::replace(span, name.as_str()),
    ];
    Some(Fix::new(format!("compute it on every {per} in a new `let {name}` before this statement"), edits))
}

/// Whether `thing` is in the body of a `par` / `par~` under `root` (its
/// range too); None when it is not under `root`, which no walk gives.
fn under_par(ast: &Ast, root: ExprId, thing: ExprId) -> Option<bool> {
    let mut todo = vec![(root, false)];
    while let Some((x, par)) = todo.pop() {
        if x == thing {
            return Some(par);
        }
        let par = par || matches!(ast.expr(x).kind, ExprKind::Par { .. });
        todo.extend(ast.sub_exprs(x).into_iter().map(|y| (y, par)));
    }
    onsa_diag::internal::bug(Some(ast.expr(thing).span), "a thing with state outside its statement")
}

/// Whether every binding `thing` reads is an input or a `let` of the body,
/// or is bound in `thing` (the index of a `par~` it is).
fn reads_seen(b: &Body, thing: ExprId) -> bool {
    let span = b.ast.expr(thing).span;
    let mut todo = vec![thing];
    while let Some(x) = todo.pop() {
        if let Some(PathRes::Local(id)) = b.names.paths.get(&x) {
            let binding = &b.names.bindings[id.0 as usize];
            let inside = span.start <= binding.span.start && binding.span.end <= span.end;
            if !inside && !matches!(binding.kind, BindingKind::FlowInput | BindingKind::FlowLet) {
                return false;
            }
        }
        todo.extend(b.ast.sub_exprs(x));
    }
    true
}

/// The first `<kind>_<n>` that is no binding of the body, no parameter of
/// the heading and hides no name of the module (the one test of a
/// declaration, [`crate::names::hides`]).
fn free_name(b: &Body, kind: &str, span: onsa_diag::Span) -> String {
    let bound: HashSet<&str> = b.names.bindings.iter().map(|x| x.name.as_str()).collect();
    let generics = crate::body::generics_of(b.a, b.def);
    let module = b.a.def(b.def).module;
    let taken = |name: &str| {
        let id = Ident { name: name.to_string(), span };
        bound.contains(name)
            || generics.iter().any(|g| g.name == name)
            || crate::names::hides(b.a, module, &id, None, true).is_some()
    };
    // A flow named with a trailing `_` (`foo_`) gives `foo_0`, not `foo__0`, which §2.3 forbids (E0320).
    let name = |n: u32| if kind.ends_with('_') { format!("{kind}{n}") } else { super::plan::names::local(kind, n) };
    (0..).map(name).find(|n| !taken(n)).unwrap_or_default()
}

#[cfg(test)]
mod tests;
