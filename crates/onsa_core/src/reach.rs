//! Reachability (spec §15.2, S-242; R-80 (3), D-15): the functions and the
//! `const`s that the entries of a run or a build reach. The one place that
//! decides it: the C backend emits what the exports reach, the build-time
//! evaluation of the `const`s evaluates what they reach, and `onsa test`
//! reports the E0200 of the interpreter for what the tests it runs reach.
//!
//! An entry reaches, statically and in turn, the functions it calls, the
//! `const`s it reads and the initializers of those `const`s (the calls and the
//! `const`s in them, however long the chain). Whether a run passes the
//! expression is not looked at: a branch that is not taken, a loop that runs
//! zero times and the code after an early `return` are reached. A flow whose
//! instance the code makes is a call of its generated functions in Core (its
//! `render`, `process`, ...), and the generated functions call those of the
//! flows they instantiate, so following calls follows flows. A function used
//! as a value is not lowered by this version (E0200 at lowering, W8-09), and
//! an anonymous function given to `array.from_fn` is expanded in place.

use std::collections::BTreeSet;

use crate::ir::{ConstId, Expr, ExprKind, FnId, Module};
use crate::walk::{walk_block, walk_expr};

/// What the roots reach, each in the order of its ids.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Reach {
    pub fns: BTreeSet<FnId>,
    pub consts: BTreeSet<ConstId>,
}

impl Reach {
    /// Every expression of what was reached, depth first: the bodies of the
    /// functions, then the initializers of the `const`s, each in the order of
    /// its ids. What looks for a form in the code a run reaches (the E0200 of
    /// the interpreter, a transcendental primitive) walks it here.
    pub fn walk(&self, m: &Module, f: &mut dyn FnMut(&Expr)) {
        for &id in &self.fns {
            if let Some(b) = &m.fn_(id).body {
                walk_block(b, f);
            }
        }
        for &c in &self.consts {
            walk_expr(&m.const_(c).init, f);
        }
    }
}

/// An item to visit.
enum Item {
    Fn(FnId),
    Const(ConstId),
}

/// The functions and `const`s that `roots` reach in `m` (the roots
/// included). Iterative over the items, so a long chain of calls or `const`s
/// does not grow the stack; only the nesting of one expression does.
pub fn reach(m: &Module, roots: &[FnId]) -> Reach {
    let mut r = Reach::default();
    let mut stack: Vec<Item> = roots.iter().rev().map(|f| Item::Fn(*f)).collect();
    while let Some(item) = stack.pop() {
        let mut visit = |e: &Expr| match &e.kind {
            ExprKind::Call { fn_, .. } => stack.push(Item::Fn(*fn_)),
            ExprKind::Const(c) => stack.push(Item::Const(*c)),
            _ => {}
        };
        match item {
            Item::Fn(f) => {
                if !r.fns.insert(f) {
                    continue;
                }
                if let Some(b) = &m.fn_(f).body {
                    walk_block(b, &mut visit);
                }
            }
            Item::Const(c) => {
                if !r.consts.insert(c) {
                    continue;
                }
                walk_expr(&m.const_(c).init, &mut visit);
            }
        }
    }
    r
}
