//! The cycles of the imports (spec §15.1, S-594, R-39): E0310. A `use` that
//! takes a module is a dependency on it and on every module below it (itself
//! left out), one that takes an item a dependency on the module of the item,
//! and the path in a body is not looked at.
//!
//! The graph has a point for each module and one more, S(T), for "T and every
//! module below it": S(T) → T and S(T) → S(child). A `use` of a module adds
//! M → S(T), of an item M → T, so the graph has 2N points and as many edges
//! as the modules, the children and the dependencies. A strongly connected
//! component with two modules
//! or more is a cycle: one with one module M alone is M → S(T) → … → M, the
//! dependency on itself that the spec leaves out. In a component with two
//! modules, cutting those loops out of a path between them leaves a path, so
//! the cycle stays. Tarjan's algorithm, iterative: O(N + U), no recursion.

use std::cell::RefCell;
use std::collections::HashMap;

use onsa_diag::{Code, Diagnostic, Stage};

use crate::def::ModId;
use crate::resolve::{Dep, DepTarget, Entity, Modules};
use crate::sig::Sema;

/// The edges of the graph of the dependencies of the `use`, by point: the
/// module `m` is the point `m`, and S(m) the point `N + m`.
#[derive(Debug)]
pub(crate) struct ImportGraph {
    edges: Vec<Vec<usize>>,
    /// The component of each point, numbered sinks first (Tarjan): a point
    /// reaches no point of a component of a lower number than its own.
    comp: Vec<usize>,
    walks: RefCell<Walks>,
}

/// What [`Modules::closes_cycle`] keeps from one walk to the next: the answer
/// of each pair asked (the bodies ask for one path more than once), the
/// number of the last walk, and the walk that last saw each point, before
/// and after it passed a module (no array made per walk).
#[derive(Debug)]
struct Walks {
    answers: HashMap<(usize, usize), bool>,
    count: u64,
    seen: Vec<[u64; 2]>,
}

impl ImportGraph {
    fn build(modules: &Modules) -> ImportGraph {
        let n = modules.mods.len();
        let mut edges = vec![Vec::new(); 2 * n];
        for (m, info) in modules.mods.iter().enumerate() {
            edges[n + m].push(m);
            edges[n + m].extend(info.children.values().map(|c| n + c.0 as usize));
            edges[m].extend(info.deps.iter().map(|d| point(n, d.target)));
        }
        let comp = components(&edges);
        let walks = Walks { answers: HashMap::new(), count: 0, seen: vec![[0; 2]; 2 * n] };
        ImportGraph { edges, comp, walks: RefCell::new(walks) }
    }
}

fn point(n: usize, target: DepTarget) -> usize {
    match target {
        DepTarget::At(t) => t.0 as usize,
        DepTarget::Below(t) => n + t.0 as usize,
    }
}

impl Modules {
    /// A dependency on `target` added to `from` would close a cycle (E0310):
    /// some module other than `from` that it reaches reaches `from`. The walk
    /// marks whether it has passed such a module yet: reaching `from` before
    /// is the dependency on itself, which is no cycle. A point of a component
    /// below that of `from` does not reach it, and is not walked. O(N + U)
    /// for a pair not asked before.
    pub(crate) fn closes_cycle(&self, from: ModId, target: DepTarget) -> bool {
        let Some(graph) = &self.graph else {
            onsa_diag::internal::bug(None, "a cycle asked for before the graph of the imports is made")
        };
        let (n, from) = (self.mods.len(), from.0 as usize);
        let start = point(n, target);
        let Walks { answers, count, seen } = &mut *graph.walks.borrow_mut();
        if let Some(&closes) = answers.get(&(from, start)) {
            return closes;
        }
        *count += 1;
        let mut stack = vec![(start, start < n && start != from)];
        let closes = loop {
            let Some((p, passed)) = stack.pop() else { break false };
            if p == from {
                if passed {
                    break true;
                }
                continue;
            }
            if graph.comp[p] < graph.comp[from] || std::mem::replace(&mut seen[p][passed as usize], *count) == *count {
                continue;
            }
            stack.extend(graph.edges[p].iter().map(|&q| (q, passed || (q < n && q != from))));
        };
        answers.insert((from, start), closes);
        closes
    }

    /// The dependency of `m` on what a name of its `use` takes (§15.1,
    /// S-594): a module and what is below it, or else the last module of the
    /// path. None on `m` itself or on another package, which closes no cycle.
    pub(crate) fn dep_of(&self, m: ModId, taken: Option<Entity>, last: Option<ModId>) -> Option<DepTarget> {
        let target = match taken {
            Some(Entity::Module(c)) => DepTarget::Below(c),
            _ => DepTarget::At(last?),
        };
        let t = target.module();
        (t != m && self.pkg_of(t) == self.pkg_of(m)).then_some(target)
    }

    /// A `use` of `m` that takes `taken` (after the module `last`) would close
    /// a cycle.
    pub(crate) fn take_closes_cycle(&self, m: ModId, taken: Entity, last: Option<ModId>) -> bool {
        self.dep_of(m, Some(taken), last).is_some_and(|t| self.closes_cycle(m, t))
    }
}

impl<'p> Sema<'p> {
    /// Makes the graph once every `use` is resolved, and reports one E0310
    /// per cycle, on the first `use` in the order of the diagnostics that
    /// has a dependency in it (the spec fixes neither the number nor the
    /// place). When narrowing every `use` of a module to items (`At`) cuts
    /// the cycle, those `use` are the notes; when not, the rule says so.
    /// Whether it cuts reads the graph with every dependency at its module,
    /// once: a cycle is cut when no two of its modules are then in one
    /// component (a component of it is inside one of the graph).
    pub(crate) fn check_cycles(&mut self) {
        let graph = ImportGraph::build(&self.a.modules);
        let comp = graph.comp.clone();
        self.a.modules.graph = Some(graph);
        let n = self.a.modules.mods.len();
        let narrowed: Vec<Vec<usize>> = (self.a.modules.mods.iter())
            .map(|info| info.deps.iter().map(|d| d.target.module().0 as usize).collect())
            .collect();
        let narrowed = components(&narrowed);
        let mut size = vec![0; n];
        for &c in &narrowed {
            size[c] += 1;
        }
        let mut members: Vec<Vec<ModId>> = vec![Vec::new(); comp.iter().map(|&c| c + 1).max().unwrap_or(0)];
        for (m, &c) in comp[..n].iter().enumerate() {
            members[c].push(ModId(m as u32));
        }
        for mods in members.into_iter().filter(|mods| mods.len() > 1) {
            let c = comp[mods[0].0 as usize];
            let deps: Vec<(ModId, Dep)> = mods
                .iter()
                .flat_map(|&m| self.a.modules.get(m).deps.iter().map(move |&d| (m, d)))
                .filter(|(_, d)| comp[point(n, d.target)] == c)
                .collect();
            // SPEC-GAP(S-645): one E0310 per cycle, in the file of its first
            // `use`: a `check` of another file of the cycle does not see it.
            let Some(&(first, at)) = deps.iter().min_by_key(|(m, d)| (self.file_key(*m), d.span.start)) else {
                onsa_diag::internal::bug(None, "a cycle with no `use` in it")
            };
            let cut = mods.iter().all(|m| size[narrowed[m.0 as usize]] == 1);
            self.report_mod(self.cycle(&mods, (first, at), &deps, cut));
        }
    }

    fn cycle(&self, mods: &[ModId], (_, at): (ModId, Dep), deps: &[(ModId, Dep)], cut: bool) -> Diagnostic {
        let mut names: Vec<String> = mods.iter().map(|&m| format!("`{}`", self.a.modules.get(m).path)).collect();
        names.sort();
        let msg = format!("the modules {} import each other (cyclic module import, §15.1)", names.join(", "));
        let mut d = Diagnostic::new(Stage::Names, Code::E0310, at.span, msg);
        if !cut {
            return d.with_rule("no `use` of the cycle narrows to cut it: its modules take items of each other");
        }
        for &(m, dep) in deps {
            if let DepTarget::Below(t) = dep.target {
                let path = self.a.modules.abs_path(m, t).join(".");
                d = d.with_note(
                    dep.name,
                    format!(
                        "this takes `{path}` and every module below it; narrow it to what is used \
                         (`use {path}.{{…}}`)"
                    ),
                );
            }
        }
        d
    }

    /// The key of the file of `m` in the order of the diagnostics: the path
    /// of the file in its package (S-313).
    pub(crate) fn file_key(&self, m: ModId) -> String {
        match self.module(m) {
            Some(module) => format!("{}.onsa", module.segments.join("/")),
            None => String::new(),
        }
    }
}

/// The strongly connected component of each point (Tarjan, iterative).
fn components(edges: &[Vec<usize>]) -> Vec<usize> {
    const NONE: usize = usize::MAX;
    let n = edges.len();
    let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0; n], vec![NONE; n]);
    let (mut on, mut stack, mut calls) = (vec![false; n], Vec::new(), Vec::new());
    let (mut next, mut count) = (0, 0);
    for s in 0..n {
        if index[s] != NONE {
            continue;
        }
        macro_rules! visit {
            ($v:expr) => {{
                let v = $v;
                (index[v], low[v], on[v]) = (next, next, true);
                next += 1;
                stack.push(v);
                calls.push((v, 0));
            }};
        }
        visit!(s);
        while let Some(&mut (v, ref mut i)) = calls.last_mut() {
            if let Some(&w) = edges[v].get(*i) {
                *i += 1;
                if index[w] == NONE {
                    visit!(w);
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(u, _)) = calls.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    comp[w] = count;
                    if w == v {
                        break;
                    }
                }
                count += 1;
            }
        }
    }
    comp
}

#[cfg(test)]
mod tests {
    use super::components;

    #[test]
    fn the_components_of_a_ring_a_chain_and_a_loop() {
        // 0 → 1 → 2 → 0 is one; 3 → 4 two; 5 → 5 one alone.
        let edges = vec![vec![1], vec![2], vec![0], vec![4], vec![], vec![5]];
        let c = components(&edges);
        assert!(c[0] == c[1] && c[1] == c[2]);
        assert!(c[3] != c[4] && c[3] != c[0] && c[5] != c[0]);
    }

    #[test]
    fn a_long_chain_does_not_recurse() {
        let n = 200_000;
        let mut edges: Vec<Vec<usize>> = (0..n).map(|i| vec![(i + 1) % n]).collect();
        edges[n - 1] = vec![0];
        let c = components(&edges);
        assert!(c.iter().all(|&x| x == c[0]));
    }
}
