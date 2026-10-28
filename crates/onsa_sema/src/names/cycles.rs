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
        let edges = edges(modules, |t| t);
        let comp = components(&edges);
        let walks = Walks { answers: HashMap::new(), count: 0, seen: vec![[0; 2]; 2 * n] };
        ImportGraph { edges, comp, walks: RefCell::new(walks) }
    }
}

/// The edges of the graph, each dependency on what `target` makes of it.
fn edges(modules: &Modules, target: impl Fn(DepTarget) -> DepTarget) -> Vec<Vec<usize>> {
    let n = modules.mods.len();
    let mut edges = vec![Vec::new(); 2 * n];
    for (m, info) in modules.mods.iter().enumerate() {
        edges[n + m].push(m);
        edges[n + m].extend(info.children.values().map(|c| n + c.0 as usize));
        edges[m].extend(info.deps.iter().map(|d| point(n, target(d.target))));
    }
    edges
}

/// A `use` of the module `t` can be narrowed to items of it (§15.1,
/// S-683): `t` has a file of its own (a module of a directory alone has no
/// items).
fn narrows(modules: &Modules, t: DepTarget) -> bool {
    matches!(t, DepTarget::Below(m) if modules.get(m).file.is_some())
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
        let graph = self.import_graph();
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

    /// The modules of the cycle that a dependency on `target` added to
    /// `from` closes (S-682): those of the component of `from` in the graph
    /// with it, as the E0310 of that cycle names them. O(N + U); asked only
    /// for a candidate kept back.
    pub(crate) fn cycle_of(&self, from: ModId, target: DepTarget) -> Vec<ModId> {
        let (n, at) = (self.mods.len(), from.0 as usize);
        let mut edges = self.import_graph().edges.clone();
        edges[at].push(point(n, target));
        let comp = components(&edges);
        (0..n).filter(|&m| comp[m] == comp[at]).map(|m| ModId(m as u32)).collect()
    }

    /// Whether the modules `mods` are all in one cycle of the imports, which
    /// its E0310 reports (§18.1, S-734).
    pub(crate) fn one_cycle(&self, mods: &[ModId]) -> bool {
        let comp = &self.import_graph().comp;
        mods.iter().all(|m| comp[m.0 as usize] == comp[mods[0].0 as usize])
    }

    fn import_graph(&self) -> &ImportGraph {
        match &self.graph {
            Some(graph) => graph,
            None => onsa_diag::internal::bug(None, "a cycle asked for before the graph of the imports is made"),
        }
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

    /// The dependency of a `use` of `m` that takes `taken` (after the module
    /// `last`), when it would close a cycle.
    pub(crate) fn take_cycle(&self, m: ModId, taken: Entity, last: Option<ModId>) -> Option<DepTarget> {
        self.dep_of(m, Some(taken), last).filter(|&t| self.closes_cycle(m, t))
    }
}

impl<'p> Sema<'p> {
    /// Makes the graph once every `use` is resolved, and reports one E0310
    /// per cycle, on the first `use` in the order of the diagnostics that
    /// has a dependency in it, the others in notes (§18.1, S-734). When
    /// narrowing every `use` of a module with a file to items (`At`, S-683)
    /// cuts the cycle, the notes of those `use` say how; when not, the rule
    /// says so. Whether it cuts reads the graph with those dependencies
    /// narrowed, once: a cycle is cut when no two of its modules are then in
    /// one component (a component of it is inside one of the graph).
    pub(crate) fn check_cycles(&mut self) {
        let modules = &self.a.modules;
        let graph = ImportGraph::build(modules);
        let comp = graph.comp.clone();
        let n = modules.mods.len();
        let narrowed = components(&edges(modules, |t| if narrows(modules, t) { DepTarget::At(t.module()) } else { t }));
        self.a.modules.graph = Some(graph);
        let mut size = vec![0; 2 * n];
        for &c in &narrowed[..n] {
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
            d = d.with_rule(
                "the cycle stays after each `use` of it that takes a module is narrowed to items of it: \
                 its modules take items of each other",
            );
        }
        // The other `use` of the cycle in notes (§18.1, S-734), with how to
        // narrow those that cut it.
        for &(m, dep) in deps {
            let note = match dep.target {
                DepTarget::Below(t) if cut && narrows(&self.a.modules, dep.target) => {
                    let path = self.a.modules.abs_path(m, t).join(".");
                    format!(
                        "this takes `{path}` and every module below it; narrow it to what is used (`use {path}.{{…}}`)"
                    )
                }
                // Of the `use` the E0310 is on, none (R-315).
                _ if dep.span == at.span => continue,
                _ => "this `use` is in the cycle too".to_string(),
            };
            d = d.with_note(dep.name, note);
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

/// The strongly connected component of each point (Tarjan, iterative),
/// numbered sinks first.
pub(crate) fn components(edges: &[Vec<usize>]) -> Vec<usize> {
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

    /// [`Modules::closes_cycle`] leaves out the points of a component of a
    /// lower number than that of `from`: an edge never goes to a component
    /// of a higher number than its own.
    #[test]
    fn an_edge_goes_to_a_component_of_its_number_or_a_lower_one() {
        let mut seed = 7u64;
        for _ in 0..200 {
            let n = 12;
            let edges: Vec<Vec<usize>> = (0..n)
                .map(|_| {
                    (0..3)
                        .filter_map(|_| {
                            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                            let v = (seed >> 33) as usize % (n + 4);
                            (v < n).then_some(v)
                        })
                        .collect()
                })
                .collect();
            let c = components(&edges);
            for (u, out) in edges.iter().enumerate() {
                assert!(out.iter().all(|&v| c[u] >= c[v]), "{edges:?}");
            }
        }
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
