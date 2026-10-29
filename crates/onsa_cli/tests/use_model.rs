//! The `use` lines and the paths of a body against a model of the spec: random packages (a tree of
//! modules, some of them directories with no file, items, `use` lines of two forms and of lists, heads that
//! are a module, the own package name, the module itself, `std`, a name a `use` took, a name that is
//! nothing; body paths of the same kinds), the model of §15.1 that says which `use` and which path is an
//! E0302, which cycles are E0310 and which candidate is given, and `onsa check` that must say the same
//! (spec §2.2, §15.1, §18.1; S-37, S-594, S-663, S-673, S-679, R-39, R-106, R-268; W4-03 U3a2/t2). The
//! sweep moved here from the scripts of the break side (`model.py` of U2b with the rules of U3a2, and
//! `cyc.py`), which found faults the gate had passed. The check runs in this process as the command runs
//! it, with no file written (`check_input`, X-16): the reading of a package from its directory, the exit
//! code and the printing are the business of the tests that run the command.
//!
//! The model (written from the spec, not from the compiler):
//! - the head of a `use` is a module at the root of the package or a dependency (`std`); the own package
//!   name is E0302; a name that another `use` of the module took is E0302 with the full path of that
//!   binding as the candidate (S-37); a name that is nothing is E0302 without a candidate; a path is read
//!   down through the child modules and ends in a child module or an item (a name that no module or item
//!   of the module before it has is E0302); a `use` that takes the module itself is E0302 without a
//!   candidate (S-679);
//! - the dependencies (S-594): a `use` that takes a module is a dependency on the module and on every
//!   module below it, one that takes an item is a dependency on the module of the item, the module that
//!   writes the `use` and the other package (`std`) are left out; the body is not read (§15.1). A cycle
//!   is E0310, once for each strongly connected component; what is asked is the set of the modules of
//!   each component and that there is at least one, not the number or the place (the spec fixes neither),
//!   and that it has a note;
//! - the candidates (§15.1, §18.1): the own package name at the head gives `use` of the path without it
//!   (S-37, R-106), for a list one `use` for each element (S-663), for `use fx` and an empty list none; a
//!   name that a `use` took gives the `use` of the full path of the binding (S-37), none when the binding
//!   is an item; a path in a body headed by the own package name, the module itself or its own absolute
//!   path drops that part and adds the `use` of the new head when it is not there (S-673), a path headed
//!   by a module at the root or by `std` that no `use` took adds the `use` of the head (R-39, R-268);
//!   whatever the form, a candidate is given exactly when applying it is safe (§18.1): the path or the
//!   `use` it was given for is read whole by the names stage, the names it binds are free (no other
//!   binding or item of the module has them), and it closes no cycle (the modules of the components are
//!   the same before and after). The shape of an applied candidate is asked too: the `use` lines the
//!   module has and the paths of the bodies are the ones the spec names;
//! - an applied candidate, checked again, leaves in the package no E0302 for the unit it was given for, no
//!   E0304, no new E0310 and no E0302 that was not there (the unit reports one path, so one the candidate
//!   lets through is one that was hidden before, and is in the set of the package before); the member of a
//!   name that the candidate took which the module does not have is the E0401 of the types stage (R-254,
//!   W4-04), which is let through;
//! - the loop of the first candidates, over the same packages, stops, adds no code and no cycle.
//!
//! What the generator does not write, because the spec does not fix it (each has its mark in the place
//! that keeps it out):
//! - a body path whose head is a name that a failed `use` wrote (the names of a failed `use` stay silent in
//!   the places that use them, §18.1, which U3b makes), and a body path whose head is a binding whose member
//!   is nothing (E0302 or E0308, W4-04);
//! - the empty list and the broken syntax (`use_shapes.rs`), an item of the own module taken by a `use`
//!   (E0304, S-675), a module named like the package, a path headed by a name another `use` bound to a
//!   module that is not the new head (the spec says "bound by a `use` of the module");
//! - the module that takes itself with modules below it, and a `use` that fails in the middle of a path where
//!   the module read last has modules below it or is not at the root, or in a list with other names that
//!   is not the module itself (S-678, the edges of a failed `use`).
//!
//! The decisions of the group 60 are in the model: a list that has the module itself and other names
//! (`use d.{b, e}` in `d/b.onsa`) fails in the one element and takes the others (S-685); a candidate that adds
//! a `use` on a cycle that is there already closes the cycle (S-686); the module at the root that is read
//! first and closes a cycle leaves no candidate and does not move to the own name (S-687); the package name
//! followed by the own absolute path is taken off whole (`fx.a.b.f()` in `a/b.onsa` is `f()`, S-684).
//!
//! Provisional (the spec has not decided; the model follows the implementation of today, and each is in
//! one place): the cases where the E0310 of a cycle hides the E0302 of a failed `use` of the cycle
//! (`expect`: the place of the E0310 is not fixed, so the E0302 of a `use` that is partly bound is left to
//! either answer in a module of a cycle); the note of E0310 that shows how to narrow the path
//! (`narrowing_cuts`, S-683). The candidates of the names stage after an E0304 (S-675) are not in the model:
//! it writes no E0304.
//!
//! The packages: seed `n` of 160, in four tests (40 each) that run side by side, and the loop of candidates
//! in two (every fourth seed, 40 each); the modules come from a pool of 14 paths (some with no file of
//! their own), 0 to 3 `use` lines (4 when cycles are let in) and 1 to 4 paths in a body for a module, 45
//! packages in 100 are kept free of cycles while they are written (so that a candidate is the only thing
//! that can close one) and the others may have them. A test is about 2 seconds in a debug build.

mod test_support;

use std::collections::{BTreeMap, BTreeSet};

use test_support::sweep::*;

// ---- the tree of the modules ----------------------------------------------------------------------------

const ROOT: usize = 0;
const STD: usize = 1;
const STD_MATH: usize = 2;
const FIRST_MODULE: usize = 3;

#[derive(Clone)]
struct Node {
    name: String,
    parent: Option<usize>,
    children: BTreeMap<String, usize>,
    file: bool,
    items: BTreeSet<String>,
    /// A module of another package (`std`).
    ext: bool,
}

#[derive(Clone)]
struct Tree {
    nodes: Vec<Node>,
}

fn node(name: &str, parent: Option<usize>, ext: bool) -> Node {
    Node { name: name.into(), parent, children: BTreeMap::new(), file: false, items: BTreeSet::new(), ext }
}

impl Tree {
    /// The root of the package, `std` with `std.math`, and nothing else.
    fn new() -> Tree {
        let mut t = Tree { nodes: vec![node("", None, false), node("std", None, true), node("math", Some(STD), true)] };
        t.nodes[STD].children.insert("math".into(), STD_MATH);
        t.nodes[STD_MATH].file = true;
        for i in ["sin", "cos", "sqrt"] {
            t.nodes[STD_MATH].items.insert(i.into());
        }
        t
    }

    /// The module of `a/b` (and the modules above it), made when it is not there.
    fn ensure(&mut self, path: &str) -> usize {
        let mut cur = ROOT;
        for seg in path.split('/') {
            cur = match self.nodes[cur].children.get(seg) {
                Some(&c) => c,
                None => {
                    let id = self.nodes.len();
                    self.nodes.push(node(seg, Some(cur), false));
                    self.nodes[cur].children.insert(seg.into(), id);
                    id
                }
            };
        }
        cur
    }

    fn child(&self, id: usize, name: &str) -> Option<usize> {
        self.nodes[id].children.get(name).copied()
    }

    /// The names from the root: `["a", "b"]` for `a/b`; `["std", "math"]` for `std.math`.
    fn path(&self, mut id: usize) -> Vec<String> {
        let mut v = Vec::new();
        loop {
            v.push(self.nodes[id].name.clone());
            match self.nodes[id].parent {
                Some(ROOT) | None => break,
                Some(p) => id = p,
            }
        }
        v.reverse();
        v
    }

    fn dotted(&self, id: usize) -> String {
        self.path(id).join(".")
    }

    /// The module and every module below it.
    fn below(&self, id: usize) -> Vec<usize> {
        let mut out = vec![id];
        for &c in self.nodes[id].children.values() {
            out.extend(self.below(c));
        }
        out
    }

    /// Every module of the package, with a file or not.
    fn modules(&self) -> Vec<usize> {
        (FIRST_MODULE..self.nodes.len()).collect()
    }

    fn is_leaf(&self, id: usize) -> bool {
        self.nodes[id].children.is_empty()
    }

    /// The names a path can go on with from the module: its child modules and its items.
    fn members(&self, id: usize) -> Vec<String> {
        let n = &self.nodes[id];
        n.children.keys().chain(n.items.iter()).cloned().collect()
    }
}

// ---- the program: `use` lines and paths of the bodies ----------------------------------------------------

/// A `use` line: `segs` is the path (the head first) and `list` the names in braces after it.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Use {
    segs: Vec<String>,
    list: Option<Vec<String>>,
}

impl Use {
    fn new(segs: &[&str], list: Option<&[&str]>) -> Use {
        Use {
            segs: segs.iter().map(|s| s.to_string()).collect(),
            list: list.map(|l| l.iter().map(|s| s.to_string()).collect()),
        }
    }

    fn text(&self) -> String {
        let mut s = format!("use {}", self.segs.join("."));
        if let Some(l) = &self.list {
            s.push_str(&format!(".{{{}}}", l.join(", ")));
        }
        s
    }

    /// The names the `use` writes: the elements of the list, or the last name of the path.
    fn names(&self) -> Vec<String> {
        match &self.list {
            Some(l) => l.clone(),
            None => vec![self.segs.last().unwrap().clone()],
        }
    }
}

/// A path called in a body; `std` when the callee is one of `std` (it takes an `F32`).
#[derive(Clone, Debug)]
struct Body {
    segs: Vec<String>,
    std: bool,
}

#[derive(Clone)]
struct Module {
    id: usize,
    uses: Vec<Use>,
    bodies: Vec<Body>,
}

#[derive(Clone)]
struct Prog {
    tree: Tree,
    mods: Vec<Module>,
}

impl Prog {
    fn module(&self, id: usize) -> &Module {
        self.mods.iter().find(|m| m.id == id).expect("a module with a file")
    }

    fn module_mut(&mut self, id: usize) -> &mut Module {
        self.mods.iter_mut().find(|m| m.id == id).expect("a module with a file")
    }

    fn file_of(&self, id: usize) -> String {
        format!("{}.onsa", self.tree.path(id).join("/"))
    }
}

fn body_header(i: usize, b: &Body) -> String {
    if b.std { format!("pub fn t{i}(x: F32) -> F32 {{") } else { format!("pub fn t{i}() -> I32 {{") }
}

fn render(p: &Prog) -> Texts {
    let mut texts = Texts::new();
    for m in &p.mods {
        let mut s = String::new();
        for u in &m.uses {
            s.push_str(&u.text());
            s.push('\n');
        }
        if !m.uses.is_empty() {
            s.push('\n');
        }
        for it in &p.tree.nodes[m.id].items {
            s.push_str(&format!("pub fn {it}() -> I32 {{\n  1\n}}\n\n"));
        }
        s.push_str("pub fn pad() -> I32 {\n  1\n}\n");
        for (i, b) in m.bodies.iter().enumerate() {
            let call = b.segs.join(".");
            s.push('\n');
            s.push_str(&body_header(i, b));
            s.push('\n');
            s.push_str(&format!("  {call}({})\n}}\n", if b.std { "x" } else { "" }));
        }
        texts.insert(p.file_of(m.id), s);
    }
    texts
}

// ---- what a `use` reads ----------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
enum Ent {
    Mod(usize),
    Item(usize, String),
}

/// A name a `use` binds, with the path that names it from the root.
#[derive(Clone, PartialEq, Debug)]
struct Bind {
    name: String,
    ent: Ent,
    full: Vec<String>,
}

#[derive(Clone, PartialEq, Debug)]
enum Why {
    /// The head is the own package name.
    OwnPkg,
    /// The head is nothing.
    Unknown,
    /// The head is a name another `use` of the module took.
    Bound(Bind),
    /// The `use` takes the module that writes it.
    SelfUse,
    /// The `use` takes an item of the module that writes it (E0304, S-675; not written by the generator).
    OwnItem,
    /// The path ends before its end: the module read last.
    Stopped(usize),
}

/// The head, the path and the list of `u`, read by the names stage in the module `mid`; the head that is
/// a name another `use` took is read after all (`scope`).
fn resolve_use(t: &Tree, mid: usize, u: &Use) -> (Option<Why>, Vec<Bind>) {
    let head = &u.segs[0];
    let mut cur = if let Some(id) = t.child(ROOT, head) {
        id
    } else if head == "std" {
        STD
    } else if head == "fx" {
        return (Some(Why::OwnPkg), vec![]);
    } else {
        return (Some(Why::Unknown), vec![]);
    };
    let mut full = vec![head.clone()];
    let rest = &u.segs[1..];
    let mut binds = Vec::new();
    match &u.list {
        None => {
            if rest.is_empty() {
                binds.push(Bind { name: head.clone(), ent: Ent::Mod(cur), full: full.clone() });
            }
            for (i, seg) in rest.iter().enumerate() {
                let last = i + 1 == rest.len();
                if let Some(c) = t.child(cur, seg) {
                    cur = c;
                    full.push(seg.clone());
                    if last {
                        binds.push(Bind { name: seg.clone(), ent: Ent::Mod(c), full: full.clone() });
                    }
                } else if last && t.nodes[cur].items.contains(seg) {
                    let mut f = full.clone();
                    f.push(seg.clone());
                    binds.push(Bind { name: seg.clone(), ent: Ent::Item(cur, seg.clone()), full: f });
                } else {
                    return (Some(Why::Stopped(cur)), vec![]);
                }
            }
        }
        Some(list) => {
            for seg in rest {
                match t.child(cur, seg) {
                    Some(c) => {
                        cur = c;
                        full.push(seg.clone());
                    }
                    None => return (Some(Why::Stopped(cur)), vec![]),
                }
            }
            if list.is_empty() {
                return (Some(Why::Stopped(cur)), vec![]);
            }
            for e in list {
                let mut f = full.clone();
                f.push(e.clone());
                if let Some(c) = t.child(cur, e) {
                    binds.push(Bind { name: e.clone(), ent: Ent::Mod(c), full: f });
                } else if t.nodes[cur].items.contains(e) {
                    binds.push(Bind { name: e.clone(), ent: Ent::Item(cur, e.clone()), full: f });
                } else {
                    return (Some(Why::Stopped(cur)), vec![]);
                }
            }
        }
    }
    if binds.iter().any(|b| matches!(&b.ent, Ent::Item(m, _) if *m == mid)) {
        return (Some(Why::OwnItem), vec![]);
    }
    // S-679, S-685: the module itself is the one element that fails; the other elements of the list are taken.
    if binds.iter().any(|b| matches!(&b.ent, Ent::Mod(id) if *id == mid)) {
        binds.retain(|b| !matches!(&b.ent, Ent::Mod(id) if *id == mid));
        return (Some(Why::SelfUse), binds);
    }
    (None, binds)
}

/// The modules a `use` depends on (S-594): a module taken is the module and every module below it, an item
/// taken is the module of the item; the module that writes the `use` and `std` are left out. A name that
/// failed in the names stage is no dependency (§15.1, S-678), and only the names that were bound are in
/// `binds` (a `use` that fails whole has none).
fn use_edges(t: &Tree, mid: usize, binds: &[Bind]) -> Vec<usize> {
    let mut out = Vec::new();
    for b in binds {
        match &b.ent {
            Ent::Mod(id) if !t.nodes[*id].ext => out.extend(t.below(*id).into_iter().filter(|&x| x != mid)),
            Ent::Item(m, _) if !t.nodes[*m].ext && *m != mid => out.push(*m),
            _ => {}
        }
    }
    out.sort();
    out.dedup();
    out
}

struct UseEval {
    why: Option<Why>,
    binds: Vec<Bind>,
    edges: Vec<usize>,
}

/// What the names stage knows of one module: how each `use` is read, the names that were bound, whether two
/// names clashed (E0304), the names a failed `use` wrote.
struct Scope {
    evals: Vec<UseEval>,
    binds: BTreeMap<String, Bind>,
    clash: bool,
    failed: BTreeSet<String>,
}

fn scope(p: &Prog, mid: usize) -> Scope {
    let t = &p.tree;
    let m = p.module(mid);
    let mut evals: Vec<UseEval> = m
        .uses
        .iter()
        .map(|u| {
            let (why, binds) = resolve_use(t, mid, u);
            UseEval { why, binds, edges: vec![] }
        })
        .collect();
    let mut map: BTreeMap<String, Bind> = BTreeMap::new();
    let mut clash = false;
    for e in &evals {
        for b in &e.binds {
            if map.contains_key(&b.name) || t.nodes[mid].items.contains(&b.name) {
                clash = true;
            } else {
                map.insert(b.name.clone(), b.clone());
            }
        }
    }
    let mut failed = BTreeSet::new();
    for (u, e) in m.uses.iter().zip(evals.iter_mut()) {
        if e.why == Some(Why::Unknown) {
            if let Some(b) = map.get(&u.segs[0]) {
                e.why = Some(Why::Bound(b.clone()));
            }
        }
        e.edges = use_edges(t, mid, &e.binds);
        if e.why.is_some() {
            failed.extend(u.names().into_iter().filter(|n| !e.binds.iter().any(|b| &b.name == n)));
        }
    }
    Scope { evals, binds: map, clash, failed }
}

/// The strongly connected components of the dependencies, of two modules or more (S-594).
fn comps(p: &Prog) -> BTreeSet<BTreeSet<usize>> {
    let ids: Vec<usize> = p.mods.iter().map(|m| m.id).collect();
    let mut edges: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for &id in &ids {
        for e in scope(p, id).evals {
            edges.entry(id).or_default().extend(e.edges);
        }
    }
    let reach = |s: usize| -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![s];
        while let Some(x) = stack.pop() {
            for &y in edges.get(&x).into_iter().flatten() {
                if seen.insert(y) {
                    stack.push(y);
                }
            }
        }
        seen
    };
    let reached: BTreeMap<usize, BTreeSet<usize>> = ids.iter().map(|&i| (i, reach(i))).collect();
    let mut out = BTreeSet::new();
    for &i in &ids {
        if reached[&i].contains(&i) {
            out.insert(
                reached[&i].iter().copied().filter(|j| reached.get(j).is_some_and(|r| r.contains(&i))).collect(),
            );
        }
    }
    out
}

fn named(p: &Prog, c: &BTreeSet<usize>) -> BTreeSet<String> {
    c.iter().map(|&i| p.tree.dotted(i)).collect()
}

/// Whether narrowing cuts the component (§15.1, S-683): the E0310 of a component has notes that show how
/// to narrow the path (at places) when narrowing every `use` that takes a module with a file to that module
/// alone cuts the component; otherwise it has the rule (a note with no place), and its notes at the other
/// `use` of the cycle only say they are in it (§18.1, S-734). A module with no file has
/// no items, so a `use` of it is not narrowed: it stays the module and every module below it.
fn narrowing_cuts(p: &Prog, comp: &BTreeSet<usize>) -> bool {
    let t = &p.tree;
    let mut edges: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for m in &p.mods {
        for e in &scope(p, m.id).evals {
            for b in &e.binds {
                let targets = match &b.ent {
                    Ent::Mod(c) if !t.nodes[*c].file => t.below(*c),
                    Ent::Mod(c) | Ent::Item(c, _) => vec![*c],
                };
                for target in targets.into_iter().filter(|&x| !t.nodes[x].ext && x != m.id) {
                    edges.entry(m.id).or_default().insert(target);
                }
            }
        }
    }
    !comp.iter().any(|&i| reaches(&edges, i, i))
}

/// Whether `to` can be reached from `from` by one edge or more.
fn reaches(edges: &BTreeMap<usize, BTreeSet<usize>>, from: usize, to: usize) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![from];
    while let Some(x) = stack.pop() {
        for &y in edges.get(&x).into_iter().flatten() {
            if y == to {
                return true;
            }
            if seen.insert(y) {
                stack.push(y);
            }
        }
    }
    false
}

// ---- what a path in a body reads ---------------------------------------------------------------------------

/// How the names stage reads the head of a body path.
#[derive(Clone, Debug, PartialEq)]
enum Class {
    /// The path is read whole.
    Ok,
    /// The head is a name that is nothing to complain of: the member of a binding that is not there, or a
    /// name a failed `use` wrote. The spec leaves these to other stages; the generator does not write them.
    Silent,
    /// The path starts with the own absolute path of the module: its length.
    OwnAbs(usize),
    /// The head is the name of the module itself (and no module at the root has the name).
    OwnName,
    /// The head is the own package name.
    OwnPkg,
    /// The head is the own package name and the own absolute path of the module follows it: its length.
    OwnPkgAbs(usize),
    /// The head is a module at the root that no `use` took.
    Root,
    /// The head is a module at the root, and the name of the module itself, the module being below the root.
    RootTie,
    /// The head is `std`, not taken.
    Std,
    Unknown,
}

/// Whether `rest` goes from the entity to an item that can be called.
fn walks_to_item(t: &Tree, ent: &Ent, rest: &[String]) -> bool {
    match ent {
        Ent::Item(..) => rest.is_empty(),
        Ent::Mod(id) => {
            let mut cur = *id;
            for (i, s) in rest.iter().enumerate() {
                let last = i + 1 == rest.len();
                if let Some(c) = t.child(cur, s) {
                    if last {
                        return false;
                    }
                    cur = c;
                } else {
                    return last && t.nodes[cur].items.contains(s);
                }
            }
            false
        }
    }
}

fn classify(p: &Prog, mid: usize, sc: &Scope, b: &Body) -> Class {
    let t = &p.tree;
    let head = &b.segs[0];
    if t.nodes[mid].items.contains(head) {
        return if b.segs.len() == 1 { Class::Ok } else { Class::Silent };
    }
    if let Some(bind) = sc.binds.get(head) {
        return if walks_to_item(t, &bind.ent, &b.segs[1..]) { Class::Ok } else { Class::Silent };
    }
    if sc.failed.contains(head) {
        return Class::Silent;
    }
    let own = t.path(mid);
    let k = own.len();
    if k >= 2 && b.segs.len() > k && b.segs[..k] == own[..] {
        return Class::OwnAbs(k);
    }
    if head == "fx" {
        let rest = &b.segs[1..];
        return if rest.len() > k && rest[..k] == own[..] { Class::OwnPkgAbs(k) } else { Class::OwnPkg };
    }
    if *head == own[k - 1] {
        return match t.child(ROOT, head) {
            Some(id) if id != mid => Class::RootTie,
            _ => Class::OwnName,
        };
    }
    if head == "std" {
        return Class::Std;
    }
    if t.child(ROOT, head).is_some() {
        return Class::Root;
    }
    Class::Unknown
}

// ---- the candidates -----------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Edit {
    /// The `use` number `ui` becomes the `use` lines `repl`.
    Use { mid: usize, ui: usize, repl: Vec<Use> },
    /// The path of the body number `bi` becomes `segs`, and the `use` `add` is added.
    Body { mid: usize, bi: usize, segs: Vec<String>, add: Option<Use> },
}

impl Edit {
    fn mid(&self) -> usize {
        match self {
            Edit::Use { mid, .. } | Edit::Body { mid, .. } => *mid,
        }
    }
}

/// What the model says of the candidate of a fault.
enum Cand {
    /// None is given.
    None,
    /// One is given, and this is what it does.
    Some(Edit),
}

fn apply_edit(p: &Prog, e: &Edit) -> Prog {
    let mut q = p.clone();
    match e {
        Edit::Use { mid, ui, repl } => {
            q.module_mut(*mid).uses.splice(*ui..*ui + 1, repl.iter().cloned());
        }
        Edit::Body { mid, bi, segs, add } => {
            let m = q.module_mut(*mid);
            m.bodies[*bi].segs = segs.clone();
            if let Some(u) = add {
                m.uses.push(u.clone());
            }
        }
    }
    q
}

/// §18.1, S-686: the candidate is safe when, applied alone, what it was given for is read whole, no name is
/// bound twice and no cycle is closed: the components of the dependencies are the same, and the edges that
/// the new `use` lines add are on no cycle (a `use` between two modules of a cycle that is there already
/// closes a cycle too).
fn safe(p: &Prog, e: &Edit) -> bool {
    let after = apply_edit(p, e);
    let before_comps = comps(p);
    if before_comps != comps(&after) {
        return false;
    }
    let sc = scope(&after, e.mid());
    if sc.clash {
        return false;
    }
    let read_whole = match e {
        Edit::Use { ui, repl, .. } => (*ui..*ui + repl.len()).all(|i| sc.evals[i].why.is_none()),
        Edit::Body { mid, bi, add, .. } => {
            (add.is_none() || sc.evals.last().unwrap().why.is_none())
                && classify(&after, *mid, &sc, &after.module(*mid).bodies[*bi]) == Class::Ok
        }
    };
    if !read_whole {
        return false;
    }
    // The modules the new `use` lines take: a cycle through the module and one of them is closed by the
    // line, or is the one there already when the two are in one component (S-686).
    let fresh: Vec<usize> = match e {
        Edit::Use { ui, repl, .. } => (*ui..*ui + repl.len()).flat_map(|i| sc.evals[i].edges.clone()).collect(),
        Edit::Body { add: Some(_), .. } => sc.evals.last().unwrap().edges.clone(),
        Edit::Body { add: None, .. } => vec![],
    };
    !fresh.iter().any(|t| before_comps.iter().any(|c| c.contains(&e.mid()) && c.contains(t)))
}

fn checked(p: &Prog, e: Option<Edit>) -> Cand {
    match e {
        Some(e) if safe(p, &e) => Cand::Some(e),
        _ => Cand::None,
    }
}

/// §15.1, S-37, S-663: the candidate of a `use` that failed in the head.
fn use_cand(p: &Prog, mid: usize, ui: usize) -> Cand {
    let sc = scope(p, mid);
    let u = &p.module(mid).uses[ui];
    let repl = match &sc.evals[ui].why {
        Some(Why::OwnPkg) if u.segs.len() == 1 => match &u.list {
            Some(l) if !l.is_empty() => l.iter().map(|e| Use { segs: vec![e.clone()], list: None }).collect(),
            _ => return Cand::None,
        },
        Some(Why::OwnPkg) => vec![Use { segs: u.segs[1..].to_vec(), list: u.list.clone() }],
        Some(Why::Bound(b)) => match b.ent {
            Ent::Item(..) => return Cand::None,
            Ent::Mod(_) => {
                let mut segs = b.full.clone();
                segs.extend_from_slice(&u.segs[1..]);
                vec![Use { segs, list: u.list.clone() }]
            }
        },
        _ => return Cand::None,
    };
    checked(p, Some(Edit::Use { mid, ui, repl }))
}

/// The `use` of the head `name` to add, when no `use` of the module took that name.
fn add_head(sc: &Scope, segs: &[String]) -> Option<Use> {
    if sc.binds.contains_key(segs.last().unwrap()) { None } else { Some(Use { segs: segs.to_vec(), list: None }) }
}

/// S-673: the path with the part that names the module itself dropped: `rest` is what is left.
fn strip_own(p: &Prog, mid: usize, sc: &Scope, bi: usize, rest: &[String]) -> Option<Edit> {
    let t = &p.tree;
    let r0 = rest.first()?;
    if t.nodes[mid].items.contains(r0) {
        Some(Edit::Body { mid, bi, segs: rest.to_vec(), add: None })
    } else if t.child(mid, r0).is_some() {
        let mut child = t.path(mid);
        child.push(r0.clone());
        Some(Edit::Body { mid, bi, segs: rest.to_vec(), add: add_head(sc, &child) })
    } else {
        None
    }
}

/// §15.1, S-673, R-39, R-268: the candidate of a path in a body.
fn body_cand(p: &Prog, mid: usize, bi: usize) -> Cand {
    let sc = scope(p, mid);
    let b = &p.module(mid).bodies[bi];
    let head = &b.segs[0];
    match classify(p, mid, &sc, b) {
        Class::Ok | Class::Silent | Class::Unknown => Cand::None,
        Class::Std | Class::Root => checked(
            p,
            Some(Edit::Body { mid, bi, segs: b.segs.clone(), add: add_head(&sc, std::slice::from_ref(head)) }),
        ),
        Class::RootTie => {
            // The module at the root is read first; when the path is not read whole that way, the name of
            // the module itself is (S-673). When the root reading is read whole and closes a cycle there is
            // no candidate: the name of the module itself is not read then (S-687).
            let root = Edit::Body { mid, bi, segs: b.segs.clone(), add: add_head(&sc, std::slice::from_ref(head)) };
            let after = apply_edit(p, &root);
            let sc2 = scope(&after, mid);
            if classify(&after, mid, &sc2, &after.module(mid).bodies[bi]) == Class::Ok {
                checked(p, Some(root))
            } else {
                checked(p, strip_own(p, mid, &sc, bi, &b.segs[1..]))
            }
        }
        Class::OwnName => checked(p, strip_own(p, mid, &sc, bi, &b.segs[1..])),
        Class::OwnAbs(k) => checked(p, strip_own(p, mid, &sc, bi, &b.segs[k..])),
        // S-684: the package name and the own absolute path that follows it are taken off together.
        Class::OwnPkgAbs(k) => checked(p, strip_own(p, mid, &sc, bi, &b.segs[1 + k..])),
        Class::OwnPkg => {
            let rest = &b.segs[1..];
            if rest.len() < 2 {
                return Cand::None;
            }
            checked(p, Some(Edit::Body { mid, bi, segs: rest.to_vec(), add: add_head(&sc, &rest[..1]) }))
        }
    }
}

// ---- the generator ---------------------------------------------------------------------------------------

const POOL: [&str; 14] =
    ["a", "b", "c", "d", "main", "a/b", "a/c", "d/e", "d/e/a", "b/a", "a/b/c", "d/b", "main/inner", "c/d"];
const ITEMS: [&str; 3] = ["f", "g", "h"];

fn gen_tree(r: &mut Rng) -> Tree {
    let mut t = Tree::new();
    for path in POOL {
        if r.chance(if path == "main" { 85 } else { 60 }) {
            let id = t.ensure(path);
            t.nodes[id].file = true;
            let mut items = ITEMS.to_vec();
            r.shuffle(&mut items);
            for it in items.into_iter().take(r.range(0, 2)) {
                t.nodes[id].items.insert(it.into());
            }
        }
    }
    t
}

fn pick_some(r: &mut Rng, names: &[String], lo: usize, hi: usize) -> Vec<String> {
    let mut v = names.to_vec();
    r.shuffle(&mut v);
    v.truncate(r.range(lo, hi.min(v.len().max(lo))));
    v
}

/// A `use` of the kinds the model reads, drawn at random (it may be unfit for the module; `add_use` asks).
fn gen_use(r: &mut Rng, p: &Prog, mid: usize) -> Option<Use> {
    let t = &p.tree;
    let mods = t.modules();
    let target = *r.pick(&mods);
    let tpath = t.path(target);
    let root_names: Vec<String> = t.nodes[ROOT].children.keys().cloned().collect();
    let with_members = |r: &mut Rng, q: usize| -> Option<Vec<String>> {
        let members = t.members(q);
        if members.is_empty() { None } else { Some(pick_some(r, &members, 1, 3)) }
    };
    let strs = |v: &[String]| v.to_vec();
    if root_names.is_empty() {
        return None;
    }
    match r.below(100) {
        0..=57 => match r.below(10) {
            0..=4 => Some(Use { segs: strs(&tpath), list: None }),
            5..=6 => {
                let it = t.nodes[target].items.iter().next()?.clone();
                let mut segs = strs(&tpath);
                segs.push(it);
                Some(Use { segs, list: None })
            }
            _ => Some(Use { segs: strs(&tpath), list: Some(with_members(r, target)?) }),
        },
        58..=69 => match r.below(10) {
            0..=3 => {
                let mut segs = vec!["fx".to_string()];
                segs.extend(tpath);
                Some(Use { segs, list: None })
            }
            4..=5 => {
                let mut names = pick_some(r, &root_names, 1, 3);
                if r.chance(20) {
                    names.push(names[0].clone());
                }
                Some(Use { segs: vec!["fx".into()], list: Some(names) })
            }
            6 => Some(Use { segs: vec!["fx".into()], list: None }),
            _ => {
                let mut segs = vec!["fx".to_string()];
                segs.extend(tpath);
                Some(Use { segs, list: Some(with_members(r, target)?) })
            }
        },
        70..=79 => Some(match r.below(7) {
            0 => Use::new(&["std"], None),
            1 | 2 => Use::new(&["std", "math"], None),
            3 => Use::new(&["std", "math", "sin"], None),
            4 => Use::new(&["std", "math"], Some(&["sin", "cos"])),
            5 => Use::new(&["std"], Some(&["math"])),
            _ => Use::new(&["std", "zz"], None),
        }),
        80..=84 => Some(match r.below(3) {
            0 => Use::new(&["zz"], None),
            1 => Use::new(&["zz", "a"], None),
            _ => Use::new(&["zz"], Some(&["f"])),
        }),
        85..=89 => {
            // The module takes itself (S-679); only in a module with no module below it. In a list it can have
            // other names of the module above (S-685: they are taken, the module itself is the one that fails).
            let own = t.path(mid);
            if own.len() >= 2 && r.chance(50) {
                let last = own.last().unwrap().clone();
                let parent = t.nodes[mid].parent.unwrap();
                let others: Vec<String> = t.members(parent).into_iter().filter(|m| *m != last).collect();
                let mut names = vec![last];
                if !others.is_empty() && r.chance(60) {
                    names.extend(pick_some(r, &others, 1, 2));
                    r.shuffle(&mut names);
                }
                Some(Use { segs: own[..own.len() - 1].to_vec(), list: Some(names) })
            } else {
                Some(Use { segs: own, list: None })
            }
        }
        _ => {
            // `use m.zz` with `m` a module at the root that has no module below it (S-678).
            let leaves: Vec<String> =
                root_names.iter().filter(|n| t.is_leaf(t.child(ROOT, n).unwrap())).cloned().collect();
            if leaves.is_empty() {
                return None;
            }
            let l = r.pick(&leaves).clone();
            if r.chance(50) {
                Some(Use { segs: vec![l, "zz".into()], list: None })
            } else {
                Some(Use { segs: vec![l], list: Some(vec!["zz".into()]) })
            }
        }
    }
}

/// A `use` whose head is a name another `use` of the module took (S-37).
fn gen_bound_use(r: &mut Rng, p: &Prog, mid: usize) -> Option<Use> {
    let t = &p.tree;
    let sc = scope(p, mid);
    let names: Vec<&Bind> =
        sc.binds.values().filter(|b| t.child(ROOT, &b.name).is_none() && b.name != "std" && b.name != "fx").collect();
    if names.is_empty() {
        return None;
    }
    let b = (*r.pick(&names)).clone();
    match b.ent {
        Ent::Item(..) => Some(Use { segs: vec![b.name, "x".into()], list: None }),
        Ent::Mod(id) => {
            let members = t.members(id);
            let head = vec![b.name.clone()];
            if members.is_empty() {
                return Some(Use { segs: head, list: None });
            }
            match r.below(10) {
                0..=2 => Some(Use { segs: head, list: None }),
                3..=6 => {
                    let mut segs = head;
                    segs.push(r.pick(&members).clone());
                    Some(Use { segs, list: None })
                }
                _ => Some(Use { segs: head, list: Some(pick_some(r, &members, 1, 3)) }),
            }
        }
    }
}

/// Add `u` to the module when the model can read it as the generator wants: no name bound twice, no module
/// that takes itself with modules below it, a path that stops only in the planned shape, no head that a
/// failed `use` wrote, and no cycle when `acyclic`.
fn add_use(p: &mut Prog, mid: usize, u: Use, acyclic: bool) -> bool {
    if p.module(mid).uses.contains(&u) {
        return false;
    }
    let mut q = p.clone();
    q.module_mut(mid).uses.push(u.clone());
    let sc = scope(&q, mid);
    if sc.clash {
        return false;
    }
    let ev = sc.evals.last().unwrap();
    let t = &q.tree;
    match &ev.why {
        Some(Why::OwnItem) => return false,
        Some(Why::SelfUse) if !t.is_leaf(mid) => return false,
        Some(Why::Stopped(l)) if !t.nodes[*l].ext => {
            let zz_list = u.segs.len() == 1 && u.list.as_deref() == Some(&["zz".to_string()][..]);
            let planned = t.is_leaf(*l)
                && t.nodes[*l].parent == Some(ROOT)
                && ((u.segs.len() == 2 && u.list.is_none()) || zz_list);
            if !planned {
                return false;
            }
        }
        _ => {}
    }
    // The name a failed `use` wrote is silent in the places that use it (§18.1, U3b), so no `use` reads
    // through it.
    for e in &sc.evals {
        if let Some(Why::Bound(b)) = &e.why {
            if sc.failed.contains(&b.name) {
                return false;
            }
        }
    }
    if acyclic && !comps(&q).is_empty() {
        return false;
    }
    *p = q;
    true
}

fn item_of_ent(ent: &Ent, t: &Tree) -> bool {
    match ent {
        Ent::Item(m, _) => t.nodes[*m].ext,
        Ent::Mod(m) => t.nodes[*m].ext,
    }
}

/// A path for a body of the module, drawn at random in the kinds of the model.
fn gen_body(r: &mut Rng, p: &Prog, mid: usize, sc: &Scope) -> Option<Body> {
    let t = &p.tree;
    let items: Vec<String> = t.nodes[mid].items.iter().cloned().collect();
    let root_names: Vec<String> = t.nodes[ROOT].children.keys().cloned().collect();
    let descend = |r: &mut Rng, start: usize, max: usize| -> (Vec<String>, usize) {
        let mut segs = Vec::new();
        let mut cur = start;
        for _ in 0..r.range(0, max) {
            let kids: Vec<String> = t.nodes[cur].children.keys().cloned().collect();
            if kids.is_empty() {
                break;
            }
            let k = r.pick(&kids).clone();
            cur = t.child(cur, &k).unwrap();
            segs.push(k);
        }
        (segs, cur)
    };
    let finish = |r: &mut Rng, mut segs: Vec<String>, cur: usize, bad: usize| -> Vec<String> {
        let its: Vec<String> = t.nodes[cur].items.iter().cloned().collect();
        if its.is_empty() || r.chance(bad) {
            segs.push("zz".into());
        } else {
            segs.push(r.pick(&its).clone());
        }
        segs
    };
    match r.below(100) {
        0..=14 => {
            if items.is_empty() {
                return None;
            }
            Some(Body { segs: vec![r.pick(&items).clone()], std: false })
        }
        15..=44 => {
            let binds: Vec<&Bind> = sc.binds.values().collect();
            if binds.is_empty() {
                return None;
            }
            let b = (*r.pick(&binds)).clone();
            let std = item_of_ent(&b.ent, t);
            match b.ent {
                Ent::Item(..) => Some(Body { segs: vec![b.name], std }),
                Ent::Mod(id) => {
                    let (mut segs, cur) = descend(r, id, 2);
                    segs.insert(0, b.name);
                    if t.nodes[cur].items.is_empty() {
                        return None;
                    }
                    Some(Body { segs: finish(r, segs, cur, 0), std })
                }
            }
        }
        45..=58 => {
            let h = r.pick(&root_names).clone();
            let id = t.child(ROOT, &h).unwrap();
            let (mut segs, cur) = descend(r, id, 2);
            segs.insert(0, h);
            Some(Body { segs: finish(r, segs, cur, 30), std: false })
        }
        59..=65 => Some(Body { segs: vec!["std".into(), "math".into(), "sqrt".into()], std: true }),
        66..=73 => {
            let h = r.pick(&root_names).clone();
            let id = t.child(ROOT, &h).unwrap();
            let (mut segs, cur) = descend(r, id, 2);
            segs.insert(0, h);
            segs.insert(0, "fx".into());
            Some(Body { segs: finish(r, segs, cur, 20), std: false })
        }
        74..=94 => {
            let own = t.path(mid);
            let mut segs = if own.len() >= 2 && r.chance(50) { own.clone() } else { vec![own.last().unwrap().clone()] };
            let (down, cur) = descend(r, mid, 1);
            segs.extend(down);
            Some(Body { segs: finish(r, segs, cur, 20), std: false })
        }
        _ => Some(Body { segs: vec!["zz".into(), "f".into()], std: false }),
    }
}

/// Add a body path when the model can read it as the generator wants: not one the spec leaves to another
/// stage, and for the candidate that names a new head, one that a `use` of the module took only for the
/// module the head names.
fn add_body(p: &mut Prog, mid: usize, b: Body) -> bool {
    let mut q = p.clone();
    q.module_mut(mid).bodies.push(b.clone());
    let sc = scope(&q, mid);
    let class = classify(&q, mid, &sc, &b);
    let t = &q.tree;
    let new_head: Option<(String, Ent)> = match class {
        Class::Silent => return false,
        Class::OwnPkg => {
            let r0 = b.segs.get(1).cloned();
            match r0 {
                Some(r0) => t.child(ROOT, &r0).map(|id| (r0, Ent::Mod(id))),
                None => return false,
            }
        }
        Class::OwnPkgAbs(k) => b.segs.get(1 + k).and_then(|r0| t.child(mid, r0).map(|c| (r0.clone(), Ent::Mod(c)))),
        Class::OwnName | Class::OwnAbs(_) | Class::RootTie => {
            let k = if let Class::OwnAbs(k) = class { k } else { 1 };
            match b.segs.get(k) {
                Some(r0) => t.child(mid, r0).map(|c| (r0.clone(), Ent::Mod(c))),
                None => None,
            }
        }
        _ => None,
    };
    if let Some((name, ent)) = new_head {
        if let Some(bound) = sc.binds.get(&name) {
            if bound.ent != ent {
                return false;
            }
        }
    }
    *p = q;
    true
}

fn gen_prog(seed: u64) -> Prog {
    let mut r = Rng::new(seed);
    let tree = gen_tree(&mut r);
    let mods: Vec<Module> = tree
        .modules()
        .into_iter()
        .filter(|&i| tree.nodes[i].file)
        .map(|id| Module { id, uses: vec![], bodies: vec![] })
        .collect();
    let mut p = Prog { tree, mods };
    let acyclic = r.chance(45);
    let ids: Vec<usize> = p.mods.iter().map(|m| m.id).collect();
    for &id in &ids {
        for _ in 0..r.range(0, if acyclic { 3 } else { 4 }) {
            for _ in 0..6 {
                if let Some(u) = gen_use(&mut r, &p, id) {
                    if add_use(&mut p, id, u, acyclic) {
                        break;
                    }
                }
            }
        }
    }
    for &id in &ids {
        if r.chance(35) {
            for _ in 0..4 {
                if let Some(u) = gen_bound_use(&mut r, &p, id) {
                    if add_use(&mut p, id, u, acyclic) {
                        break;
                    }
                }
            }
        }
    }
    for &id in &ids {
        for _ in 0..r.range(1, 4) {
            for _ in 0..6 {
                let sc = scope(&p, id);
                if let Some(b) = gen_body(&mut r, &p, id, &sc) {
                    if add_body(&mut p, id, b) {
                        break;
                    }
                }
            }
        }
    }
    p
}

// ---- the expectations -------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Site {
    Use(usize, usize),
    Body(usize, usize),
}

/// The text that names a site in a text: the file and the `use` line, or the file and the header of the
/// function.
fn key_of(p: &Prog, s: &Site) -> String {
    match s {
        Site::Use(m, i) => format!("{}|{}", p.file_of(*m), p.module(*m).uses[*i].text()),
        Site::Body(m, i) => format!("{}|{}", p.file_of(*m), body_header(*i, &p.module(*m).bodies[*i])),
    }
}

/// The key of a diagnostic in `texts`: the file and the `use` line, or the file and the header of the
/// function around the line.
fn key_in(texts: &Texts, d: &Diag) -> String {
    let lines: Vec<&str> = texts[&d.file].lines().collect();
    let line = lines[d.line as usize - 1];
    if line.starts_with("use ") {
        return format!("{}|{line}", d.file);
    }
    for i in (0..d.line as usize).rev() {
        if lines[i].starts_with("pub fn ") {
            return format!("{}|{}", d.file, lines[i]);
        }
    }
    format!("{}|?", d.file)
}

struct Expect {
    /// The sites of an E0302.
    e0302: BTreeSet<Site>,
    /// The sites of an E0302 that may be there or not: a `use` that is partly bound (S-685), in a module of a
    /// cycle, where the E0310 may be the diagnostic that the unit reports (§18.1; the place of the E0310 is
    /// not fixed).
    maybe: BTreeSet<Site>,
    comps: BTreeSet<BTreeSet<usize>>,
}

fn expect(p: &Prog) -> Expect {
    let cs = comps(p);
    let mut e0302 = BTreeSet::new();
    let mut maybe = BTreeSet::new();
    for m in &p.mods {
        let sc = scope(p, m.id);
        for (i, ev) in sc.evals.iter().enumerate() {
            // A `use` that failed whole makes no dependency (S-678), so no E0310 hides its E0302. One that
            // is partly bound has the edges of the names that were bound, and in a module of a cycle the
            // E0310 may be on it.
            if ev.why.is_some() {
                if !ev.binds.is_empty() && cs.iter().any(|c| c.contains(&m.id)) {
                    maybe.insert(Site::Use(m.id, i));
                } else {
                    e0302.insert(Site::Use(m.id, i));
                }
            }
        }
        for bi in 0..m.bodies.len() {
            let class = classify(p, m.id, &sc, &m.bodies[bi]);
            assert!(class != Class::Silent, "the generator wrote a path the model leaves out");
            if !matches!(class, Class::Ok) {
                e0302.insert(Site::Body(m.id, bi));
            }
        }
    }
    Expect { e0302, maybe, comps: cs }
}

fn cand_of(p: &Prog, s: &Site) -> Cand {
    match s {
        Site::Use(m, i) => use_cand(p, *m, *i),
        Site::Body(m, i) => body_cand(p, *m, *i),
    }
}

/// Texts of the same module, except for the place where the lines of `use` stand and the blank lines.
fn same_modulo_use_place(a: &str, b: &str) -> bool {
    let split = |s: &str| {
        let mut uses: Vec<String> = s.lines().filter(|l| l.starts_with("use ")).map(String::from).collect();
        uses.sort();
        let rest: Vec<String> =
            s.lines().filter(|l| !l.starts_with("use ") && !l.trim().is_empty()).map(String::from).collect();
        (uses, rest)
    };
    split(a) == split(b)
}

fn dump(texts: &Texts) -> String {
    texts.iter().map(|(f, t)| format!("--- {f}\n{t}")).collect::<Vec<_>>().join("")
}

/// The sites of the E0302 in `c`, and the sets of modules of the E0310; codes other than these two go to
/// `problems`.
fn observe(
    texts: &Texts,
    c: &Checked,
    what: &str,
    after_candidate: bool,
    problems: &mut Vec<String>,
) -> (BTreeMap<String, Diag>, BTreeSet<BTreeSet<String>>) {
    let mut sites = BTreeMap::new();
    let mut cycles = BTreeSet::new();
    for d in &c.diags {
        match d.code.as_str() {
            "E0302" => {
                let k = key_in(texts, d);
                if sites.insert(k.clone(), d.clone()).is_some() {
                    problems.push(format!("{what}: two E0302 for {k}"));
                }
            }
            "E0310" => {
                cycles.insert(quoted(&d.message).into_iter().collect::<BTreeSet<String>>());
            }
            // R-254, W4-04: the member of a name that a candidate took is not found by the types stage; the
            // path was an E0302 on its head before, and the unit reports one.
            "E0401" if after_candidate => {}
            _ => problems.push(format!(
                "{what}: a diagnostic the model has none of: {} {}:{} {}",
                d.code, d.file, d.line, d.message
            )),
        }
    }
    (sites, cycles)
}

/// What a sweep covered, so that a sweep that lost its subject fails.
#[derive(Default, Debug)]
struct Stats {
    packages: usize,
    with_cycles: usize,
    use_faults: usize,
    body_faults: usize,
    given: usize,
    withheld: usize,
    applied: usize,
    /// The `use` lines that have the module itself and other names (S-685).
    partial_self: usize,
    shapes_compared: usize,
    cycles: usize,
    notes_checked: usize,
    notes_narrow: usize,
    /// The faults by kind and by what the model says of the candidate: `body OwnAbs given`.
    kinds: BTreeMap<String, usize>,
}

/// The kind of the fault at a site, for the account of what a sweep covered.
fn kind_of(p: &Prog, s: &Site) -> String {
    match s {
        Site::Use(m, i) => {
            let why = scope(p, *m).evals[*i].why.clone().unwrap();
            let k = match why {
                Why::Bound(b) => match b.ent {
                    Ent::Item(..) => "Bound-item".to_string(),
                    Ent::Mod(_) => "Bound-module".to_string(),
                },
                Why::OwnPkg => {
                    let u = &p.module(*m).uses[*i];
                    match (u.segs.len(), &u.list) {
                        (1, None) => "OwnPkg-whole".into(),
                        (1, Some(l)) if l.len() == 1 => "OwnPkg-list-1".into(),
                        (1, Some(_)) => "OwnPkg-list".into(),
                        _ => "OwnPkg-path".into(),
                    }
                }
                other => format!("{other:?}").split('(').next().unwrap().to_string(),
            };
            format!("use {k}")
        }
        Site::Body(m, i) => {
            let sc = scope(p, *m);
            let c = classify(p, *m, &sc, &p.module(*m).bodies[*i]);
            format!("body {}", format!("{c:?}").split('(').next().unwrap())
        }
    }
}

fn run_seed(seed: u64, st: &mut Stats) -> Vec<String> {
    let p = gen_prog(seed);
    let texts = render(&p);
    let ex = expect(&p);
    st.packages += 1;
    st.with_cycles += !ex.comps.is_empty() as usize;
    st.use_faults += ex.e0302.iter().filter(|s| matches!(s, Site::Use(..))).count();
    st.partial_self += p
        .mods
        .iter()
        .flat_map(|m| scope(&p, m.id).evals)
        .filter(|ev| ev.why == Some(Why::SelfUse) && !ev.binds.is_empty())
        .count();
    st.body_faults += ex.e0302.iter().filter(|s| matches!(s, Site::Body(..))).count();
    let what = format!("seed {seed}");
    let mut problems = Vec::new();
    let c = check_input(&input_of("fx", &texts));
    if !ended_well(&c) {
        return vec![format!("{what}: ended with code {} {:?}\n{}", c.code, c.stderr.lines().next(), dump(&texts))];
    }
    let (sites, cycles) = observe(&texts, &c, &what, false, &mut problems);
    // E0302: the sites.
    let expected: BTreeSet<String> = ex.e0302.iter().map(|s| key_of(&p, s)).collect();
    for k in &expected {
        if !sites.contains_key(k) {
            problems.push(format!("{what}: no E0302 for {k}"));
        }
    }
    let maybe: BTreeSet<String> = ex.maybe.iter().map(|s| key_of(&p, s)).collect();
    for k in sites.keys() {
        if !expected.contains(k) && !maybe.contains(k) {
            problems.push(format!("{what}: an E0302 for {k}, which the model reads whole"));
        }
    }
    // E0310: the modules of the components, and the note.
    let want_cycles: BTreeSet<BTreeSet<String>> = ex.comps.iter().map(|c| named(&p, c)).collect();
    if cycles != want_cycles {
        problems.push(format!("{what}: the modules of the E0310: {cycles:?}, the model: {want_cycles:?}"));
    }
    for e in c.of_code("E0310") {
        st.cycles += 1;
        let comp: BTreeSet<String> = quoted(&e.message).into_iter().collect();
        if e.notes == 0 {
            problems.push(format!("{what}: an E0310 with no note: {comp:?}"));
        }
        // The other `use` of the cycle are in notes with places (§18.1, S-734): a cycle has two modules
        // or more, so a `use` other than the one of the E0310.
        if e.spanned_notes == 0 {
            problems.push(format!("{what}: an E0310 with no note at another `use`: {comp:?}"));
        }
        if let Some(ids) = ex.comps.iter().find(|c| named(&p, c) == comp) {
            // The rule, the note with no place, is there when narrowing does not cut the cycle (S-683);
            // when it cuts, the notes at the `use` show how.
            st.notes_checked += 1;
            let rule = e.notes > e.spanned_notes;
            st.notes_narrow += !rule as usize;
            if rule == narrowing_cuts(&p, ids) {
                problems.push(format!(
                    "{what}: the E0310 {comp:?} has the rule: {rule}, the cycle is cut by narrowing: {}",
                    narrowing_cuts(&p, ids)
                ));
            }
        }
    }
    // §15.1: each `use` is read whatever its place and whatever the other `use` lines are, so the faults
    // and the cycles are the same with the `use` lines of each module in the opposite order.
    {
        let mut reversed = p.clone();
        for m in &mut reversed.mods {
            m.uses.reverse();
        }
        let rtexts = render(&reversed);
        let rc = check_input(&input_of("fx", &rtexts));
        let tag = format!("{what} with the `use` lines in the opposite order");
        if !ended_well(&rc) {
            problems.push(format!("{tag}: ended with code {}", rc.code));
        } else {
            let (rsites, rcycles) = observe(&rtexts, &rc, &tag, false, &mut problems);
            let keys = |m: &BTreeMap<String, Diag>| -> BTreeSet<String> { m.keys().cloned().collect() };
            if keys(&rsites) != keys(&sites) {
                problems.push(format!("{tag}: the E0302 are {:?}, they were {:?}", keys(&rsites), keys(&sites)));
            }
            if rcycles != cycles {
                problems.push(format!("{tag}: the modules of the E0310 are {rcycles:?}, they were {cycles:?}"));
            }
        }
    }
    // The candidates.
    for site in &ex.e0302 {
        let k = key_of(&p, site);
        let Some(diag) = sites.get(&k) else { continue };
        let verdict = cand_of(&p, site);
        let outcome = match &verdict {
            Cand::None => {
                st.withheld += 1;
                "withheld"
            }
            Cand::Some(_) => {
                st.given += 1;
                "given"
            }
        };
        *st.kinds.entry(format!("{} {outcome}", kind_of(&p, site))).or_default() += 1;
        match &verdict {
            Cand::None if !diag.fixes.is_empty() => {
                problems.push(format!(
                    "{what}: a candidate for {k}, which closes a cycle or does not read whole: {}",
                    diag.fixes[0]["title"]
                ));
            }
            Cand::Some(_) if diag.fixes.len() != 1 => {
                problems.push(format!("{what}: {} candidates for {k}, the model has one", diag.fixes.len()));
            }
            _ => {}
        }
        for fix in &diag.fixes {
            let mut applied = texts.clone();
            apply_fix_texts(&mut applied, fix);
            st.applied += 1;
            let after = check_input(&input_of("fx", &applied));
            let tag = format!("{what}: the candidate {:?} for {k}", fix["title"].as_str().unwrap_or(""));
            if !ended_well(&after) {
                problems.push(format!("{tag}: ended with code {}", after.code));
                continue;
            }
            let (sites_after, cycles_after) = observe(&applied, &after, &tag, true, &mut problems);
            if sites_after.contains_key(&k) {
                problems.push(format!("{tag}: the fault is still there"));
            }
            for a in sites_after.keys() {
                if !sites.contains_key(a) {
                    problems.push(format!("{tag}: a new E0302 for {a}"));
                }
            }
            if cycles_after != cycles {
                problems.push(format!("{tag}: the modules of the E0310 were {cycles:?}, are {cycles_after:?}"));
            }
            if let Cand::Some(e) = &verdict {
                st.shapes_compared += 1;
                let predicted = render(&apply_edit(&p, e));
                let file = p.file_of(e.mid());
                if !same_modulo_use_place(&predicted[&file], &applied[&file]) {
                    problems.push(format!(
                        "{tag}: the module is\n{}but the spec names\n{}",
                        applied[&file], predicted[&file]
                    ));
                }
                for (f, t) in &applied {
                    if *f != file && t != &texts[f] {
                        problems.push(format!("{tag}: {f} was changed"));
                    }
                }
            }
        }
    }
    if !problems.is_empty() {
        problems.push(format!("{what}: the package was\n{}", dump(&texts)));
    }
    problems
}

const CHUNK: u64 = 40;

fn sweep(chunk: u64) {
    let mut problems = Vec::new();
    let mut st = Stats::default();
    for seed in chunk * CHUNK..(chunk + 1) * CHUNK {
        problems.extend(run_seed(seed, &mut st));
    }
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
    // A sweep that lost its subject passes for nothing: these are about half of what a chunk covers or less.
    assert_eq!(st.packages, CHUNK as usize);
    assert!(st.with_cycles >= 6 && st.cycles >= 6, "cycles: {st:?}");
    assert!(st.use_faults >= 120 && st.body_faults >= 300, "faults: {st:?}");
    assert!(st.given >= 150 && st.withheld >= 250, "candidates: {st:?}");
    assert!(st.shapes_compared >= 150 && st.applied >= 150, "applied: {st:?}");
    assert!(st.notes_checked >= 2, "notes of E0310: {st:?}");
    assert!(st.partial_self >= 1, "a `use` with the module itself and other names (S-685): {st:?}");
    for kind in [
        "body OwnAbs given",
        "body OwnName given",
        "body OwnPkg given",
        "body OwnPkgAbs given",
        "body Root given",
        "body Std given",
        "body RootTie given",
        "body RootTie withheld",
        "body Unknown withheld",
        "use Bound-module given",
        "use Bound-item withheld",
        "use OwnPkg-path given",
        "use OwnPkg-list withheld",
        "use SelfUse withheld",
        "use Stopped withheld",
        "use Unknown withheld",
    ] {
        assert!(st.kinds.get(kind).copied().unwrap_or(0) >= 1, "{kind}: {:?}", st.kinds);
    }
}

/// The loop of the first candidates over a generated package (the loop of `use_repair_loop.rs` on the
/// packages of the model, which have the faults of every kind, and cycles): it stops within four steps
/// for each fault and ten more, ends as a check does at every step, and the cycles are the cycles there
/// were (a candidate closes none and opens none).
fn repair_seed(seed: u64) -> Vec<String> {
    let p = gen_prog(seed);
    let mut texts = render(&p);
    let first = check_input(&input_of("fx", &texts));
    if !ended_well(&first) {
        return vec![format!("seed {seed}: ended with code {}", first.code)];
    }
    let cycles = |c: &Checked| -> BTreeSet<BTreeSet<String>> {
        c.of_code("E0310").iter().map(|e| quoted(&e.message).into_iter().collect()).collect()
    };
    let codes0: BTreeSet<String> = first.diags.iter().map(|x| x.code.clone()).collect();
    let cycles0 = cycles(&first);
    let faults = first.of_code("E0302").len();
    let cap = 4 * faults + 10;
    let mut problems = Vec::new();
    for step in 0..=cap {
        let c = check_input(&input_of("fx", &texts));
        if !ended_well(&c) {
            problems.push(format!("seed {seed}: step {step}: ended with code {}", c.code));
            break;
        }
        let new: Vec<String> = c
            .diags
            .iter()
            .map(|x| x.code.clone())
            // R-254, W4-04: the member of a name that a candidate took is found by the types stage.
            .filter(|code| !codes0.contains(code) && code != "E0401")
            .collect();
        if !new.is_empty() {
            problems.push(format!("seed {seed}: step {step}: the codes {new:?}, which the package did not have"));
            break;
        }
        if cycles(&c) != cycles0 {
            problems.push(format!("seed {seed}: step {step}: the cycles are {:?}, they were {cycles0:?}", cycles(&c)));
            break;
        }
        let Some(diag) = c.diags.iter().find(|x| x.code == "E0302" && !x.fixes.is_empty()) else { break };
        if step == cap {
            problems.push(format!("seed {seed}: {cap} steps (four for each of the {faults} faults and ten) and a candidate is still given for {} {}:{}", diag.code, diag.file, diag.line));
            break;
        }
        apply_fix_texts(&mut texts, &diag.fixes[0]);
    }
    if !problems.is_empty() {
        problems.push(format!("seed {seed}: the package was\n{}", dump(&render(&p))));
    }
    problems
}

fn repair_seeds(offset: u64) {
    let mut problems = Vec::new();
    for seed in (offset..4 * CHUNK).step_by(4) {
        problems.extend(repair_seed(seed));
    }
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
}

/// §18.1: the loop of candidates over the generated packages stops, adds no code and no cycle. The seeds
/// 0, 4, 8, ... below 160 (the tests above run each seed with each candidate alone).
#[test]
fn the_loop_of_candidates_on_generated_packages_stops_a() {
    repair_seeds(0);
}

/// The same for the seeds 2, 6, 10, ... below 160.
#[test]
fn the_loop_of_candidates_on_generated_packages_stops_b() {
    repair_seeds(2);
}

/// §15.1, §18.1: the packages of the seeds 0 to 39.
#[test]
fn model_seeds_0_to_39() {
    sweep(0);
}

/// The seeds 40 to 79.
#[test]
fn model_seeds_40_to_79() {
    sweep(1);
}

/// The seeds 80 to 119.
#[test]
fn model_seeds_80_to_119() {
    sweep(2);
}

/// The seeds 120 to 159.
#[test]
fn model_seeds_120_to_159() {
    sweep(3);
}
