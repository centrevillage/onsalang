//! The drop at the end of a block, counted by the paths that reach it, against a model of the paths (spec
//! §12.2, §8.1, §10 rule 1, §9.2, §7, §3.5, §5.2, §5.4; S-873, S-1042; W6-02 U2a/t2).
//!
//! §12.2: the destruction of an owned `Buf` and of a value that holds one needs `Alloc` (a function with no
//! `uses {Alloc}` gets E0601, §8.1; an `rt fn` gets E0901, §10 rule 1), and the destruction on the way out by
//! a `panic` does not (§9.2: there is no unwinding). So an owned local that is alive where a path reaches
//! the end of its block is dropped there, once for each block that ends. A local that is moved on every path
//! that reaches the end is not dropped, and nor is one that is alive only on a path a `panic` ends, or in
//! front of a `while true` with no `break` that never ends (§7, S-873).
//!
//! The model counts it by the paths. It runs a body over a set of states (the set of the owned locals that
//! may be alive on a path that arrives), block by block: a branch of an `if` (an `else if` chain, with or
//! without the last `else`), an arm of a `match` (the heading is a Copy value, a borrow, or an owned value
//! whose binding the arm owns), the right operand of `&&` and `||` (§3.5: it is skipped when the left one
//! decides, so the way past it is a path too), the body of a `while c` and of a `for _ in 0 ..< n` (which
//! may run no time, and runs again from the states it ended with), and the end of the body of the function.
//! A local that is alive on some path that reaches the end of its block is dropped there, and the function
//! needs `Alloc` for the first one of them in the order of the declarations (the parameters in the order
//! written, then the locals in the order of the text). The test writes the same body as a `fn` (E0601), as an
//! `rt fn` with the parameters in the other order (E0901), and as a method with `move self`, and compares
//! the code and the local the diagnostic names with the model's.
//!
//! The values are `Buf[F32]`, `Option[Buf[F32]]` and a struct that holds a `Buf`. Not generated: an early
//! exit (`return`, `?`, `continue`: no drop is counted at them until U3 puts the drop points there, W6-02
//! U3), and the pattern of a `for` that binds an owned value and a guard (U2b), a value with no name,
//! an overwrite, `_`, a Dup value, a type parameter `T` and an anonymous function (the later units).
//! The `break` of a `while true` (the loop that only a `break` leaves, S-1042: no path leaves it by its
//! condition) is generated only when `WHILE_TRUE_BREAK` is true.
//!
//! The bodies come from a fixed seed (`Rng`), many in each of a few packages, kept in memory
//! (`check_input`, no file written: `rules/common.md` 3.7). A function that gets a diagnostic other than
//! E0601 and E0901 is a fault of the generator (counted and left out). A failure shows the seed, the text of
//! the function, the answer of the model and the diagnostics.

use std::collections::BTreeSet;

use onsa_driver::PackageInput;

use crate::test_support::doc_of;
use crate::test_support::sweep::{Rng, check_input_out};

/// Whether the generator writes a `while true` that is left by a `break` (S-1042, the loop's only way out
/// is the `break`). It is false until U3: the drop points of the early exits are not in yet, and the check
/// counts a path where the condition is false after such a loop. **U3 sets it to true.** The model then
/// also counts the owned locals of the body that are alive at the `break` (the drop of the early exit).
const WHILE_TRUE_BREAK: bool = false;

const SEED: u64 = 0x2a02_0602;
/// The packages (each from the seed plus its number) and the bodies of each.
const CHUNKS: usize = 12;
const TREES: usize = 30;
/// What the compared functions must show, so that a sweep that checks nothing does not pass.
const MIN_FUNCTIONS: usize = 700;

/// The statements of a function (each block has one to four, so that the nesting would multiply them).
const BUDGET: usize = 12;

const HEAD: &str =
    "pub struct Holder { buf: Buf[F32], n: U32 }\n\npub rt fn pass(move b: Buf[F32]) -> Buf[F32] { b }\n";

// ---------------------------------------------------------------------------------------------- the tree

type Id = usize;
/// The owned locals that may be alive on one path, one bit for each.
type St = u128;
type Sts = BTreeSet<St>;

fn bit(i: Id) -> St {
    1u128 << i
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Buf,
    Opt,
    Holder,
    /// A `Bool` local (not owned).
    Flag,
}

struct Local {
    prefix: char,
    kind: Kind,
    is_var: bool,
}

/// The consuming expression of a binding.
#[derive(Clone)]
enum Src {
    /// `pass(move b)`
    Pass(Id),
    /// `Holder { buf: pass(move b), n: 0 }`
    Hold(Id),
    /// `Some(move b)`
    Wrap(Id),
    /// `pass(move h.buf)`: takes the field out and consumes `h` (§5.2).
    Take(Id),
}

impl Src {
    fn id(&self) -> Id {
        match self {
            Src::Pass(i) | Src::Hold(i) | Src::Wrap(i) | Src::Take(i) => *i,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Loop {
    /// `while c { .. }`
    While,
    /// `for _ in 0 ..< n { .. }`
    For,
    /// `while true { .. }` with no `break`: it never ends (§7).
    Spin,
    /// `while true { .. ; break }`: left by the `break` only (S-1042).
    SpinBreak,
}

#[derive(Clone)]
enum Node {
    Let(Id, Src),
    Var(Id, Src),
    Assign(Id, Src),
    /// The branches `if c { } else if d { } ..`, then the last `else` (if any).
    If(Vec<Block>, Option<Block>),
    /// `match n { 0 => .., 1 => .., _ => .. }`
    MatchN(Vec<Block>),
    /// `match q0 { Some(_) => .., None => .. }`: the heading is a borrow.
    MatchQ(Block, Block),
    /// `match move o { Some(v) => .., None => .. }`: the arm owns `v`.
    MatchO(Id, Id, Block, Block),
    /// `match move b { t => .. }`
    MatchB(Id, Id, Block),
    /// `let g = c && ({ .. })` (`true`: `&&`, else `||`): the block is the right operand.
    Logic(bool, Id, Block),
    Loop(Loop, Block),
    Panic,
    Break,
    // Values.
    SomeOf(Id),
    SomeField(Id),
    MoveOf(Id),
    NoneV,
    True,
    Group(Block),
}

#[derive(Clone, Default)]
struct Block {
    stmts: Vec<Node>,
    tail: Option<Box<Node>>,
}

struct Func {
    locals: Vec<Local>,
    /// The parameters (owned ones) in the order written for the `fn`.
    params: Vec<Id>,
    body: Block,
}

impl Func {
    fn owned_mask(&self) -> St {
        let mut m = 0;
        for (i, l) in self.locals.iter().enumerate() {
            if l.kind != Kind::Flag {
                m |= bit(i);
            }
        }
        m
    }
}

fn blocks_of(n: &Node) -> Vec<&Block> {
    match n {
        Node::If(bs, e) => bs.iter().chain(e.iter()).collect(),
        Node::MatchN(bs) => bs.iter().collect(),
        Node::MatchQ(a, b) | Node::MatchO(_, _, a, b) => vec![a, b],
        Node::MatchB(_, _, b) | Node::Logic(_, _, b) | Node::Loop(_, b) | Node::Group(b) => vec![b],
        _ => Vec::new(),
    }
}

/// The name of the form of a node, for the tally of the forms generated.
fn tag(n: &Node) -> &'static str {
    match n {
        Node::Let(_, Src::Take(_)) => "take",
        Node::Let(_, Src::Hold(_)) => "struct",
        Node::Let(_, Src::Wrap(_)) => "some",
        Node::Let(..) => "let",
        Node::Var(..) => "var",
        Node::Assign(..) => "assign",
        Node::If(bs, Some(_)) if bs.len() > 1 => "else-if",
        Node::If(bs, None) if bs.len() > 1 => "else-if-open",
        Node::If(_, Some(_)) => "if-else",
        Node::If(_, None) => "if-open",
        Node::MatchN(_) => "match-copy",
        Node::MatchQ(..) => "match-borrow",
        Node::MatchO(..) => "match-move",
        Node::MatchB(..) => "match-bind",
        Node::Logic(true, ..) => "and",
        Node::Logic(false, ..) => "or",
        Node::Loop(Loop::While, _) => "while",
        Node::Loop(Loop::For, _) => "for",
        Node::Loop(Loop::Spin, _) => "spin",
        Node::Loop(Loop::SpinBreak, _) => "spin-break",
        Node::Panic => "panic",
        Node::Break => "break",
        Node::SomeField(_) => "move-field",
        Node::MoveOf(_) => "move-value",
        Node::Group(_) => "group",
        _ => "leaf",
    }
}

fn walk(b: &Block, f: &mut dyn FnMut(&Node)) {
    for n in b.stmts.iter().chain(b.tail.iter().map(|t| &**t)) {
        f(n);
        for sub in blocks_of(n) {
            walk(sub, f);
        }
    }
}

// ---------------------------------------------------------------------------------------------- the model

struct Flow {
    /// The states that reach the end of the node.
    n: Sts,
    /// The states at a `break` that leaves the loop around.
    b: Sts,
}

impl Flow {
    fn normal(n: Sts) -> Flow {
        Flow { n, b: Sts::new() }
    }
    fn none() -> Flow {
        Flow { n: Sts::new(), b: Sts::new() }
    }
}

/// The paths: R-32 (an owned local that is alive on a path that reaches the end of its block is dropped
/// there), S-873 (a `panic` and a `while true` with no `break` end the path, no state goes on),
/// §3.5 (the right operand of `&&` and `||` is a path or it is not), S-1042 (a `while true` with a `break`
/// is left by the `break` only).
struct Model {
    owned: St,
    /// The locals dropped at the end of their block on some path that reaches it.
    flagged: St,
    /// A local was moved where it was not alive on every path (a fault of the generator).
    invalid: bool,
    /// For each loop around: the locals declared in it.
    loops: Vec<St>,
}

impl Model {
    fn new(f: &Func) -> Model {
        Model { owned: f.owned_mask(), flagged: 0, invalid: false, loops: Vec::new() }
    }

    fn take(&mut self, s: &Src, st: St) -> St {
        if st & bit(s.id()) == 0 {
            self.invalid = true;
        }
        st & !bit(s.id())
    }

    fn declare(&mut self, id: Id, declared: &mut St) {
        *declared |= bit(id);
        if let Some(top) = self.loops.last_mut() {
            *top |= bit(id);
        }
    }

    /// Run the body of a function from the state that holds all its owned parameters.
    fn run(&mut self, f: &Func) {
        let mut start = 0;
        for &p in &f.params {
            start |= bit(p);
        }
        self.block(&f.body, &Sts::from([start]), &f.params);
    }

    fn block(&mut self, blk: &Block, states: &Sts, extra: &[Id]) -> Flow {
        let mut declared: St = 0;
        for &e in extra {
            self.declare(e, &mut declared);
        }
        let mut cur = states.clone();
        let mut brk = Sts::new();
        for n in blk.stmts.iter().chain(blk.tail.iter().map(|t| &**t)) {
            if cur.is_empty() {
                break;
            }
            let f = self.node(n, &cur, &mut declared);
            brk.extend(f.b);
            cur = f.n;
        }
        for &st in &cur {
            self.flagged |= st & declared & self.owned;
        }
        Flow { n: cur.iter().map(|st| st & !declared).collect(), b: brk.iter().map(|st| st & !declared).collect() }
    }

    fn branches<'a>(&mut self, blks: impl Iterator<Item = &'a Block>, cur: &Sts) -> Flow {
        let mut out = Flow::none();
        for blk in blks {
            let f = self.block(blk, cur, &[]);
            out.n.extend(f.n);
            out.b.extend(f.b);
        }
        out
    }

    fn node(&mut self, n: &Node, cur: &Sts, declared: &mut St) -> Flow {
        match n {
            Node::Let(l, s) | Node::Var(l, s) => {
                let out = cur.iter().map(|&st| self.take(s, st) | bit(*l)).collect();
                self.declare(*l, declared);
                Flow::normal(out)
            }
            Node::Assign(l, s) => {
                let mut out = Sts::new();
                for &st in cur {
                    if st & bit(*l) != 0 {
                        // The overwrite of an alive value drops it: not in the model (a later unit).
                        self.invalid = true;
                    }
                    out.insert(self.take(s, st) | bit(*l));
                }
                Flow::normal(out)
            }
            Node::Panic => Flow::none(),
            Node::Break => {
                // The drop of the early exit: the locals of the loop's body alive at the `break`.
                let top = self.loops.last().copied().unwrap_or(0);
                for &st in cur {
                    self.flagged |= st & top & self.owned;
                }
                Flow { n: Sts::new(), b: cur.clone() }
            }
            Node::If(bs, e) => {
                let mut f = self.branches(bs.iter().chain(e.iter()), cur);
                if e.is_none() {
                    f.n.extend(cur.iter().copied());
                }
                f
            }
            Node::MatchN(bs) => self.branches(bs.iter(), cur),
            Node::MatchQ(a, b) => self.branches([a, b].into_iter(), cur),
            Node::MatchO(o, v, some, none) => {
                let mut after = Sts::new();
                for &st in cur {
                    after.insert(self.take(&Src::Pass(*o), st));
                }
                let with_v: Sts = after.iter().map(|st| st | bit(*v)).collect();
                let a = self.block(some, &with_v, &[*v]);
                let b = self.block(none, &after, &[]);
                Flow { n: a.n.into_iter().chain(b.n).collect(), b: a.b.into_iter().chain(b.b).collect() }
            }
            Node::MatchB(b, t, arm) => {
                let with_t: Sts = cur.iter().map(|&st| self.take(&Src::Pass(*b), st) | bit(*t)).collect();
                self.block(arm, &with_t, &[*t])
            }
            Node::Logic(_, g, rhs) => {
                self.declare(*g, declared);
                let mut f = self.block(rhs, cur, &[]);
                // The right operand may not run: the states as they were are a path past it.
                f.n.extend(cur.iter().copied());
                f
            }
            Node::Loop(kind, body) => {
                self.loops.push(0);
                // The state at the head: the states the loop is entered with, and the ones the body ends with.
                let mut heads = cur.clone();
                let mut leave = Sts::new();
                loop {
                    let f = self.block(body, &heads, &[]);
                    leave.extend(f.b);
                    let mut next = heads.clone();
                    next.extend(f.n);
                    if next == heads {
                        break;
                    }
                    heads = next;
                }
                self.loops.pop();
                Flow::normal(match kind {
                    Loop::While | Loop::For => heads,
                    Loop::Spin => Sts::new(),
                    Loop::SpinBreak => leave,
                })
            }
            Node::SomeOf(i) | Node::SomeField(i) | Node::MoveOf(i) => {
                Flow::normal(cur.iter().map(|&st| self.take(&Src::Pass(*i), st)).collect())
            }
            Node::NoneV | Node::True => Flow::normal(cur.clone()),
            Node::Group(b) => self.block(b, cur, &[]),
        }
    }
}

/// The first of the flagged locals in the order of the declarations: `order` lists the parameters, then the
/// others are in the order of their ids (the text).
fn first_flagged(f: &Func, flagged: St, order: &[Id]) -> Option<Id> {
    order.iter().copied().chain(0..f.locals.len()).find(|&i| flagged & bit(i) != 0)
}

// ------------------------------------------------------------------------------------------- the generator

struct Gen<'r> {
    rng: &'r mut Rng,
    f: Func,
    depth: usize,
    /// The names in scope, for an assignment to a `var`.
    vis: Vec<Id>,
    /// The first id a body may move (the locals of the loop around: it runs again, §5.2).
    floor: Vec<Id>,
    /// How many statements are still to be written in the function (the nesting multiplies them).
    budget: usize,
}

fn live_all(states: &Sts) -> St {
    states.iter().fold(!0u128, |a, &s| a & s)
}

impl Gen<'_> {
    fn fresh(&mut self, prefix: char, kind: Kind, is_var: bool) -> Id {
        self.f.locals.push(Local { prefix, kind, is_var });
        self.f.locals.len() - 1
    }

    fn room(&self) -> bool {
        self.f.locals.len() < 100
    }

    fn movable(&self, states: &Sts, kind: Kind) -> Vec<Id> {
        let live = live_all(states);
        let floor = self.floor.last().copied().unwrap_or(0);
        (floor..self.f.locals.len()).filter(|&i| live & bit(i) != 0 && self.f.locals[i].kind == kind).collect()
    }

    fn scratch(&self, n: &Node, cur: &Sts) -> Flow {
        let mut m = Model::new(&self.f);
        m.node(n, cur, &mut 0)
    }

    fn completes(&self, b: &Block, cur: &Sts, extra: &[Id]) -> bool {
        let mut m = Model::new(&self.f);
        !m.block(b, cur, extra).n.is_empty()
    }

    fn block(&mut self, states: &Sts, d: usize, value: bool, extra: &[Id]) -> Block {
        let mark = self.vis.len();
        self.vis.extend(extra.iter().copied());
        let n = if d < self.depth { self.rng.range(1, 4) } else { self.rng.range(0, 2) };
        let n = if self.budget == 0 { 0 } else { n };
        let mut stmts = Vec::new();
        let mut cur = states.clone();
        for _ in 0..n {
            if cur.is_empty() {
                break;
            }
            self.budget = self.budget.saturating_sub(1);
            let Some(node) = self.stmt(&cur, d, value) else { continue };
            let flow = self.scratch(&node, &cur);
            if let Node::Let(i, _) | Node::Var(i, _) | Node::Logic(_, i, _) = &node {
                self.vis.push(*i);
            }
            stmts.push(node);
            cur = flow.n;
        }
        let tail = (value && !cur.is_empty()).then(|| Box::new(self.val(&cur, d)));
        self.vis.truncate(mark);
        Block { stmts, tail }
    }

    fn sub(&mut self, states: &Sts, d: usize, value: bool) -> Block {
        self.block(states, d + 1, value, &[])
    }

    fn stmt(&mut self, cur: &Sts, d: usize, value: bool) -> Option<Node> {
        let bl = self.movable(cur, Kind::Buf);
        let hl = self.movable(cur, Kind::Holder);
        let ol = self.movable(cur, Kind::Opt);
        let mut c = self.rng.below(100);
        // Nothing consumes an owned local in a block that carries no value (only a `panic` or a loop that
        // never ends does not drop it), so such a block makes fewer of them.
        if !value && c < 52 && self.rng.chance(60) {
            c = 52 + self.rng.below(48);
        }
        if !self.room() {
            return None;
        }
        // A `var` that was moved gets a whole new value (§5.2); a `var` that is alive is moved on.
        let live = live_all(cur);
        let floor = self.floor.last().copied().unwrap_or(0);
        let dead: Vec<Id> = self
            .vis
            .iter()
            .copied()
            .filter(|&i| {
                self.f.locals[i].is_var && i >= floor && live & bit(i) == 0 && cur.iter().all(|s| s & bit(i) == 0)
            })
            .collect();
        if !dead.is_empty() && !bl.is_empty() && self.rng.chance(50) {
            return Some(Node::Assign(*self.rng.pick(&dead), Src::Pass(*self.rng.pick(&bl))));
        }
        let vars: Vec<Id> = bl.iter().copied().filter(|&i| self.f.locals[i].is_var).collect();
        if !vars.is_empty() && self.rng.chance(25) {
            let s = Src::Pass(*self.rng.pick(&vars));
            return Some(Node::Let(self.fresh('t', Kind::Buf, false), s));
        }
        if c < 30 && !bl.is_empty() {
            let s = Src::Pass(*self.rng.pick(&bl));
            return Some(Node::Let(self.fresh('t', Kind::Buf, false), s));
        }
        if c < 35 && !bl.is_empty() {
            let s = Src::Hold(*self.rng.pick(&bl));
            return Some(Node::Let(self.fresh('h', Kind::Holder, false), s));
        }
        if c < 39 && !bl.is_empty() {
            let s = Src::Wrap(*self.rng.pick(&bl));
            return Some(Node::Let(self.fresh('o', Kind::Opt, false), s));
        }
        if c < 43 && !hl.is_empty() {
            let s = Src::Take(*self.rng.pick(&hl));
            return Some(Node::Let(self.fresh('t', Kind::Buf, false), s));
        }
        if c < 48 && !bl.is_empty() {
            let s = Src::Pass(*self.rng.pick(&bl));
            return Some(Node::Var(self.fresh('w', Kind::Buf, true), s));
        }
        if d >= self.depth {
            return None;
        }
        if c < 64 {
            let extra = self.rng.below(3);
            let mut branches = vec![self.sub(cur, d, false)];
            for _ in 0..extra {
                branches.push(self.sub(cur, d, false));
            }
            let els = if self.rng.chance(55) { Some(self.sub(cur, d, false)) } else { None };
            return Some(Node::If(branches, els));
        }
        if c < 69 {
            return Some(Node::MatchN((0..3).map(|_| self.sub(cur, d, false)).collect()));
        }
        if c < 73 {
            return Some(Node::MatchQ(self.sub(cur, d, false), self.sub(cur, d, false)));
        }
        if c < 78 && !ol.is_empty() {
            let o = *self.rng.pick(&ol);
            let v = self.fresh('v', Kind::Buf, false);
            let after: Sts = cur.iter().map(|st| st & !bit(o)).collect();
            let with_v: Sts = after.iter().map(|st| st | bit(v)).collect();
            let some = self.block(&with_v, d + 1, false, &[v]);
            let none = self.sub(&after, d, false);
            return Some(Node::MatchO(o, v, some, none));
        }
        if c < 81 && !bl.is_empty() {
            let b = *self.rng.pick(&bl);
            let t = self.fresh('v', Kind::Buf, false);
            let with_t: Sts = cur.iter().map(|st| (st & !bit(b)) | bit(t)).collect();
            let arm = self.block(&with_t, d + 1, false, &[t]);
            return Some(Node::MatchB(b, t, arm));
        }
        if c < 87 && !bl.is_empty() {
            let and = self.rng.chance(50);
            let g = self.fresh('g', Kind::Flag, false);
            let mut rhs = self.sub(cur, d, false);
            if self.completes(&rhs, cur, &[]) {
                rhs.tail = Some(Box::new(Node::True));
            }
            return Some(Node::Logic(and, g, rhs));
        }
        if c < 93 {
            return Some(self.looped(cur, d));
        }
        if c < 96 {
            return Some(Node::Panic);
        }
        None
    }

    fn looped(&mut self, cur: &Sts, d: usize) -> Node {
        let pick = self.rng.below(100);
        let spin_break = WHILE_TRUE_BREAK && pick < 30;
        if spin_break {
            // The body runs once (it ends with the `break`), so it may move what the function owns.
            let mut body = self.sub(cur, d, false);
            if self.completes(&body, cur, &[]) {
                body.stmts.push(Node::Break);
                return Node::Loop(Loop::SpinBreak, body);
            }
            return Node::Loop(Loop::Spin, body);
        }
        let kind = match pick {
            0..=44 => Loop::While,
            45..=79 => Loop::For,
            _ => Loop::Spin,
        };
        self.floor.push(self.f.locals.len());
        let body = self.sub(cur, d, false);
        self.floor.pop();
        Node::Loop(kind, body)
    }

    fn val(&mut self, cur: &Sts, d: usize) -> Node {
        let bl = self.movable(cur, Kind::Buf);
        let hl = self.movable(cur, Kind::Holder);
        let ol = self.movable(cur, Kind::Opt);
        let c = self.rng.below(100);
        if d < self.depth && c < 45 && self.room() && self.budget > 0 {
            let mut kinds = vec![0, 1, 2, 4];
            if !ol.is_empty() {
                kinds.push(3);
            }
            if !bl.is_empty() {
                kinds.push(5);
            }
            match *self.rng.pick(&kinds) {
                0 => {
                    let extra = self.rng.below(3);
                    let mut branches = vec![self.sub(cur, d, true)];
                    for _ in 0..extra {
                        branches.push(self.sub(cur, d, true));
                    }
                    let els = self.sub(cur, d, true);
                    return Node::If(branches, Some(els));
                }
                1 => return Node::MatchN((0..3).map(|_| self.sub(cur, d, true)).collect()),
                2 => return Node::MatchQ(self.sub(cur, d, true), self.sub(cur, d, true)),
                3 => {
                    let o = *self.rng.pick(&ol);
                    let v = self.fresh('v', Kind::Buf, false);
                    let after: Sts = cur.iter().map(|st| st & !bit(o)).collect();
                    let with_v: Sts = after.iter().map(|st| st | bit(v)).collect();
                    let some = self.block(&with_v, d + 1, true, &[v]);
                    let none = self.sub(&after, d, true);
                    return Node::MatchO(o, v, some, none);
                }
                5 => {
                    let b = *self.rng.pick(&bl);
                    let t = self.fresh('v', Kind::Buf, false);
                    let with_t: Sts = cur.iter().map(|st| (st & !bit(b)) | bit(t)).collect();
                    let arm = self.block(&with_t, d + 1, true, &[t]);
                    return Node::MatchB(b, t, arm);
                }
                _ => return Node::Group(self.sub(cur, d, true)),
            }
        }
        if c < 55 {
            return Node::Panic;
        }
        let mut opts = vec![Node::NoneV, Node::NoneV];
        for &b in &bl {
            opts.push(Node::SomeOf(b));
            opts.push(Node::SomeOf(b));
        }
        for &h in &hl {
            opts.extend([Node::SomeField(h), Node::SomeField(h), Node::SomeField(h)]);
        }
        for &o in &ol {
            opts.extend([Node::MoveOf(o), Node::MoveOf(o), Node::MoveOf(o)]);
        }
        opts[self.rng.below(opts.len())].clone()
    }
}

/// A function body over owned parameters.
fn gen_func(rng: &mut Rng) -> Func {
    let depth = *rng.pick(&[2, 3, 4, 5]);
    let mut g = Gen {
        rng,
        f: Func { locals: Vec::new(), params: Vec::new(), body: Block::default() },
        depth,
        vis: Vec::new(),
        floor: Vec::new(),
        budget: BUDGET,
    };
    // A body with one owned parameter can move it on every path (a value cannot be split in two).
    let single = g.rng.chance(40);
    let nb = if single { 1 } else { *g.rng.pick(&[1, 2, 2, 3]) };
    let mut params: Vec<Id> = (0..nb).map(|_| g.fresh('a', Kind::Buf, false)).collect();
    if !single && g.rng.chance(35) {
        params.push(g.fresh('p', Kind::Opt, false));
    }
    if !single && g.rng.chance(30) {
        params.push(g.fresh('q', Kind::Holder, false));
    }
    g.rng.shuffle(&mut params);
    let start: St = params.iter().fold(0, |a, &p| a | bit(p));
    let body = g.block(&Sts::from([start]), 0, true, &params);
    let mut f = g.f;
    f.params = params;
    f.body = body;
    f
}

// -------------------------------------------------------------------------------------------- the text

struct Writer<'a> {
    f: &'a Func,
    /// The parameter that is `self` (a method).
    self_id: Option<Id>,
}

fn indent(s: &str) -> String {
    s.lines().map(|l| if l.is_empty() { String::new() } else { format!("  {l}") }).collect::<Vec<_>>().join("\n")
}

impl Writer<'_> {
    fn name(&self, i: Id) -> String {
        if Some(i) == self.self_id { "self".to_string() } else { format!("{}{}", self.f.locals[i].prefix, i) }
    }

    fn src(&self, s: &Src) -> String {
        match s {
            Src::Pass(i) => format!("pass(move {})", self.name(*i)),
            Src::Hold(i) => format!("Holder {{ buf: pass(move {}), n: 0 }}", self.name(*i)),
            Src::Wrap(i) => format!("Some(move {})", self.name(*i)),
            Src::Take(i) => format!("pass(move {}.buf)", self.name(*i)),
        }
    }

    fn block(&self, b: &Block) -> String {
        let mut lines: Vec<String> = b.stmts.iter().map(|s| self.node(s)).collect();
        if let Some(t) = &b.tail {
            lines.push(self.node(t));
        }
        if lines.is_empty() {
            return "{\n}".to_string();
        }
        format!("{{\n{}\n}}", indent(&lines.join("\n")))
    }

    fn arms(&self, arms: &[String]) -> String {
        format!("{{\n{}\n}}", indent(&arms.join(",\n")))
    }

    fn node(&self, n: &Node) -> String {
        match n {
            Node::Let(l, s) => format!("let {} = {}", self.name(*l), self.src(s)),
            Node::Var(l, s) => format!("var {} = {}", self.name(*l), self.src(s)),
            Node::Assign(l, s) => format!("{} = {}", self.name(*l), self.src(s)),
            Node::If(bs, e) => {
                let conds = ["c", "d", "c"];
                let mut t = String::new();
                for (k, b) in bs.iter().enumerate() {
                    t += &format!("{} {} {}", if k == 0 { "if" } else { " else if" }, conds[k % 3], self.block(b));
                }
                if let Some(e) = e {
                    t += &format!(" else {}", self.block(e));
                }
                t
            }
            Node::MatchN(bs) => {
                let pats = ["0", "1", "_"];
                let arms: Vec<String> = bs.iter().zip(pats).map(|(b, p)| format!("{p} => {}", self.block(b))).collect();
                format!("match n {}", self.arms(&arms))
            }
            Node::MatchQ(a, b) => {
                format!(
                    "match q0 {}",
                    self.arms(&[format!("Some(_) => {}", self.block(a)), format!("None => {}", self.block(b))])
                )
            }
            Node::MatchO(o, v, a, b) => format!(
                "match move {} {}",
                self.name(*o),
                self.arms(&[
                    format!("Some({}) => {}", self.name(*v), self.block(a)),
                    format!("None => {}", self.block(b))
                ])
            ),
            Node::MatchB(b, t, arm) => {
                format!(
                    "match move {} {}",
                    self.name(*b),
                    self.arms(&[format!("{} => {}", self.name(*t), self.block(arm))])
                )
            }
            Node::Logic(and, g, rhs) => {
                format!("let {} = c {} ({})", self.name(*g), if *and { "&&" } else { "||" }, self.block(rhs))
            }
            Node::Loop(kind, b) => match kind {
                Loop::While => format!("while c {}", self.block(b)),
                Loop::For => format!("for _ in 0 ..< n {}", self.block(b)),
                Loop::Spin | Loop::SpinBreak => format!("while true {}", self.block(b)),
            },
            Node::Panic => "panic(\"x\")".to_string(),
            Node::Break => "break".to_string(),
            Node::SomeOf(i) => format!("Some(move {})", self.name(*i)),
            Node::SomeField(i) => format!("Some(move {}.buf)", self.name(*i)),
            Node::MoveOf(i) => format!("move {}", self.name(*i)),
            Node::NoneV => "None".to_string(),
            Node::True => "true".to_string(),
            Node::Group(b) => self.block(b),
        }
    }

    fn param(&self, i: Id) -> String {
        let ty = match self.f.locals[i].kind {
            Kind::Buf => "Buf[F32]",
            Kind::Opt => "Option[Buf[F32]]",
            _ => "Holder",
        };
        format!("move {}: {ty}", self.name(i))
    }

    fn header_tail(&self, order: &[Id]) -> String {
        let mut s = String::from("c: Bool, d: Bool, n: U32, q0: Option[Buf[F32]]");
        for &p in order {
            s += &format!(", {}", self.param(p));
        }
        s
    }
}

// ---------------------------------------------------------------------------------------------- the check

/// One function of a package, with the answer of the model.
struct Case {
    name: String,
    /// The line of the header (1-based).
    line: usize,
    /// True for an `rt fn` (E0901), false for a `fn` and a method (E0601).
    rt: bool,
    /// The local the diagnostic names, if the model says there is one.
    expect: Option<String>,
}

struct Package {
    text: String,
    cases: Vec<Case>,
}

fn build_package(
    rng: &mut Rng,
    tally: &mut std::collections::BTreeMap<&'static str, usize>,
    invalid: &mut usize,
) -> Package {
    let mut text = HEAD.to_string();
    let mut cases = Vec::new();
    let mut methods: Vec<(String, String, Option<String>)> = Vec::new();
    let mut k = 0;
    while k < TREES {
        let f = gen_func(rng);
        let mut m = Model::new(&f);
        m.run(&f);
        if m.invalid {
            *invalid += 1;
            continue;
        }
        walk(&f.body, &mut |n| *tally.entry(tag(n)).or_default() += 1);
        let w = Writer { f: &f, self_id: None };
        let name_of = |i: Option<Id>| i.map(|i| w.name(i));
        // The `fn`: the parameters in the order written.
        let order_fn = f.params.clone();
        let mut order_rt = f.params.clone();
        order_rt.reverse();
        for (rt, order) in [(false, &order_fn), (true, &order_rt)] {
            let nm = format!("{}{k}", if rt { "r" } else { "f" });
            text += "\n";
            let line = text.lines().count() + 1;
            text += &format!(
                "pub {}fn {nm}({}) -> Option[Buf[F32]] {}\n",
                if rt { "rt " } else { "" },
                w.header_tail(order),
                w.block(&f.body)
            );
            cases.push(Case { name: nm, line, rt, expect: name_of(first_flagged(&f, m.flagged, order)) });
        }
        if let Some(&q) = f.params.iter().find(|&&p| f.locals[p].kind == Kind::Holder) {
            let ws = Writer { f: &f, self_id: Some(q) };
            let mut order = vec![q];
            order.extend(f.params.iter().copied().filter(|&p| p != q));
            let others: Vec<Id> = order[1..].to_vec();
            let head = format!(
                "pub fn m{k}(move self, {}) -> Option[Buf[F32]] {}",
                ws.header_tail(&others),
                ws.block(&f.body)
            );
            let expect = first_flagged(&f, m.flagged, &order).map(|i| ws.name(i));
            methods.push((format!("m{k}"), head, expect));
        }
        k += 1;
    }
    if !methods.is_empty() {
        text += "\nimpl Holder {\n";
        for (name, head, expect) in methods {
            let at = text.lines().count() + 1;
            text += &format!("{}\n\n", indent(&head));
            cases.push(Case { name, line: at, rt: false, expect });
        }
        text += "}\n";
    }
    Package { text, cases }
}

/// What a function got: its diagnostics `(code, line, message-or-note)`.
struct Got {
    own: Vec<(String, String)>,
    other: Vec<(String, usize, String)>,
}

/// The name in the first backticks of a message.
fn first_quoted(s: &str) -> String {
    s.split('`').nth(1).unwrap_or("").to_string()
}

fn diagnostics_of(p: &Package, got: &mut [Got], strays: &mut Vec<String>) -> Result<(), String> {
    let out = check_input_out(&PackageInput::single_file("m.onsa", p.text.clone()));
    if out.code != 0 && out.code != 1 {
        return Err(format!("exit {}: {}", out.code, out.stderr));
    }
    let doc = doc_of(&out);
    for d in doc["diagnostics"].as_array().expect("diagnostics") {
        let code = d["code"].as_str().expect("a code").to_string();
        let line = d["span"]["line"].as_u64().expect("a line") as usize;
        let message = d["message"].as_str().expect("a message").to_string();
        let idx = if code == "E0601" {
            let f = first_quoted(&message);
            p.cases.iter().position(|c| c.name == f)
        } else {
            p.cases.iter().enumerate().filter(|(_, c)| c.line <= line).max_by_key(|(_, c)| c.line).map(|(i, _)| i)
        };
        let Some(i) = idx else {
            strays.push(format!("{code} at line {line}: {message}"));
            continue;
        };
        // E0309 (a binding never read, §5.1) is the last stage and is reported only where the unit has no other
        // error: most of the locals here are never read, and it comes up where nothing is dropped. It says
        // nothing about a drop.
        if code == "E0309" {
            continue;
        }
        let named = match code.as_str() {
            "E0601" => Some(first_quoted(d["notes"][0]["message"].as_str().unwrap_or(""))),
            "E0901" => Some(first_quoted(&message)),
            _ => None,
        };
        match named {
            Some(n) => got[i].own.push((code, n)),
            None => got[i].other.push((code, line, message)),
        }
    }
    Ok(())
}

fn slice_of(p: &Package, i: usize) -> String {
    let start = p.cases[i].line;
    let end = p.cases.iter().map(|c| c.line).filter(|&l| l > start).min().unwrap_or(usize::MAX);
    p.text
        .lines()
        .enumerate()
        .filter(|(n, _)| n + 1 >= start && n + 1 < end)
        .map(|(_, l)| l)
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn the_drop_at_the_end_of_a_block_follows_the_paths_the_model_counts() {
    onsa_diag::stack::run(run_sweep);
}

fn run_sweep() {
    let mut tally = std::collections::BTreeMap::new();
    let (mut invalid, mut functions, mut skipped, mut expect_flag, mut expect_clean) = (0, 0, 0, 0, 0);
    let mut failed: Vec<String> = Vec::new();
    let mut other_shown: Vec<String> = Vec::new();
    for chunk in 0..CHUNKS {
        let seed = SEED + chunk as u64;
        let mut rng = Rng::new(seed);
        let p = build_package(&mut rng, &mut tally, &mut invalid);
        let mut got: Vec<Got> = p.cases.iter().map(|_| Got { own: Vec::new(), other: Vec::new() }).collect();
        let mut strays = Vec::new();
        if let Err(e) = diagnostics_of(&p, &mut got, &mut strays) {
            failed.push(format!("seed {seed:#x}: the check did not end as a check does: {e}"));
            continue;
        }
        for s in strays {
            failed.push(format!("seed {seed:#x}: a diagnostic outside every function: {s}"));
        }
        for (i, c) in p.cases.iter().enumerate() {
            if !got[i].other.is_empty() {
                skipped += 1;
                if other_shown.len() < 3 {
                    other_shown.push(format!("seed {seed:#x}, {}: {:?}\n{}", c.name, got[i].other, slice_of(&p, i)));
                }
                continue;
            }
            functions += 1;
            if c.expect.is_some() {
                expect_flag += 1;
            } else {
                expect_clean += 1;
            }
            let want_code = if c.rt { "E0901" } else { "E0601" };
            let ok = match &c.expect {
                Some(n) => got[i].own.len() == 1 && got[i].own[0].0 == want_code && &got[i].own[0].1 == n,
                None => got[i].own.is_empty(),
            };
            if !ok {
                failed.push(format!(
                    "seed {seed:#x}, `{}` ({}): the model says {}, the check says {:?}\n{}",
                    c.name,
                    if c.rt { "rt fn" } else { "fn" },
                    c.expect.as_ref().map_or("no drop".to_string(), |n| format!("{want_code} naming `{n}`")),
                    got[i].own,
                    slice_of(&p, i)
                ));
            }
        }
    }
    eprintln!(
        "drop_path_model: {functions} functions compared, {skipped} left out for another diagnostic, {invalid} bodies out of the model; \
         the model says drop in {expect_flag}, none in {expect_clean}; forms {tally:?}"
    );
    let shown = failed.iter().take(5).cloned().collect::<Vec<_>>().join("\n\n");
    assert!(
        failed.is_empty(),
        "{} of {functions} functions differ from the model (the first 5; the seed makes the package again):\n{shown}",
        failed.len()
    );
    assert!(
        skipped == 0 && invalid == 0,
        "the generator made {skipped} functions with another diagnostic and {invalid} outside the model:\n{}",
        other_shown.join("\n")
    );
    assert!(functions >= MIN_FUNCTIONS, "only {functions} functions compared");
    assert!(
        expect_flag * 5 >= functions && expect_clean * 5 >= functions,
        "the answers are not mixed: drop {expect_flag}, none {expect_clean}"
    );
    let mut missing: Vec<&str> = [
        "let",
        "var",
        "assign",
        "take",
        "struct",
        "some",
        "if-else",
        "if-open",
        "else-if",
        "else-if-open",
        "match-copy",
        "match-borrow",
        "match-move",
        "match-bind",
        "and",
        "or",
        "while",
        "for",
        "spin",
        "panic",
        "move-field",
        "move-value",
        "group",
    ]
    .into_iter()
    .filter(|t| !tally.contains_key(t))
    .collect();
    if WHILE_TRUE_BREAK {
        missing.extend(["spin-break", "break"].into_iter().filter(|t| !tally.contains_key(t)));
    }
    assert!(missing.is_empty(), "forms never generated: {missing:?}");
}
