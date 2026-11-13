//! The hand-off of an owned `Str` (a `move` parameter) at a position that consumes it, against a model of the paths
//! (spec §5.2, §12.2, §8.1, §10 rule 1, §7, §3.5; S-1030 and R-255; W6-02 U4a/t).
//!
//! §5.2: an owned binding that is a Dup value (a `Str` is Shared, not Copy) and is put at a consuming position is moved
//! when it could carry a `move` as an Affine value would: nothing uses it afterwards (on any path that goes on, and
//! in the next iteration of a loop), no other argument of the call overlaps it, and the place is not held by a borrowed
//! `for` or a guard. Where it can not, a copy is handed over and the original is dropped at the end of its binding
//! (and at an early exit), and that drop needs `Alloc` (§12.2: a function with no `uses {Alloc}` gets E0601, §8.1; an `rt fn`
//! E0901, §10 rule 1); a value that is moved is not dropped ("所有する Dup の値を、消費する位置で移すこと: 要らない").
//!
//! The function has one parameter `move s: Str` and writes its bodies from a few statements, each on a line of its own,
//! with `acc` for the `U32` that every hand-off and read leaves: `Read` (`acc = acc + s.len()`), `Hand` (`acc = acc +
//! eat_n(s)`, an argument of a `move` parameter that gives back a `U32`, so that nothing else is dropped), `Ret` (`return
//! acc`, which leaves with `s` as it is), `RetHand` (`return acc + eat_n(s)`), `Break`, `Continue`, and `if`, `while c`,
//! `for _ in 0 ..< n` and `while true` (S-1042: the loop is left by its `break` only, and the body ends with `if d { break }`)
//! around blocks of them. The position of each `Hand` is the argument of a `move` parameter (R-255), so no other condition of §5.2
//! can fail here (no other argument, no derived binding, no guard).
//!
//! The model decides each `Hand` by the later use: it moves when no path that goes on from it reaches a `Read` or a `Hand`
//! (the next iteration of the loop it is in, and a `continue`, count), and then no path that has it moved drops `s`; it is
//! copied otherwise, and `s` stays alive. It runs the body over the set of states `{alive, moved}` of `s` (the loops to a
//! fixed point; the `while true` leaves by the `break`s only), and the function needs `Alloc` when `s` may be alive where
//! a `Ret` or the end of the body is reached. One diagnostic is expected there (E0601 in a `fn`, E0901 in an `rt fn`),
//! none otherwise. The model has no later use of the value that is handed off before the `eat_n` helper itself
//! (its own E0901 is reported at the head and left out).
//!
//! The test fails until the hand-off moves (U4a): today every hand-off is a copy, so a function that the model says is
//! clean (every path ends with `s` moved) gets a drop. The bodies come from a fixed seed (`Rng`), kept in memory
//! (`check_input_out`, no file written: `rules/common.md` 3.7). A function that gets a diagnostic other than E0601, E0901
//! and E0309 (a binding that is never read, which says nothing of a drop) is a fault of the generator.

use onsa_driver::PackageInput;

use crate::test_support::doc_of;
use crate::test_support::sweep::{Rng, check_input_out};

const SEED: u64 = 0x2a04_0602;
/// The packages and the bodies of each package (the check of a package is the time).
const CHUNKS: usize = 14;
const TREES: usize = 36;
/// What the compared functions must show, so that a sweep that checks nothing does not pass.
const MIN_FUNCTIONS: usize = 800;
const HEAD: &str = "pub rt fn eat_n(move s: Str) -> U32 { s.len() }\n";

#[derive(Clone)]
enum St {
    Read,
    /// The value is moved when nothing uses `s` after it (decided by `Model::mark`).
    Hand,
    Ret,
    RetHand,
    Break,
    Continue,
    If(Vec<St>, Vec<St>),
    While(Vec<St>),
    For(Vec<St>),
    Spin(Vec<St>),
}

fn diverges(b: &[St]) -> bool {
    b.iter().any(|s| match s {
        St::Ret | St::RetHand | St::Break | St::Continue => true,
        St::If(a, e) => diverges(a) && diverges(e),
        _ => false,
    })
}

struct Gen<'r> {
    rng: &'r mut Rng,
}

impl Gen<'_> {
    fn block(&mut self, depth: usize, in_loop: bool) -> Vec<St> {
        let mut out = Vec::new();
        for _ in 0..self.rng.range(1, 3) {
            let nested = depth < 3;
            let s = match self.rng.below(100) {
                0..=17 => St::Read,
                18..=39 => St::Hand,
                40..=54 if nested => {
                    let a = self.block(depth + 1, in_loop);
                    let e = if self.rng.chance(60) { self.block(depth + 1, in_loop) } else { Vec::new() };
                    St::If(a, e)
                }
                55..=60 if nested => St::While(self.block(depth + 1, true)),
                61..=65 if nested => St::For(self.block(depth + 1, true)),
                66..=70 if nested => {
                    let mut b = self.block(depth + 1, true);
                    while diverges(&b) {
                        b.pop();
                    }
                    // The loop is left by a `break` only: the body ends with the condition that leaves.
                    b.push(St::If(vec![St::Break], Vec::new()));
                    St::Spin(b)
                }
                71..=79 => St::Ret,
                80..=87 => St::RetHand,
                88..=93 if in_loop => St::Break,
                94..=99 if in_loop => St::Continue,
                _ => St::Read,
            };
            let stop = diverges(std::slice::from_ref(&s));
            out.push(s);
            if stop {
                break;
            }
        }
        out
    }
}

/// The set of the states of `s`: whether it may be alive, and whether it may be moved.
#[derive(Clone, Copy, PartialEq, Default, Debug)]
struct Set {
    alive: bool,
    moved: bool,
}

impl Set {
    fn join(self, o: Set) -> Set {
        Set { alive: self.alive || o.alive, moved: self.moved || o.moved }
    }
    fn none(self) -> bool {
        !self.alive && !self.moved
    }
}

struct Model {
    /// The `Hand`s in the order of the text: whether each one moves.
    moves: Vec<bool>,
    next: usize,
    /// True where `s` may be alive at a `Ret` or at the end of the body.
    drops: bool,
    at_break: Set,
    at_continue: Set,
}

/// The later use: whether a `Read` or a `Hand` may come after, on the paths that go on.
#[derive(Clone, Copy)]
struct Ctx {
    after: bool,
    at_break: bool,
    at_continue: bool,
}

impl Model {
    /// Whether a use is reachable from the start of the block (and, with `write`, which `Hand`s move: those with no use after).
    fn mark(&mut self, b: &[St], c: Ctx, write: bool, first: usize) -> bool {
        // The `Hand`s of a block are numbered from `first` in the order of the text, so the block is walked twice: the
        // count of the `Hand`s in each statement is needed to find the number of one from the end.
        let counts: Vec<usize> = b.iter().map(hands).collect();
        let mut k = c.after;
        let mut idx = first + counts.iter().sum::<usize>();
        for (s, n) in b.iter().zip(&counts).rev() {
            idx -= n;
            k = match s {
                St::Read => true,
                St::Hand => {
                    if write {
                        self.moves[idx] = !k;
                    }
                    true
                }
                St::Ret => false,
                St::RetHand => {
                    if write {
                        self.moves[idx] = true;
                    }
                    true
                }
                St::Break => c.at_break,
                St::Continue => c.at_continue,
                St::If(a, e) => {
                    let ka = self.mark(a, Ctx { after: k, ..c }, write, idx);
                    let ke = self.mark(e, Ctx { after: k, ..c }, write, idx + hands_of(a));
                    ka || ke
                }
                St::While(body) | St::For(body) => {
                    let head = self.loop_head(body, k, false);
                    self.mark(body, Ctx { after: head, at_break: k, at_continue: head }, write, idx);
                    head
                }
                St::Spin(body) => {
                    let head = self.loop_head(body, k, true);
                    self.mark(body, Ctx { after: head, at_break: k, at_continue: head }, write, idx);
                    head
                }
            };
        }
        k
    }

    /// Whether a use is reachable from the head of a loop: the fixed point of the body that flows back to it.
    fn loop_head(&mut self, body: &[St], after_loop: bool, spin: bool) -> bool {
        let mut head = if spin { false } else { after_loop };
        for _ in 0..3 {
            let inner = Ctx { after: head, at_break: after_loop, at_continue: head };
            let used = self.mark(body, inner, false, 0);
            head = if spin { used } else { after_loop || used };
        }
        head
    }

    fn run(&mut self, b: &[St], mut st: Set) -> Set {
        for s in b {
            st = match s {
                St::Read => st,
                St::Hand => {
                    let i = self.next;
                    self.next += 1;
                    if self.moves[i] { Set { alive: false, moved: !st.none() } } else { st }
                }
                St::Ret => {
                    self.drops |= st.alive;
                    Set::default()
                }
                St::RetHand => {
                    self.next += 1;
                    Set::default()
                }
                St::Break => {
                    self.at_break = self.at_break.join(st);
                    Set::default()
                }
                St::Continue => {
                    self.at_continue = self.at_continue.join(st);
                    Set::default()
                }
                St::If(a, e) => {
                    let sa = self.run(a, st);
                    let se = self.run(e, st);
                    sa.join(se)
                }
                St::While(body) | St::For(body) => self.run_loop(body, st, false),
                St::Spin(body) => self.run_loop(body, st, true),
            };
        }
        st
    }

    /// A loop to a fixed point. The `Hand`s of the body are numbered once: the walk of a round is rewound.
    fn run_loop(&mut self, body: &[St], input: Set, spin: bool) -> Set {
        let (saved_break, saved_continue) = (self.at_break, self.at_continue);
        let start = self.next;
        let mut head = input;
        loop {
            self.next = start;
            self.at_break = Set::default();
            self.at_continue = Set::default();
            let out = self.run(body, head);
            let again = head.join(out).join(self.at_continue);
            if again == head {
                break;
            }
            head = again;
        }
        let after = if spin { self.at_break } else { head.join(self.at_break) };
        self.at_break = saved_break;
        self.at_continue = saved_continue;
        after
    }
}

fn hands(s: &St) -> usize {
    match s {
        St::Hand | St::RetHand => 1,
        St::If(a, e) => hands_of(a) + hands_of(e),
        St::While(b) | St::For(b) | St::Spin(b) => hands_of(b),
        _ => 0,
    }
}

fn hands_of(b: &[St]) -> usize {
    b.iter().map(hands).sum()
}

fn write_block(b: &[St], pad: usize, out: &mut String) {
    let sp = " ".repeat(pad);
    for s in b {
        match s {
            St::Read => *out += &format!("{sp}acc = acc + s.len()\n"),
            St::Hand => *out += &format!("{sp}acc = acc + eat_n(s)\n"),
            St::Ret => *out += &format!("{sp}return acc\n"),
            St::RetHand => *out += &format!("{sp}return acc + eat_n(s)\n"),
            St::Break => *out += &format!("{sp}break\n"),
            St::Continue => *out += &format!("{sp}continue\n"),
            St::If(a, e) => {
                *out += &format!("{sp}if c {{\n");
                write_block(a, pad + 2, out);
                if e.is_empty() {
                    *out += &format!("{sp}}}\n");
                } else {
                    *out += &format!("{sp}}} else {{\n");
                    write_block(e, pad + 2, out);
                    *out += &format!("{sp}}}\n");
                }
            }
            St::While(body) => {
                *out += &format!("{sp}while d {{\n");
                write_block(body, pad + 2, out);
                *out += &format!("{sp}}}\n");
            }
            St::For(body) => {
                *out += &format!("{sp}for _ in 0 ..< n {{\n");
                write_block(body, pad + 2, out);
                *out += &format!("{sp}}}\n");
            }
            St::Spin(body) => {
                *out += &format!("{sp}while true {{\n");
                write_block(body, pad + 2, out);
                *out += &format!("{sp}}}\n");
            }
        }
    }
}

struct Case {
    name: String,
    line: usize,
    rt: bool,
    drops: bool,
    /// True where the model moves every `Hand`.
    all_move: bool,
    body: String,
}

fn build(rng: &mut Rng) -> (String, Vec<Case>) {
    let mut text = HEAD.to_string();
    let mut cases = Vec::new();
    for k in 0..TREES {
        let b = Gen { rng: &mut *rng }.block(0, false);
        let total = hands_of(&b);
        let mut m = Model {
            moves: vec![false; total],
            next: 0,
            drops: false,
            at_break: Set::default(),
            at_continue: Set::default(),
        };
        m.mark(&b, Ctx { after: false, at_break: false, at_continue: false }, true, 0);
        let end = m.run(&b, Set { alive: true, moved: false });
        // The end of the body is reached with `s` alive on some path: the tail `acc` leaves it as it is.
        let drops = m.drops || (!diverges(&b) && end.alive);
        let mut body = String::new();
        body += "  var acc: U32 = 0\n";
        write_block(&b, 2, &mut body);
        if !diverges(&b) {
            body += "  acc\n";
        }
        for rt in [false, true] {
            let name = format!("{}{k}", if rt { "r" } else { "f" });
            text += "\n";
            let line = text.lines().count() + 1;
            text += &format!(
                "pub {}fn {name}(move s: Str, c: Bool, d: Bool, n: U32) -> U32 {{\n{body}}}\n",
                if rt { "rt " } else { "" }
            );
            cases.push(Case { name, line, rt, drops, all_move: m.moves.iter().all(|&x| x), body: body.clone() });
        }
    }
    (text, cases)
}

/// The model's choice is the rule of an Affine value (§5.2: "その値が Affine であったとして、そこに `move` を置けるなら"): the
/// same bodies with a `Buf[F32]` and a `move` at every hand-off (which this version checks, §7) have an E0704 exactly where the
/// model copies a hand-off, and where it moves every one the drop is the model's. It passes today, and guards the model.
#[test]
fn the_model_moves_a_hand_off_where_the_affine_program_has_no_use_after_a_move() {
    onsa_diag::stack::run(|| {
        let (mut compared, mut with_use, mut without_use) = (0, 0, 0);
        let mut failed: Vec<String> = Vec::new();
        for chunk in 0..CHUNKS {
            let seed = SEED + chunk as u64;
            let (text, cases) = build(&mut Rng::new(seed));
            let text = text.replace("Str", "Buf[F32]").replace("eat_n(s)", "eat_n(move s)");
            let out = check_input_out(&PackageInput::single_file("m.onsa", text));
            assert!(out.code == 0 || out.code == 1, "seed {seed:#x}: exit {}: {}", out.code, out.stderr);
            let doc = doc_of(&out);
            let mut got: Vec<(bool, Vec<String>)> = vec![(false, Vec::new()); cases.len()];
            for d in doc["diagnostics"].as_array().expect("diagnostics") {
                let code = d["code"].as_str().expect("a code");
                let line = d["span"]["line"].as_u64().expect("a line") as usize;
                let message = d["message"].as_str().expect("a message");
                let i = if code == "E0601" {
                    let name = message.split('`').nth(1).unwrap_or("");
                    cases.iter().position(|c| c.name == name)
                } else {
                    cases.iter().enumerate().filter(|(_, c)| c.line <= line).max_by_key(|(_, c)| c.line).map(|(i, _)| i)
                };
                let Some(i) = i else { continue };
                match code {
                    "E0704" => got[i].0 = true,
                    "E0601" | "E0901" => got[i].1.push(code.to_string()),
                    _ => {}
                }
            }
            for (c, (use_after, drops)) in cases.iter().zip(&got) {
                compared += 1;
                if c.all_move {
                    without_use += 1;
                } else {
                    with_use += 1;
                }
                let want = if c.rt { "E0901" } else { "E0601" };
                // Where the Affine program has a use after a move, the drop is not compared (the check stops at the E0704).
                let ok = *use_after != c.all_move
                    && (*use_after || (drops.len() == usize::from(c.drops) && drops.iter().all(|d| d == want)));
                if !ok {
                    failed.push(format!(
                        "seed {seed:#x}, `{}`: the model moves {} (drop {}); the Affine program has a use after a move: {use_after}, drops {drops:?}\n{}",
                        c.name,
                        if c.all_move { "every hand-off" } else { "not every hand-off" },
                        c.drops,
                        c.body
                    ));
                }
            }
        }
        let shown = failed.iter().take(3).cloned().collect::<Vec<_>>().join("\n\n");
        assert!(failed.is_empty(), "{} of {compared} functions differ (the first 3):\n{shown}", failed.len());
        assert!(
            with_use * 6 >= compared && without_use * 6 >= compared,
            "not mixed: copy {with_use}, move {without_use}"
        );
    });
}

#[test]
fn the_hand_off_of_an_owned_str_follows_the_paths_the_model_counts() {
    onsa_diag::stack::run(run_sweep);
}

fn run_sweep() {
    let (mut functions, mut drops, mut clean, mut failed_clean, mut failed_drop) = (0, 0, 0, 0, 0);
    let mut failed: Vec<String> = Vec::new();
    let mut strays: Vec<String> = Vec::new();
    for chunk in 0..CHUNKS {
        let seed = SEED + chunk as u64;
        let mut rng = Rng::new(seed);
        let (text, cases) = build(&mut rng);
        let out = check_input_out(&PackageInput::single_file("m.onsa", text.clone()));
        assert!(out.code == 0 || out.code == 1, "seed {seed:#x}: exit {}: {}", out.code, out.stderr);
        let doc = doc_of(&out);
        let mut got: Vec<Vec<String>> = vec![Vec::new(); cases.len()];
        for d in doc["diagnostics"].as_array().expect("diagnostics") {
            let code = d["code"].as_str().expect("a code").to_string();
            let line = d["span"]["line"].as_u64().expect("a line") as usize;
            let message = d["message"].as_str().expect("a message").to_string();
            if code == "E0309" {
                continue;
            }
            let idx = if code == "E0601" {
                let name = message.split('`').nth(1).unwrap_or("");
                cases.iter().position(|c| c.name == name)
            } else {
                cases.iter().enumerate().filter(|(_, c)| c.line <= line).max_by_key(|(_, c)| c.line).map(|(i, _)| i)
            };
            match idx {
                Some(i) if code == "E0601" || code == "E0901" => got[i].push(code),
                Some(i) => strays.push(format!("seed {seed:#x}, `{}`: {code} {message}", cases[i].name)),
                // The helper at the head drops its own argument (an E0901 before the first function).
                None if code == "E0901" && line == 1 => {}
                None => strays.push(format!("seed {seed:#x}: {code} at line {line}: {message}")),
            }
        }
        for (c, g) in cases.iter().zip(&got) {
            functions += 1;
            if c.drops {
                drops += 1;
            } else {
                clean += 1;
            }
            let want = if c.rt { "E0901" } else { "E0601" };
            let ok = if c.drops { g.len() == 1 && g[0] == want } else { g.is_empty() };
            if !ok {
                if c.drops {
                    failed_drop += 1;
                } else {
                    failed_clean += 1;
                }
                failed.push(format!(
                    "seed {seed:#x}, `{}` ({}): the model says {}, the check says {g:?}\n{}",
                    c.name,
                    if c.rt { "rt fn" } else { "fn" },
                    if c.drops { want.to_string() } else { "no drop (every path ends with `s` moved)".to_string() },
                    c.body
                ));
            }
        }
    }
    eprintln!(
        "dup_release_model: {functions} functions compared; the model says drop in {drops}, none in {clean}; \
         {failed_clean} differ where it says none, {failed_drop} where it says drop"
    );
    assert!(strays.is_empty(), "the generator made functions with another diagnostic:\n{}", strays.join("\n"));
    let shown = failed.iter().take(3).cloned().collect::<Vec<_>>().join("\n\n");
    assert!(
        failed.is_empty(),
        "{} of {functions} functions differ from the model: {failed_clean} where the model says every path ends with `s` moved \
         (the hand-off is a copy today, R-255, S-1030), {failed_drop} where it says drop (the first 3; the seed makes the package \
         again):\n{shown}",
        failed.len()
    );
    assert!(functions >= MIN_FUNCTIONS, "only {functions} functions compared");
    assert!(drops * 6 >= functions && clean * 6 >= functions, "the answers are not mixed: drop {drops}, none {clean}");
}
