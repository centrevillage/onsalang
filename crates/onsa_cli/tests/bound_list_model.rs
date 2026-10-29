//! A drawn sweep of the lists of bounds of a type parameter against a model of the spec (§4.5, §18.1, S-711,
//! S-747; W4-05 U4b/i2, from the grid of the break side of U4b).
//!
//! The words are `Dup`, `Copy`, `Num`, `Float`, `Show`, `Add`, `Gone` and `I32`, each with and without `?`;
//! the lists of one to three words are drawn with a fixed seed, with the lists of an overlap before a
//! contradiction (`Copy + Copy + ?Dup`) always in. Each list is a function `u` of its own line, with two users:
//! `a`, which calls it with a `Buf[F32]` (Affine: it meets no word but `?Dup`), and `i`, which calls it with an
//! integer literal (an `I32`: it meets every word but `Float`). What the model takes from the spec:
//! - The names stage first (§18.1): a name not found (`Gone`, E0302), a type where a bound is written (`I32`,
//!   E0308) and a trait this version does not take as a bound (`Add`, E0200), the first by its place.
//! - Else the types stage, from the front (§4.5): the first word that is `?` on a bound not `Dup` (E0416,
//!   S-711), the same as one before it, or `?Dup` with one that requires `Dup` (`Dup`, `Copy`, `Num`,
//!   `Float`) before it (E0416, S-747). A word with an error of its own is not compared. The position is the
//!   name of the word.
//! - The users: a parameter whose list has a name not found or a contradiction anywhere is an unknown bound,
//!   with no diagnostic where it is used (§18.1, S-747 A5); an overlap alone is no such list. Else the call is
//!   the E0416 when the argument does not meet the list (the implicit `Dup` too, unless `?Dup`).
//!
//! Not in the model, so not drawn for it: the order of a `?` on a bound not `Dup` and an `Add` (S-711 says
//! only that the E0416 comes before the E0200 of the same word), and the users of a list with an `I32`, an
//! `Add` or a `?` on a bound not `Dup` (the spec does not say whether they are unknown).

mod test_support;

use std::collections::BTreeMap;

use test_support::sweep::{Rng, Texts, check_package, ended_well, package};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum W {
    Dup,
    Copy,
    Num,
    Float,
    Show,
    Add,
    Gone,
    I32,
}

const WORDS: [W; 8] = [W::Dup, W::Copy, W::Num, W::Float, W::Show, W::Add, W::Gone, W::I32];

/// A word and whether it has `?`.
type Word = (W, bool);

fn requires_dup(w: W) -> bool {
    matches!(w, W::Dup | W::Copy | W::Num | W::Float)
}

fn contradict(a: Word, b: Word) -> bool {
    (a == (W::Dup, true) && !b.1 && requires_dup(b.0)) || (b == (W::Dup, true) && !a.1 && requires_dup(a.0))
}

fn shown(list: &[Word]) -> String {
    let words: Vec<String> = list.iter().map(|&(w, r)| format!("{}{w:?}", if r { "?" } else { "" })).collect();
    words.join(" + ")
}

/// The diagnostic of the unit of the list: its code and the index of its word.
fn unit(list: &[Word]) -> Option<(&'static str, usize)> {
    let named = list.iter().position(|&(w, r)| matches!(w, W::Gone | W::I32) || (w == W::Add && !r));
    if let Some(i) = named {
        let code = match list[i].0 {
            W::Gone => "E0302",
            W::I32 => "E0308",
            _ => "E0200",
        };
        return Some((code, i));
    }
    let mut read: Vec<Word> = Vec::new();
    for (i, &x) in list.iter().enumerate() {
        if x.1 && x.0 != W::Dup || read.iter().any(|&y| y == x || contradict(y, x)) {
            return Some(("E0416", i));
        }
        read.push(x);
    }
    None
}

/// Whether the users of the list are out of the model (above).
fn unsure(list: &[Word]) -> bool {
    list.iter().any(|&(w, r)| matches!(w, W::I32 | W::Add) || r && w != W::Dup)
}

#[test]
fn a_list_of_bounds_is_judged_from_the_front_and_its_users_as_the_spec_says() {
    let tokens: Vec<Word> = WORDS.iter().flat_map(|&w| [(w, false), (w, true)]).collect();
    let mut lists: Vec<Vec<Word>> = Vec::new();
    for len in 1..=3u32 {
        for n in 0..tokens.len().pow(len) {
            let digits = (0..len).map(|k| n / tokens.len().pow(k) % tokens.len());
            lists.push(digits.map(|d| tokens[d]).collect());
        }
    }
    let mut r = Rng::new(0x0747_0405);
    r.shuffle(&mut lists);
    // 300 of all, and 200 more whose users the model judges (most lists of three have a word it does not).
    let rest = lists.split_off(300);
    lists.extend(rest.into_iter().filter(|l| !unsure(l)).take(200));
    for s in [[W::Copy, W::Copy], [W::Num, W::Num], [W::Dup, W::Dup]] {
        lists.push(vec![(s[0], false), (s[1], false), (W::Dup, true)]);
    }
    lists.push(vec![(W::Dup, true), (W::Dup, true), (W::Copy, false)]);
    // The open order of S-711 and E0200 (above).
    let open = |l: &Vec<Word>| l.contains(&(W::Add, false)) && l.iter().any(|&(w, r)| r && w != W::Dup);
    lists.retain(|l| !open(l));

    let mut text = String::new();
    for (k, l) in lists.iter().enumerate() {
        text.push_str(&format!("pub fn u{k}[T: {}](x: T) -> U32 {{ 0 }}\n", shown(l)));
        text.push_str(&format!("pub fn a{k}(b: Buf[F32]) -> U32 {{ u{k}(b) }}\n"));
        text.push_str(&format!("pub fn i{k}() -> U32 {{ u{k}(1) }}\n"));
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text);
    let d = package("bound_list_model", "demo", &texts);
    let checked = check_package(d.root());
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);
    let mut got: BTreeMap<u64, Vec<(u64, String)>> = BTreeMap::new();
    for x in &checked.diags {
        got.entry(x.line).or_default().push((x.col, x.code.clone()));
    }
    let at = |n: u64| got.get(&n).cloned().unwrap_or_default();
    let codes = |n: u64| at(n).into_iter().map(|x| x.1).collect::<Vec<_>>();

    let (mut bad, mut users, mut silenced) = (Vec::new(), 0, 0);
    for (k, l) in lists.iter().enumerate() {
        let line = 3 * k as u64 + 1;
        // The column of each word's name, after its `?`.
        let mut col = format!("pub fn u{k}[T: ").len() as u64 + 1;
        let mut cols = Vec::new();
        for &(w, r) in l {
            cols.push(col + r as u64);
            col += format!("{w:?}").len() as u64 + r as u64 + 3;
        }
        let want: Vec<(u64, String)> = unit(l).map(|(c, i)| (cols[i], c.to_string())).into_iter().collect();
        if at(line) != want {
            bad.push(format!("`{}`: {:?}, the model {want:?}", shown(l), at(line)));
        }
        if unsure(l) {
            continue;
        }
        users += 1;
        let contradiction = l.iter().enumerate().any(|(i, &x)| l[..i].iter().any(|&y| contradict(y, x)));
        let known = !l.iter().any(|&(w, _)| w == W::Gone) && !contradiction;
        silenced += !known as usize;
        let e = |b: bool| if b { vec!["E0416".to_string()] } else { Vec::new() };
        let affine = e(known && !l.iter().all(|&x| x == (W::Dup, true)));
        let literal = e(known && l.contains(&(W::Float, false)));
        if codes(line + 1) != affine || codes(line + 2) != literal {
            let (a, i) = (codes(line + 1), codes(line + 2));
            bad.push(format!("`{}` used: {a:?} and {i:?}, the model {affine:?} and {literal:?}", shown(l)));
        }
    }
    // The draw has both sides of the users' rule.
    assert!(users > 150 && silenced > 30 && users - silenced > 30, "{users} users, {silenced} unknown");
    assert!(bad.is_empty(), "{} mismatches:\n{}", bad.len(), bad.join("\n"));
}
