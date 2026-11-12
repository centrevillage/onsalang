//! The tree of the rows of a `match` (R-386): the arms that it passes by do
//! not change what the search answers. Matches of random arms of a fixed
//! seed are checked with the tree and with every row of a head (as before
//! it), and their diagnostics compared.

use crate::exhaust::WHOLE;
use crate::tests::check;

const HEAD: &str =
    "pub enum E { A, B(I32), C(Bool, I32) }\npub struct S {\n  a: Bool,\n  b: I32,\n}\npub const K: I32 = 1\n";

const TYPES: [&str; 6] =
    ["E", "S", "Option[(I32, Bool)]", "(E, I32, Bool)", "(Option[Bool], E, I32)", "(I32, I32, I32, I32)"];

/// A generator of a fixed seed (xorshift).
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }

    fn pick<'s>(&mut self, xs: &[&'s str]) -> &'s str {
        xs[self.below(xs.len())]
    }

    /// A pattern of the type `ty`: often one that names its heads, so that
    /// the tree passes rows by, and now and then `_`, a constant or a choice.
    fn pat(&mut self, ty: &str, depth: u32) -> String {
        match self.below(10) {
            0 => return "_".into(),
            1 if depth < 2 => return format!("{} | {}", self.pat(ty, depth + 1), self.pat(ty, depth + 1)),
            _ => {}
        }
        let d = depth + 1;
        match ty {
            "I32" => self.pick(&["0", "1", "2", "K"]).into(),
            "Bool" => self.pick(&["true", "false"]).into(),
            "E" => match self.below(3) {
                0 => "E.A".into(),
                1 => format!("E.B({})", self.pat("I32", d)),
                _ => format!("E.C({}, {})", self.pat("Bool", d), self.pat("I32", d)),
            },
            "S" => format!("S {{ a: {}, b: {} }}", self.pat("Bool", d), self.pat("I32", d)),
            "Option[(I32, Bool)]" if self.below(4) == 0 => "None".into(),
            "Option[(I32, Bool)]" => format!("Some({})", self.pat("(I32, Bool)", d)),
            "Option[Bool]" if self.below(3) == 0 => "None".into(),
            "Option[Bool]" => format!("Some({})", self.pat("Bool", d)),
            _ => {
                let inner = &ty[1..ty.len() - 1];
                let parts: Vec<String> = split(inner).into_iter().map(|t| self.pat(t, d)).collect();
                format!("({})", parts.join(", "))
            }
        }
    }
}

/// The element types of a tuple type, its parentheses taken off.
fn split(inner: &str) -> Vec<&str> {
    let (mut depth, mut start, mut parts) = (0, 0, Vec::new());
    for (i, c) in inner.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(inner[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(inner[start..].trim());
    parts
}

fn source(seed: u64, fns: usize) -> String {
    let mut rng = Rng(seed);
    let mut src = HEAD.to_string();
    for k in 0..fns {
        if k % 4 == 3 {
            src += &dense(&mut rng, k);
            continue;
        }
        let ty = rng.pick(&TYPES);
        src += &format!("pub fn f{k}(x: {ty}, c: Bool) -> I32 {{\n  match x {{\n");
        for _ in 0..2 + rng.below(12) {
            let guard = if rng.below(8) == 0 { " if c" } else { "" };
            src += &format!("    {}{guard} => 0,\n", rng.pat(ty, 0));
        }
        src += if rng.below(3) == 0 { "    _ => 1,\n  }\n}\n" } else { "  }\n}\n" };
    }
    src
}

/// A match of many arms over 12 to 15 columns with choices, whose steps reach
/// the limit (§7, S-930) now and then.
fn dense(rng: &mut Rng, k: usize) -> String {
    let cols = 12 + rng.below(4);
    let mut src = format!("pub fn d{k}(x: ({})) -> I32 {{\n  match x {{\n", vec!["I32"; cols].join(", "));
    for _ in 0..30 + rng.below(30) {
        let named = rng.below(3) == 0;
        let cells: Vec<&str> = (0..cols)
            .map(|_| {
                if named {
                    rng.pick(&["0", "1"])
                } else {
                    rng.pick(&["_", "0 | 1", "1 | 0", "0 | 1", "1 | 0", "0", "K"])
                }
            })
            .collect();
        src += &format!("    ({}) => 0,\n", cells.join(", "));
    }
    src + "  }\n}\n"
}

fn diagnostics(src: &str, whole: bool) -> String {
    WHOLE.set(whole);
    let a = check(src);
    WHOLE.set(false);
    format!("{:#?}", a.diagnostics)
}

/// R-386: the tree answers as every row of the head does, for each arm and
/// for the candidates of an E0503; the matches give both E0501 and E0503.
#[test]
fn the_tree_of_the_rows_answers_as_every_row() {
    let (mut e0501, mut e0503, mut limit) = (0, 0, 0);
    for seed in 1..=12 {
        let src = source(seed * 0x9e37_79b9, 60);
        let (tree, whole) = (diagnostics(&src, false), diagnostics(&src, true));
        assert_eq!(tree, whole, "seed {seed}:\n{src}");
        e0501 += tree.matches("E0501").count();
        e0503 += tree.matches("E0503").count();
        limit += tree.matches("not known to be exhaustive").count();
    }
    assert!(e0501 > 10 && e0503 > 10 && limit > 0, "E0501 {e0501}, E0503 {e0503}, at the limit {limit}");
}
