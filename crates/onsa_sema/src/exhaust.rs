//! `match` exhaustiveness and reachability (spec §7, E0501, E0503): the
//! usefulness algorithm over lowered patterns, one search for both.
//! Constructors come from the scrutinee type: `Bool`, enums, tuples and
//! structs (one constructor); integer, `Char` and `Str` literals have an
//! infinite domain and need `_`. A constant is not counted, whatever its type
//! (§7): only `_` covers what it compares with.
//!
//! Usefulness is NP-complete, so the search of one `match` stops at
//! [`STEP_LIMIT`].

use std::rc::Rc;

use onsa_diag::Span;
use onsa_diag::hash::HashMap;

use crate::body::Checker;
use crate::def::{DefKind, Fields};
use crate::ty::{Ty, TyId};

/// The steps the search of one `match` takes (§7, S-930): what its columns
/// and its choices branch into, a number and no time.
const STEP_LIMIT: usize = 4096;

/// A lowered pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum P {
    Wild,
    /// Constructor index and sub-patterns (in field order).
    Ctor(u32, Vec<P>),
    /// Integer / char literal.
    Lit(i128),
    Str(String),
    /// A constant (`LIMIT`): its value is not read (§7, S-185).
    Const,
    Or(Vec<P>),
}

static WILD: P = P::Wild;

/// Constructors of a type: `None` for infinite domains and opaque types.
struct Ctors {
    /// `(name, field types)` per constructor.
    items: Vec<(String, Vec<TyId>)>,
}

/// The arms of a `match` read so far, as rows: the arms without a guard
/// (§7), sorted by their heads so that an arm meets only the rows that share
/// one, and the steps its search has taken.
#[derive(Clone, Default)]
pub(crate) struct Seen {
    rows: Vec<P>,
    /// The rows by the head of a constructor (with no fields) or a literal.
    heads: HashMap<P, Vec<u32>>,
    /// The rows with a head of a constructor.
    ctors_named: Vec<u32>,
    /// The rows with a head of `_`.
    wild: Vec<u32>,
    /// The first arm of a `_` or a binding, which takes every value after it.
    pub(crate) whole: Option<Span>,
    steps: usize,
    ctors: HashMap<TyId, Option<Rc<Ctors>>>,
}

impl Seen {
    /// The arm of the pattern `p` at `at` takes part in covering.
    pub(crate) fn add(&mut self, p: P, at: Span) {
        let row = self.rows.len() as u32;
        self.index(&p, row);
        if matches!(p, P::Wild) {
            self.whole.get_or_insert(at);
        }
        self.rows.push(p);
    }

    fn index(&mut self, p: &P, row: u32) {
        match p {
            P::Or(alts) => alts.iter().for_each(|alt| self.index(alt, row)),
            P::Wild => self.wild.push(row),
            P::Const => {}
            P::Ctor(..) | P::Lit(_) | P::Str(_) => {
                if matches!(p, P::Ctor(..)) {
                    self.ctors_named.push(row);
                }
                self.heads.entry(head_key(p)).or_default().push(row);
            }
        }
    }

    /// The rows besides those of `_` that the head of `q` can meet. No
    /// literal covers an arm of a `_`.
    fn rows_for(&self, q: &P, out: &mut Vec<u32>) {
        match q {
            P::Or(alts) => alts.iter().for_each(|alt| self.rows_for(alt, out)),
            P::Wild | P::Const => out.extend_from_slice(&self.ctors_named),
            P::Ctor(..) | P::Lit(_) | P::Str(_) => {
                out.extend(self.heads.get(&head_key(q)).into_iter().flatten().copied());
            }
        }
    }
}

fn head_key(p: &P) -> P {
    if let P::Ctor(k, _) = p { P::Ctor(*k, Vec::new()) } else { p.clone() }
}

/// What a search is asked: whether the arms cover the type, or whether an arm
/// is left a value. Both read a part of the error type so that it reports
/// nothing that follows from the error (§18.1).
#[derive(Clone, Copy)]
enum Mode {
    Cover,
    Reach,
}

/// What the arms leave uncovered (E0501).
pub(crate) enum Missing {
    /// A value, as source text.
    Value(String),
    /// The search stopped at [`STEP_LIMIT`].
    OverLimit,
}

/// The search stopped at [`STEP_LIMIT`].
struct OverLimit;

/// The answer of [`Checker::useful`]: the text of a value, column by column,
/// the head column last.
type Asked = Result<Option<Vec<String>>, OverLimit>;

/// The text of a value of the constructor `name` (the tuple one is `(..)`).
fn value_text(name: &str, fields: &[String]) -> String {
    match (name, fields.join(", ")) {
        (_, f) if f.is_empty() => name.into(),
        ("(..)", f) => format!("({f})"),
        (_, f) => format!("{name}({f})"),
    }
}

/// One cell of a row, and of the arm asked about: its head column and the
/// cell of the columns after it. The rows share their tails, so that a step
/// that drops or opens a head copies no column.
#[derive(Clone, Copy)]
struct Cell<'p> {
    head: &'p P,
    tail: u32,
    /// Every column from here on is `_`.
    wild: bool,
}

/// The state of one question: cell 0 ends every row, and type 0 every list of
/// column types.
struct Search<'s, 'p> {
    mode: Mode,
    steps: &'s mut usize,
    ctors: &'s mut HashMap<TyId, Option<Rc<Ctors>>>,
    cells: Vec<Cell<'p>>,
    tys: Vec<(TyId, u32)>,
}

impl<'p> Search<'_, 'p> {
    fn push(&mut self, head: &'p P, tail: u32) -> u32 {
        let wild = matches!(head, P::Wild) && self.cells[tail as usize].wild;
        self.cells.push(Cell { head, tail, wild });
        self.cells.len() as u32 - 1
    }

    /// The cells a branch makes are its own.
    fn mark(&self) -> (usize, usize) {
        (self.cells.len(), self.tys.len())
    }

    fn reset(&mut self, (cells, tys): (usize, usize)) {
        self.cells.truncate(cells);
        self.tys.truncate(tys);
    }

    fn check(&self) -> Result<(), OverLimit> {
        if *self.steps > STEP_LIMIT { Err(OverLimit) } else { Ok(()) }
    }

    /// A step that branches `n` ways.
    fn charge(&mut self, n: usize) -> Result<(), OverLimit> {
        *self.steps += n;
        self.check()
    }

    /// The rows as their head column reads them: a choice is its branches,
    /// and a constant covers no value (see [`Checker::useful`]).
    fn open(&mut self, rows: &[u32]) -> Vec<u32> {
        let mut opened = Vec::with_capacity(rows.len());
        for &r in rows {
            self.branch(r, &mut opened);
        }
        opened
    }

    fn branch(&mut self, row: u32, out: &mut Vec<u32>) {
        let Cell { head, tail, .. } = self.cells[row as usize];
        match head {
            P::Or(alts) => {
                *self.steps += alts.len() - 1;
                for alt in alts {
                    let row = self.push(alt, tail);
                    self.branch(row, out);
                }
            }
            P::Const => {}
            _ => out.push(row),
        }
    }

    /// The row `r` with its head, a constructor or `_`, opened into `arity`
    /// columns.
    fn enter(&mut self, r: u32, arity: usize) -> u32 {
        let Cell { head, mut tail, .. } = self.cells[r as usize];
        if let P::Ctor(_, subs) = head {
            for sub in subs.iter().rev() {
                tail = self.push(sub, tail);
            }
        } else {
            for _ in 0..arity {
                tail = self.push(&WILD, tail);
            }
        }
        tail
    }
}

impl Checker<'_> {
    fn ctors(&mut self, ty: TyId) -> Option<Ctors> {
        let ty = self.infer.resolve(&mut self.a.types, ty);
        match self.a.types.get(ty).clone() {
            Ty::Bool => Some(Ctors { items: vec![("false".into(), vec![]), ("true".into(), vec![])] }),
            Ty::Unit => Some(Ctors { items: vec![("()".into(), vec![])] }),
            Ty::Tuple(ts) => Some(Ctors { items: vec![("(..)".into(), ts)] }),
            Ty::Named(d, args) => match self.a.def(d).kind.clone() {
                DefKind::Enum(e) => {
                    // A variant of a lang item is written by its name alone (§4.1).
                    let name = self.a.def(d).name.clone();
                    let lang = self.a.modules.lang.of(d).is_some();
                    let items = e
                        .variants
                        .iter()
                        .map(|v| {
                            let fs: Vec<TyId> = v.fields.iter().map(|&f| self.a.types.subst(f, &args)).collect();
                            (if lang { v.name.clone() } else { format!("{name}.{}", v.name) }, fs)
                        })
                        .collect();
                    Some(Ctors { items })
                }
                DefKind::Struct(s) => match s.fields {
                    Fields::Named(fs) => {
                        let tys: Vec<TyId> = fs.iter().map(|f| self.a.types.subst(f.ty, &args)).collect();
                        Some(Ctors { items: vec![(self.a.def(d).name.clone(), tys)] })
                    }
                    Fields::Opaque => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// The constructors of `ty`, read once for a `match`.
    fn ctors_of(&mut self, s: &mut Search, ty: TyId) -> Option<Rc<Ctors>> {
        let ty = self.infer.resolve(&mut self.a.types, ty);
        if let Some(cs) = s.ctors.get(&ty) {
            return cs.clone();
        }
        let cs = self.ctors(ty).map(Rc::new);
        s.ctors.insert(ty, cs.clone());
        cs
    }

    /// Whether the columns `tys` of `q` take a value that none of `rows`
    /// covers: such a value, its head column last. Both E0501 and E0503 ask
    /// this; [`Mode`] is the one thing they differ in.
    fn useful<'p>(&mut self, s: &mut Search<'_, 'p>, rows: &[u32], q: u32, tys: u32) -> Asked {
        if tys == 0 {
            return Ok(rows.is_empty().then(Vec::new));
        }
        let (head, rest) = (s.cells[q as usize].head, s.cells[q as usize].tail);
        let (ty, rest_tys) = s.tys[tys as usize];
        // A part of the error type matches anything (§18.1, S-692 A2), and so
        // does a type not all read (S-260), which a field of a struct can hold
        // where `mentions_failed` does not look.
        if match self.ty(self.shallow(ty)) {
            Ty::Error => true,
            Ty::Named(d, _) => self.a.partly_read(d),
            _ => false,
        } {
            let tails: Vec<u32> = match s.mode {
                Mode::Cover => rows.iter().map(|&r| s.cells[r as usize].tail).collect(),
                // §18.1, S-936: an arm with such a part is reached.
                Mode::Reach => Vec::new(),
            };
            return self.useful_rest(s, &tails, rest, rest_tys, "_".into());
        }
        // A constant (§7, S-185): its value is not read, so a row of one
        // covers no value and an arm of one can be any value.
        let head = if matches!(head, P::Const) { &WILD } else { head };
        let opened = s.open(rows);
        let grew = opened.len() > rows.len();
        let rows = &opened[..];
        if rows.iter().any(|&r| s.cells[r as usize].wild) {
            return Ok(None);
        }
        let cs = self.ctors_of(s, ty);
        // One constructor chooses nothing: `(_, _)` reads as far as `_`.
        if grew || cs.as_ref().is_none_or(|cs| cs.items.len() != 1) {
            s.check()?;
        }
        match (head, &cs) {
            // The unit is the arm: any branch that is useful will do (§7, S-932).
            (P::Or(alts), _) => {
                s.charge(alts.len())?;
                for alt in alts {
                    let mark = s.mark();
                    let q = s.push(alt, rest);
                    let found = self.useful(s, rows, q, tys)?;
                    s.reset(mark);
                    if found.is_some() {
                        return Ok(found);
                    }
                }
                Ok(None)
            }
            (P::Lit(_) | P::Str(_), _) => {
                let same = |c: &&Cell| matches!(c.head, P::Wild) || c.head == head;
                let tails = rows.iter().map(|&r| &s.cells[r as usize]).filter(same).map(|c| c.tail).collect::<Vec<_>>();
                self.useful_rest(s, &tails, rest, rest_tys, "_".into())
            }
            (P::Ctor(k, _), Some(cs)) => {
                let cells = &s.cells;
                let of_k = |&r: &u32| match cells[r as usize].head {
                    P::Ctor(j, _) => j == k,
                    h => matches!(h, P::Wild),
                };
                let rows: Vec<u32> = rows.iter().copied().filter(of_k).collect();
                self.useful_ctor(s, &rows, q, &cs.items[*k as usize], tys)
            }
            _ => self.useful_wild(s, rows, q, cs.as_deref(), tys),
        }
    }

    /// [`Self::useful`] of what follows a head that takes no column of its
    /// own, which `head` stands for.
    fn useful_rest<'p>(&mut self, s: &mut Search<'_, 'p>, rows: &[u32], q: u32, tys: u32, head: String) -> Asked {
        let mut w = self.useful(s, rows, q, tys)?;
        if let Some(w) = &mut w {
            w.push(head);
        }
        Ok(w)
    }

    /// [`Self::useful`] of the rows of one constructor, the head of each and
    /// of `q` opened into its fields.
    fn useful_ctor<'p>(
        &mut self,
        s: &mut Search<'_, 'p>,
        rows: &[u32],
        q: u32,
        (name, fields): &(String, Vec<TyId>),
        tys: u32,
    ) -> Asked {
        let mark = s.mark();
        let rows: Vec<u32> = rows.iter().map(|&r| s.enter(r, fields.len())).collect();
        let q = s.enter(q, fields.len());
        let mut inner = s.tys[tys as usize].1;
        for &t in fields.iter().rev() {
            s.tys.push((t, inner));
            inner = s.tys.len() as u32 - 1;
        }
        let mut found = self.useful(s, &rows, q, inner)?;
        s.reset(mark);
        if let Some(w) = &mut found {
            let mut subs = w.split_off(w.len() - fields.len());
            subs.reverse();
            w.push(value_text(name, &subs));
        }
        Ok(found)
    }

    /// [`Self::useful`] of a head that takes any value: every constructor
    /// when the rows name them all, else what the rows of `_` leave (§7: an
    /// infinite domain is never all named). A value of the first constructor
    /// missing stands for such a head.
    fn useful_wild<'p>(&mut self, s: &mut Search<'_, 'p>, rows: &[u32], q: u32, cs: Option<&Ctors>, tys: u32) -> Asked {
        let of_cell = |r: u32| s.cells[r as usize];
        let mut named: Vec<(u32, u32)> = rows
            .iter()
            .filter_map(|&r| if let P::Ctor(k, _) = of_cell(r).head { Some((*k, r)) } else { None })
            .collect();
        named.sort_by_key(|n| n.0);
        let wilds: Vec<u32> = rows.iter().copied().filter(|&r| matches!(of_cell(r).head, P::Wild)).collect();
        let groups: Vec<&[(u32, u32)]> = named.chunk_by(|a, b| a.0 == b.0).collect();
        if let Some(cs) = cs
            && groups.len() == cs.items.len()
        {
            if groups.len() > 1 {
                s.charge(groups.len())?;
            }
            for (group, item) in groups.iter().zip(&cs.items) {
                let of_k: Vec<u32> = group.iter().map(|n| n.1).chain(wilds.iter().copied()).collect();
                let found = self.useful_ctor(s, &of_k, q, item, tys)?;
                if found.is_some() {
                    return Ok(found);
                }
            }
            return Ok(None);
        }
        let tails: Vec<u32> = wilds.iter().map(|&r| s.cells[r as usize].tail).collect();
        let wit = cs.map_or("_".into(), |cs| {
            let k = groups.iter().zip(0u32..).find(|(g, k)| g[0].0 != *k).map_or(groups.len(), |(_, k)| k as usize);
            let (name, fields) = &cs.items[k];
            value_text(name, &vec!["_".to_string(); fields.len()])
        });
        let (rest, rest_tys) = (s.cells[q as usize].tail, s.tys[tys as usize].1);
        self.useful_rest(s, &tails, rest, rest_tys, wit)
    }

    /// [`Self::useful`] of `q` over the rows of `seen` that its head can
    /// meet, whose steps count towards the limit of the `match`.
    fn ask(&mut self, seen: &mut Seen, q: &P, ty: TyId, mode: Mode) -> Asked {
        let mut found = Vec::new();
        seen.rows_for(q, &mut found);
        found.extend_from_slice(&seen.wild);
        found.sort_unstable();
        found.dedup();
        let end = Cell { head: &WILD, tail: 0, wild: true };
        let Seen { rows, steps, ctors, .. } = seen;
        let mut s = Search { mode, steps, ctors, cells: vec![end], tys: vec![(ty, 0), (ty, 0)] };
        let rows: Vec<u32> = found.iter().map(|&i| s.push(&rows[i as usize], 0)).collect();
        let q = s.push(q, 0);
        self.useful(&mut s, &rows, q, 1)
    }

    /// Whether an arm of the pattern `q` can be chosen after the arms of
    /// `seen` (§7, E0503). Past the limit of the `match`, it can.
    pub(crate) fn reachable(&mut self, seen: &mut Seen, q: &P, ty: TyId) -> bool {
        !matches!(self.ask(seen, q, ty, Mode::Reach), Ok(None))
    }

    /// What the arms of `seen` leave uncovered of `ty`, if anything (E0501).
    pub(crate) fn missing_pattern(&mut self, seen: &mut Seen, ty: TyId) -> Option<Missing> {
        match self.ask(seen, &WILD, ty, Mode::Cover) {
            Ok(None) => None,
            Ok(Some(mut w)) => Some(Missing::Value(w.pop().unwrap_or_else(|| "_".into()))),
            Err(OverLimit) => Some(Missing::OverLimit),
        }
    }
}
