//! `match` exhaustiveness (spec §7, E0501): the usefulness algorithm over
//! lowered patterns. Constructors come from the scrutinee type: `Bool`,
//! enums, `Option` / `Result`, tuples and structs (one constructor); integer,
//! `Char` and `Str` literals have an infinite domain and need `_`.

use crate::body::Checker;
use crate::def::{DefKind, Fields};
use crate::ty::{BuiltinTy, Ty, TyId};

/// A lowered pattern.
#[derive(Debug, Clone, PartialEq)]
pub enum P {
    Wild,
    /// Constructor index and sub-patterns (in field order).
    Ctor(u32, Vec<P>),
    /// Integer / char literal.
    Lit(i128),
    Str(String),
    Or(Vec<P>),
}

/// Constructors of a type: `None` for infinite domains and opaque types.
struct Ctors {
    /// `(name, field types)` per constructor.
    items: Vec<(String, Vec<TyId>)>,
}

impl Checker<'_> {
    fn ctors(&mut self, ty: TyId) -> Option<Ctors> {
        let ty = self.infer.resolve(&mut self.a.types, ty);
        match self.a.types.get(ty).clone() {
            Ty::Bool => Some(Ctors { items: vec![("false".into(), vec![]), ("true".into(), vec![])] }),
            Ty::Unit => Some(Ctors { items: vec![("()".into(), vec![])] }),
            Ty::Tuple(ts) => Some(Ctors { items: vec![("(..)".into(), ts)] }),
            Ty::Builtin(BuiltinTy::Option, a) => {
                Some(Ctors { items: vec![("None".into(), vec![]), ("Some".into(), vec![a[0]])] })
            }
            Ty::Builtin(BuiltinTy::Result, a) => {
                Some(Ctors { items: vec![("Ok".into(), vec![a[0]]), ("Err".into(), vec![a[1]])] })
            }
            Ty::Named(d, args) => match self.a.def(d).kind.clone() {
                DefKind::Enum(e) => {
                    let name = self.a.def(d).name.clone();
                    let items = e
                        .variants
                        .iter()
                        .map(|v| {
                            let fs: Vec<TyId> = v.fields.iter().map(|&f| self.subst_pub(f, &args)).collect();
                            (format!("{name}.{}", v.name), fs)
                        })
                        .collect();
                    Some(Ctors { items })
                }
                DefKind::Struct(s) => match s.fields {
                    Fields::Named(fs) => {
                        let tys: Vec<TyId> = fs.iter().map(|f| self.subst_pub(f.ty, &args)).collect();
                        Some(Ctors { items: vec![(self.a.def(d).name.clone(), tys)] })
                    }
                    Fields::Tuple(t) => {
                        let t = self.subst_pub(t, &args);
                        Some(Ctors { items: vec![(self.a.def(d).name.clone(), vec![t])] })
                    }
                    Fields::Opaque => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Expand or-patterns in the first column.
    fn expand(rows: Vec<Vec<P>>) -> Vec<Vec<P>> {
        let mut out = Vec::new();
        for row in rows {
            match row.first() {
                Some(P::Or(alts)) => {
                    for alt in alts {
                        let mut r = row.clone();
                        r[0] = alt.clone();
                        out.extend(Self::expand(vec![r]));
                    }
                }
                _ => out.push(row),
            }
        }
        out
    }

    /// Specialize rows by constructor `c` with `arity` fields.
    fn specialize(rows: &[Vec<P>], c: u32, arity: usize) -> Vec<Vec<P>> {
        let mut out = Vec::new();
        for row in rows {
            match &row[0] {
                P::Ctor(k, subs) if *k == c => {
                    let mut r = subs.clone();
                    r.extend_from_slice(&row[1..]);
                    out.push(r);
                }
                P::Wild => {
                    let mut r = vec![P::Wild; arity];
                    r.extend_from_slice(&row[1..]);
                    out.push(r);
                }
                _ => {}
            }
        }
        out
    }

    fn default_rows(rows: &[Vec<P>]) -> Vec<Vec<P>> {
        rows.iter().filter(|r| matches!(r[0], P::Wild)).map(|r| r[1..].to_vec()).collect()
    }

    /// A witness (as source text) for a value the rows do not cover, if any.
    fn witness(&mut self, rows: Vec<Vec<P>>, tys: &[TyId]) -> Option<Vec<String>> {
        if tys.is_empty() {
            return if rows.is_empty() { Some(Vec::new()) } else { None };
        }
        let rows = Self::expand(rows);
        let ctors = self.ctors(tys[0]);
        match ctors {
            Some(cs) => {
                let used: Vec<u32> =
                    rows.iter().filter_map(|r| if let P::Ctor(k, _) = &r[0] { Some(*k) } else { None }).collect();
                let complete = (0..cs.items.len() as u32).all(|k| used.contains(&k));
                if complete || !used.is_empty() {
                    // Try every constructor; a missing one yields a witness directly.
                    for (k, (name, fields)) in cs.items.iter().enumerate() {
                        let k = k as u32;
                        let spec = Self::specialize(&rows, k, fields.len());
                        let mut sub_tys = fields.clone();
                        sub_tys.extend_from_slice(&tys[1..]);
                        if let Some(mut w) = self.witness(spec, &sub_tys) {
                            let rest = w.split_off(fields.len());
                            let head = if fields.is_empty() {
                                name.clone()
                            } else if name == "(..)" {
                                format!("({})", w.join(", "))
                            } else {
                                format!("{name}({})", w.join(", "))
                            };
                            let mut out = vec![head];
                            out.extend(rest);
                            return Some(out);
                        }
                    }
                    None
                } else {
                    let d = Self::default_rows(&rows);
                    let mut w = self.witness(d, &tys[1..])?;
                    let (name, fields) = &cs.items[0];
                    let head = if fields.is_empty() {
                        name.clone()
                    } else if name == "(..)" {
                        format!("({})", vec!["_"; fields.len()].join(", "))
                    } else {
                        format!("{name}({})", vec!["_"; fields.len()].join(", "))
                    };
                    w.insert(0, head);
                    Some(w)
                }
            }
            None => {
                // Infinite domain: only a wildcard row covers it.
                let d = Self::default_rows(&rows);
                let mut w = self.witness(d, &tys[1..])?;
                w.insert(0, "_".into());
                Some(w)
            }
        }
    }

    /// `Some(text)` when the rows do not cover `ty`.
    pub(crate) fn missing_pattern(&mut self, rows: &[Vec<P>], ty: TyId) -> Option<String> {
        self.witness(rows.to_vec(), &[ty]).map(|w| w.into_iter().next().unwrap_or_else(|| "_".into()))
    }
}
