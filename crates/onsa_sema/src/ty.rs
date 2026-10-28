//! Types (spec §4, `design/03-types.md`). Interned: a `TyId`
//! identifies one structural type, so equality is `TyId` equality.

use std::collections::{HashMap, HashSet};

use onsa_syntax::ast::Mode;

use crate::def::DefId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntKind {
    pub fn name(self) -> &'static str {
        match self {
            IntKind::I8 => "I8",
            IntKind::I16 => "I16",
            IntKind::I32 => "I32",
            IntKind::I64 => "I64",
            IntKind::U8 => "U8",
            IntKind::U16 => "U16",
            IntKind::U32 => "U32",
            IntKind::U64 => "U64",
        }
    }

    pub fn parse(s: &str) -> Option<IntKind> {
        Some(match s {
            "I8" => IntKind::I8,
            "I16" => IntKind::I16,
            "I32" => IntKind::I32,
            "I64" => IntKind::I64,
            "U8" => IntKind::U8,
            "U16" => IntKind::U16,
            "U32" => IntKind::U32,
            "U64" => IntKind::U64,
            _ => return None,
        })
    }

    pub fn bits(self) -> u32 {
        match self {
            IntKind::I8 | IntKind::U8 => 8,
            IntKind::I16 | IntKind::U16 => 16,
            IntKind::I32 | IntKind::U32 => 32,
            IntKind::I64 | IntKind::U64 => 64,
        }
    }

    pub fn signed(self) -> bool {
        matches!(self, IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64)
    }

    /// Inclusive range of values.
    pub fn range(self) -> (i128, i128) {
        let b = self.bits();
        if self.signed() { (-(1i128 << (b - 1)), (1i128 << (b - 1)) - 1) } else { (0, (1i128 << b) - 1) }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatKind {
    F32,
    F64,
}

impl FloatKind {
    pub fn name(self) -> &'static str {
        match self {
            FloatKind::F32 => "F32",
            FloatKind::F64 => "F64",
        }
    }

    /// The width for the value of a float literal ([`onsa_syntax::float_value`]).
    pub fn width(self) -> onsa_syntax::FloatWidth {
        match self {
            FloatKind::F32 => onsa_syntax::FloatWidth::F32,
            FloatKind::F64 => onsa_syntax::FloatWidth::F64,
        }
    }
}

/// Builtin generic types (spec §4.1). The kind column of §4.1 is in `kind.rs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuiltinTy {
    /// `Str` (Shared, 0 args)
    Str,
    /// `Bytes` (Shared, 0 args)
    Bytes,
    /// `Array[T]` (Shared)
    Array,
    /// `Map[K, V]` (Shared)
    Map,
    /// `Set[T]` (Shared)
    Set,
    /// `Buf[T]` (Affine; interpreter-only in phase 1, D-08)
    Buf,
    /// `Span[T]` (second-class, §5.3)
    Span,
    /// `Ptr[T]` (Copy, §14)
    Ptr,
    /// `Option[T]`
    Option,
    /// `Result[T, E]`
    Result,
}

impl BuiltinTy {
    /// Whether its arguments are held as values, as of an enum (§4.4).
    pub fn holds_values(self) -> bool {
        matches!(self, BuiltinTy::Option | BuiltinTy::Result)
    }

    pub fn name(self) -> &'static str {
        match self {
            BuiltinTy::Str => "Str",
            BuiltinTy::Bytes => "Bytes",
            BuiltinTy::Array => "Array",
            BuiltinTy::Map => "Map",
            BuiltinTy::Set => "Set",
            BuiltinTy::Buf => "Buf",
            BuiltinTy::Span => "Span",
            BuiltinTy::Ptr => "Ptr",
            BuiltinTy::Option => "Option",
            BuiltinTy::Result => "Result",
        }
    }

    pub fn parse(s: &str) -> Option<BuiltinTy> {
        Some(match s {
            "Str" => BuiltinTy::Str,
            "Bytes" => BuiltinTy::Bytes,
            "Array" => BuiltinTy::Array,
            "Map" => BuiltinTy::Map,
            "Set" => BuiltinTy::Set,
            "Buf" => BuiltinTy::Buf,
            "Span" => BuiltinTy::Span,
            "Ptr" => BuiltinTy::Ptr,
            "Option" => BuiltinTy::Option,
            "Result" => BuiltinTy::Result,
            _ => return None,
        })
    }

    pub fn arity(self) -> usize {
        match self {
            BuiltinTy::Str | BuiltinTy::Bytes => 0,
            BuiltinTy::Map | BuiltinTy::Result => 2,
            _ => 1,
        }
    }
}

/// Length of a fixed-length array (§4.1): a constant, or a const generic
/// parameter of the enclosing item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Len {
    Const(u32),
    Param(u32),
    /// Inference variable for a length (body checking, T2-6).
    Var(u32),
}

/// Rates of flow signals (§11.3), the clocks `init`, `block`, `sample` of
/// the inputs and the output of a flow.
/// Constants have no rate (`None` elsewhere).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Rate {
    Init,
    Ctl,
    Sig,
}

impl Rate {
    /// Every clock, slowest first.
    pub const ALL: [Rate; 3] = [Rate::Init, Rate::Ctl, Rate::Sig];

    /// The name of the clock (§11.3): the one table of the clock names.
    pub fn clock(self) -> &'static str {
        match self {
            Rate::Init => "init",
            Rate::Ctl => "block",
            Rate::Sig => "sample",
        }
    }

    /// The clock of the name `name`, if it is one.
    pub fn of_clock(name: &str) -> Option<Rate> {
        Rate::ALL.into_iter().find(|r| r.clock() == name)
    }

    /// The rate the name `name` of a rate written as a type names (`Sig`,
    /// [`onsa_syntax::foreign::RATE_TYPES`], S-120), if it is one.
    pub fn of_type_name(name: &str) -> Option<Rate> {
        Rate::ALL.into_iter().zip(onsa_syntax::foreign::RATE_TYPES).find(|&(_, n)| n == name).map(|(r, _)| r)
    }
}

/// Function type (§4.1). Captures are not part of the type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnTy {
    pub rt: bool,
    pub params: Vec<(Mode, TyId)>,
    pub ret: TyId,
    pub effects: EffectSet,
}

/// Effect row (§8). Phase 1 recognizes `Alloc`; other names are kept so that
/// `std` can declare them (D-08) and user code gets E0200 when it names them.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct EffectSet {
    pub alloc: bool,
    /// Effects other than `Alloc`, by name (unsupported in phase 1).
    pub other: Vec<String>,
    /// Effect-row variables (`e`), as generic parameter indices.
    pub vars: Vec<u32>,
}

impl EffectSet {
    pub fn is_empty(&self) -> bool {
        !self.alloc && self.other.is_empty() && self.vars.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Int(IntKind),
    Float(FloatKind),
    Bool,
    Char,
    Unit,
    Array(TyId, Len),
    Tuple(Vec<TyId>),
    /// A user struct / enum / flow-generated type, with generic arguments.
    Named(DefId, Vec<TyId>),
    Builtin(BuiltinTy, Vec<TyId>),
    Fn(FnTy),
    /// A generic type parameter of the enclosing item (index into its generics).
    Param(u32),
    /// A const generic argument in a `Named` argument list (`Ring[F32, 4]`
    /// is `Named(Ring, [F32, ConstVal(4)])`).
    ConstVal(u32),
    /// Inference variable (T2-5; unused in this half).
    Var(u32),
    /// A type that failed to resolve; suppresses follow-on errors.
    Error,
}

/// The limits of the types the check makes (§4.4, S-264): the one place.
pub const TYPE_DEPTH_LIMIT: u32 = 256;
pub const TYPE_SIZE_LIMIT: u32 = 4096;

/// The arguments a type is read under (R-30): `Param(i)` stands for
/// `args[i]`, read under `outer`. The walks behind `&Analysis` (kinds,
/// layouts, the drops of `rt`) read a field of a generic type under the
/// arguments of its use, without making the substituted type.
#[derive(Debug, Clone, Copy)]
pub struct Env<'e> {
    pub args: &'e [TyId],
    pub outer: Option<&'e Env<'e>>,
}

/// The interner.
#[derive(Debug, Default)]
pub struct Types {
    tys: Vec<Ty>,
    map: HashMap<Ty, TyId>,
    /// The depth and the size (§4.4) of each type, from its parts once when
    /// it is interned, each held at its limit + 1: so a shared type is
    /// judged without being expanded.
    measures: Vec<(u16, u32)>,
}

impl Types {
    pub fn intern(&mut self, ty: Ty) -> TyId {
        if let Some(&id) = self.map.get(&ty) {
            return id;
        }
        let id = TyId(self.tys.len() as u32);
        self.measures.push(self.measure(&ty));
        self.tys.push(ty.clone());
        self.map.insert(ty, id);
        id
    }

    /// The depth and the size of `ty` (§4.4): a form (a type with
    /// arguments, a tuple, an array, a function type) is a level and one, a
    /// name and a const argument (a length) one each; `()` is a form with no
    /// parts. A declared type is a leaf.
    fn measure(&self, ty: &Ty) -> (u16, u32) {
        let (own, parts): (u32, Vec<TyId>) = match ty {
            Ty::Unit => (1, Vec::new()),
            Ty::Tuple(ts) => (1, ts.clone()),
            Ty::Array(t, _) => (2, vec![*t]),
            Ty::Named(_, ts) | Ty::Builtin(_, ts) if !ts.is_empty() => (2, ts.clone()),
            Ty::Fn(f) => (1, f.params.iter().map(|&(_, t)| t).chain([f.ret]).collect()),
            _ => return (0, 1),
        };
        let (depth, size) = parts.iter().fold((0, own), |(d, s), p| {
            let (pd, ps) = self.measures[p.0 as usize];
            (d.max(pd), s.saturating_add(ps))
        });
        ((depth + 1).min(TYPE_DEPTH_LIMIT as u16 + 1), size.min(TYPE_SIZE_LIMIT + 1))
    }

    /// The depth of `id` (§4.4), at most [`TYPE_DEPTH_LIMIT`] + 1.
    pub fn depth(&self, id: TyId) -> u32 {
        u32::from(self.measures[id.0 as usize].0)
    }

    /// The size of `id` (§4.4), at most [`TYPE_SIZE_LIMIT`] + 1.
    pub fn size(&self, id: TyId) -> u32 {
        self.measures[id.0 as usize].1
    }

    /// Whether `id` is deeper or larger than the limits (§4.4, E0422).
    pub fn over_limit(&self, id: TyId) -> bool {
        self.depth(id) > TYPE_DEPTH_LIMIT || self.size(id) > TYPE_SIZE_LIMIT
    }

    /// Whether the error type is in `id`. Each type is visited once.
    pub fn has_error(&self, id: TyId) -> bool {
        let (mut seen, mut todo) = (HashSet::new(), vec![id]);
        while let Some(t) = todo.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.get(t) {
                Ty::Error => return true,
                Ty::Array(e, _) => todo.push(*e),
                Ty::Tuple(ts) | Ty::Named(_, ts) | Ty::Builtin(_, ts) => todo.extend(ts),
                Ty::Fn(f) => todo.extend(f.params.iter().map(|&(_, p)| p).chain([f.ret])),
                _ => {}
            }
        }
        false
    }

    /// `ty` read under `env`: a parameter is followed to its argument, read
    /// under the environment around; one with no argument stays.
    pub fn resolve<'e>(&self, mut ty: TyId, mut env: Option<&'e Env<'e>>) -> (TyId, Option<&'e Env<'e>>) {
        while let (Ty::Param(i), Some(e)) = (self.get(ty), env) {
            let Some(&arg) = e.args.get(*i as usize) else { break };
            (ty, env) = (arg, e.outer);
        }
        (ty, env)
    }

    /// The length `len` read under `env`: a const parameter is its argument.
    pub fn len_in(&self, len: Len, env: Option<&Env>) -> Len {
        let (Len::Param(i), Some(e)) = (len, env) else { return len };
        let Some(&arg) = e.args.get(i as usize) else { return len };
        match self.get(self.resolve(arg, e.outer).0) {
            Ty::ConstVal(n) => Len::Const(*n),
            Ty::Param(j) => Len::Param(*j),
            Ty::Var(v) => Len::Var(*v),
            _ => len,
        }
    }

    /// Substitute `Ty::Param(i)` / `Len::Param(i)` with `args[i]` (variables
    /// or concrete), interning the types it makes (R-30: the one substitution).
    pub fn subst(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        if args.is_empty() {
            return ty;
        }
        match self.get(ty).clone() {
            Ty::Param(i) => args.get(i as usize).copied().unwrap_or(ty),
            Ty::Array(e, len) => {
                let e2 = self.subst(e, args);
                let len2 = self.len_in(len, Some(&Env { args, outer: None }));
                self.intern(Ty::Array(e2, len2))
            }
            Ty::Tuple(ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.intern(Ty::Tuple(ns))
            }
            Ty::Named(d, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.intern(Ty::Named(d, ns))
            }
            Ty::Builtin(b, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.subst(t, args)).collect();
                self.intern(Ty::Builtin(b, ns))
            }
            Ty::Fn(f) => {
                let params: Vec<(Mode, TyId)> = f.params.iter().map(|(m, t)| (*m, self.subst(*t, args))).collect();
                let ret = self.subst(f.ret, args);
                self.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects }))
            }
            _ => ty,
        }
    }

    pub fn get(&self, id: TyId) -> &Ty {
        &self.tys[id.0 as usize]
    }

    /// Look up an already-interned structure without interning it.
    pub fn find(&self, ty: &Ty) -> Option<TyId> {
        self.map.get(ty).copied()
    }

    pub fn int(&mut self, k: IntKind) -> TyId {
        self.intern(Ty::Int(k))
    }

    pub fn float(&mut self, k: FloatKind) -> TyId {
        self.intern(Ty::Float(k))
    }

    pub fn unit(&mut self) -> TyId {
        self.intern(Ty::Unit)
    }

    pub fn bool(&mut self) -> TyId {
        self.intern(Ty::Bool)
    }

    pub fn error(&mut self) -> TyId {
        self.intern(Ty::Error)
    }

    pub fn builtin(&mut self, b: BuiltinTy, args: Vec<TyId>) -> TyId {
        self.intern(Ty::Builtin(b, args))
    }

    pub fn len(&self) -> usize {
        self.tys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tys.is_empty()
    }

    /// Scalar type by name (`F32`, `Bool`, ...), if it is one.
    pub fn scalar(&mut self, name: &str) -> Option<TyId> {
        Some(match name {
            "Bool" => self.bool(),
            "Char" => self.intern(Ty::Char),
            "F32" => self.float(FloatKind::F32),
            "F64" => self.float(FloatKind::F64),
            _ => self.int(IntKind::parse(name)?),
        })
    }

    /// Whether the type `ty` is written in parentheses when a `uses` or an
    /// `at` follows it (`follows`): a function type there would take that
    /// `uses` or `at` as its own result's (`fn() -> (fn()) uses {Alloc}` is
    /// not `fn() -> fn() uses {Alloc}`, §8.1; `g: (fn(F32) -> F32) at block`,
    /// §11.3, S-367). The one rule, for [`Self::display`] and the signatures
    /// of `onsa interface` (W3-20/b, W3-10).
    pub fn parens_before_uses(&self, ty: TyId, follows: bool) -> bool {
        follows && matches!(self.get(ty), Ty::Fn(_))
    }

    /// The user types named in `id`, its types within types included (the
    /// arguments, the elements, the parameters and result of a function
    /// type), in the order written (§15.1, S-700). Each type is visited once,
    /// so the work is linear in the types interned, not in the tree they
    /// stand for (`type A2 = (A1, A1)`).
    pub fn named(&self, id: TyId) -> Vec<DefId> {
        let mut out = Vec::new();
        self.named_in(id, &mut HashSet::new(), &mut out);
        out
    }

    fn named_in(&self, id: TyId, seen: &mut HashSet<TyId>, out: &mut Vec<DefId>) {
        if !seen.insert(id) {
            return;
        }
        let mut each = |ts: &[TyId], out: &mut Vec<DefId>| ts.iter().for_each(|&t| self.named_in(t, seen, out));
        match self.get(id) {
            Ty::Named(d, args) => {
                out.push(*d);
                each(args, out);
            }
            Ty::Array(t, _) => each(&[*t], out),
            Ty::Tuple(ts) | Ty::Builtin(_, ts) => each(ts, out),
            Ty::Fn(f) => {
                let ts: Vec<TyId> = f.params.iter().map(|&(_, t)| t).chain([f.ret]).collect();
                each(&ts, out);
            }
            Ty::Int(_) | Ty::Float(_) | Ty::Bool | Ty::Char | Ty::Unit => {}
            Ty::Param(_) | Ty::ConstVal(_) | Ty::Var(_) | Ty::Error => {}
        }
    }

    /// Source-like rendering, with user types by name via `name_of`.
    pub fn display(&self, id: TyId, name_of: &dyn Fn(DefId) -> String, generic_name: &dyn Fn(u32) -> String) -> String {
        let ty = self.get(id);
        let list =
            |xs: &[TyId]| xs.iter().map(|&t| self.display(t, name_of, generic_name)).collect::<Vec<_>>().join(", ");
        match ty {
            Ty::Int(k) => k.name().to_string(),
            Ty::Float(k) => k.name().to_string(),
            Ty::Bool => "Bool".into(),
            Ty::Char => "Char".into(),
            Ty::Unit => "()".into(),
            Ty::Array(t, len) => {
                let n = match len {
                    Len::Const(n) => n.to_string(),
                    Len::Param(i) => generic_name(*i),
                    Len::Var(i) => format!("?{i}"),
                };
                format!("[{}; {n}]", self.display(*t, name_of, generic_name))
            }
            Ty::Tuple(ts) => format!("({})", list(ts)),
            Ty::Named(d, args) => {
                if args.is_empty() {
                    name_of(*d)
                } else {
                    format!("{}[{}]", name_of(*d), list(args))
                }
            }
            Ty::Builtin(b, args) => {
                if args.is_empty() {
                    b.name().to_string()
                } else {
                    format!("{}[{}]", b.name(), list(args))
                }
            }
            Ty::Fn(f) => {
                let ps = f
                    .params
                    .iter()
                    .map(|(m, t)| {
                        let m = match m {
                            Mode::Borrow => "",
                            Mode::Inout => "inout ",
                            Mode::Move => "move ",
                        };
                        format!("{m}{}", self.display(*t, name_of, generic_name))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let rt = if f.rt { "rt " } else { "" };
                let ret = match self.display(f.ret, name_of, generic_name) {
                    _ if matches!(self.get(f.ret), Ty::Unit) => String::new(),
                    r if self.parens_before_uses(f.ret, !f.effects.is_empty()) => format!(" -> ({r})"),
                    r => format!(" -> {r}"),
                };
                let eff = if f.effects.is_empty() {
                    String::new()
                } else {
                    let mut names = Vec::new();
                    if f.effects.alloc {
                        names.push("Alloc".to_string());
                    }
                    names.extend(f.effects.other.iter().cloned());
                    names.extend(f.effects.vars.iter().map(|&v| generic_name(v)));
                    format!(" uses {{{}}}", names.join(", "))
                };
                format!("{rt}fn({ps}){ret}{eff}")
            }
            Ty::Param(i) => generic_name(*i),
            Ty::ConstVal(n) => n.to_string(),
            Ty::Var(i) => format!("?{i}"),
            // What a syntax error left unread (S-59): shown as a hole, so that a
            // diagnostic about the type around it does not name an inner error.
            Ty::Error => "_".into(),
        }
    }
}
