//! Types (spec §4, `docs/implementation-tasks.md` §3.3). Interned: a `TyId`
//! identifies one structural type, so equality is `TyId` equality.

use std::collections::HashMap;

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

/// Rates of flow signals (§11.3). Constants have no rate (`None` elsewhere).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Rate {
    Init,
    Ctl,
    Sig,
}

impl Rate {
    pub fn name(self) -> &'static str {
        match self {
            Rate::Init => "Init",
            Rate::Ctl => "Ctl",
            Rate::Sig => "Sig",
        }
    }

    pub fn parse(s: &str) -> Option<Rate> {
        Some(match s {
            "Init" => Rate::Init,
            "Ctl" => Rate::Ctl,
            "Sig" => Rate::Sig,
            _ => return None,
        })
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
    /// `Init[T]` / `Ctl[T]` / `Sig[T]` in flow signatures (§11.3).
    Rate(Rate, TyId),
    /// A const generic argument in a `Named` argument list (`Ring[F32, 4]`
    /// is `Named(Ring, [F32, ConstVal(4)])`).
    ConstVal(u32),
    /// Inference variable (T2-5; unused in this half).
    Var(u32),
    /// A type that failed to resolve; suppresses follow-on errors.
    Error,
}

/// The interner.
#[derive(Debug, Default)]
pub struct Types {
    tys: Vec<Ty>,
    map: HashMap<Ty, TyId>,
}

impl Types {
    pub fn intern(&mut self, ty: Ty) -> TyId {
        if let Some(&id) = self.map.get(&ty) {
            return id;
        }
        let id = TyId(self.tys.len() as u32);
        self.tys.push(ty.clone());
        self.map.insert(ty, id);
        id
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
                let ret = if matches!(self.get(f.ret), Ty::Unit) {
                    String::new()
                } else {
                    format!(" -> {}", self.display(f.ret, name_of, generic_name))
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
            Ty::Rate(r, t) => format!("{}[{}]", r.name(), self.display(*t, name_of, generic_name)),
            Ty::ConstVal(n) => n.to_string(),
            Ty::Var(i) => format!("?{i}"),
            Ty::Error => "<error>".into(),
        }
    }
}
