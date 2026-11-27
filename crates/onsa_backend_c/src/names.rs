//! C identifiers and type names (D-10).

use std::collections::HashMap;

use onsa_core::{CTy, FloatKind, IntKind, Module, TyKind, TypeDefKind, TypeId};

const C_KEYWORDS: &[&str] = &[
    "auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum", "extern", "float",
    "for", "goto", "if", "inline", "int", "long", "register", "restrict", "return", "short", "signed", "sizeof",
    "static", "struct", "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "bool", "true", "false",
    "main", "NULL", "NAN", "INFINITY",
];

/// A C identifier from an Onsa name: `.` becomes `__` as in [`qualified`]
/// (`a.prev_0` is `a__prev_0`, §11.6), `@` becomes `_`, C keywords and
/// reserved spellings get a suffix, leading underscores get a prefix.
pub fn ident(name: &str) -> String {
    let mut s = String::with_capacity(name.len());
    for c in name.chars() {
        match c {
            '.' => s.push_str("__"),
            c if c.is_ascii_alphanumeric() => s.push(c),
            _ => s.push('_'),
        }
    }
    if s.starts_with('_') {
        s = format!("onsa{s}");
    }
    if s.starts_with("onsa_") && !name.starts_with("onsa_") {
        // only the generated prefix above
    } else if s.starts_with("onsa_") {
        s.push('_');
    }
    if C_KEYWORDS.contains(&s.as_str()) {
        s.push('_');
    }
    s
}

/// Qualified function / type name: `dsp.voice.State` → `dsp__voice__State`.
pub fn qualified(name: &str) -> String {
    let mut s = String::new();
    for (i, seg) in name.split('.').enumerate() {
        if i > 0 {
            s.push_str("__");
        }
        s.push_str(
            &seg.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect::<String>(),
        );
    }
    if s.starts_with('_') {
        s = format!("onsa{s}");
    }
    s
}

pub fn int_c(k: IntKind) -> &'static str {
    match k {
        IntKind::I8 => "int8_t",
        IntKind::I16 => "int16_t",
        IntKind::I32 => "int32_t",
        IntKind::I64 => "int64_t",
        IntKind::U8 => "uint8_t",
        IntKind::U16 => "uint16_t",
        IntKind::U32 => "uint32_t",
        IntKind::U64 => "uint64_t",
    }
}

/// Short lowercase tag used in helper names (`onsa_add_i32`).
pub fn int_tag(k: IntKind) -> &'static str {
    match k {
        IntKind::I8 => "i8",
        IntKind::I16 => "i16",
        IntKind::I32 => "i32",
        IntKind::I64 => "i64",
        IntKind::U8 => "u8",
        IntKind::U16 => "u16",
        IntKind::U32 => "u32",
        IntKind::U64 => "u64",
    }
}

pub fn float_c(k: FloatKind) -> &'static str {
    match k {
        FloatKind::F32 => "float",
        FloatKind::F64 => "double",
    }
}

pub fn float_tag(k: FloatKind) -> &'static str {
    match k {
        FloatKind::F32 => "f32",
        FloatKind::F64 => "f64",
    }
}

/// The C spelling of a scalar type; `None` for the other types.
pub fn scalar_c(ty: &TyKind) -> Option<&'static str> {
    match ty {
        TyKind::Int(k) => Some(int_c(*k)),
        TyKind::Float(k) => Some(float_c(*k)),
        TyKind::Bool => Some("bool"),
        TyKind::Char => Some("uint32_t"),
        _ => None,
    }
}

/// Registry of the C spellings of Core types, in dependency order.
pub struct TypeNames<'m> {
    pub m: &'m Module,
    /// C names of arrays, tuples, spans.
    synthetic: HashMap<CTy, String>,
    /// Struct / enum typedef names, of those registered or being registered.
    pub defs: HashMap<TypeId, String>,
    /// Struct tags that differ from the typedef name (exported flow states).
    pub tags: HashMap<TypeId, String>,
    /// Every type definition the unit needs, dependencies first.
    pub order: Vec<Entry>,
}

/// One type definition to emit.
#[derive(Debug, Clone)]
pub enum Entry {
    Def(TypeId),
    /// An array / tuple / span typedef, with its C name.
    Synth(CTy, String),
}

/// A struct or an enum not registered yet: the name being made stops at it,
/// and is made again once it is ([`TypeNames::register_def`]).
struct Unregistered(TypeId);

type N<T> = Result<T, Unregistered>;

impl<'m> TypeNames<'m> {
    pub fn new(m: &'m Module) -> Self {
        TypeNames { m, synthetic: HashMap::new(), defs: HashMap::new(), tags: HashMap::new(), order: Vec::new() }
    }

    /// The C type name of `ty`, registering synthetic types on first use.
    pub fn name(&mut self, ty: CTy) -> String {
        self.registered(|n| n.name_in(ty))
    }

    /// The C typedef name of the struct or enum `id`, registering it.
    pub fn def(&mut self, id: TypeId) -> String {
        self.registered(|n| n.def_in(id))
    }

    /// A short mangled tag for use inside synthetic names.
    pub fn tag(&mut self, ty: CTy) -> String {
        self.registered(|n| n.tag_in(ty))
    }

    /// `make`, again after registering each definition it stops at.
    fn registered<T>(&mut self, mut make: impl FnMut(&mut Self) -> N<T>) -> T {
        loop {
            match make(self) {
                Ok(v) => return v,
                Err(Unregistered(id)) => self.register_def(id),
            }
        }
    }

    fn def_in(&mut self, id: TypeId) -> N<String> {
        self.defs.get(&id).cloned().ok_or(Unregistered(id))
    }

    fn name_in(&mut self, ty: CTy) -> N<String> {
        Ok(match self.m.tys.kind(ty) {
            TyKind::Unit => "onsa_unit".into(),
            TyKind::Struct(id) | TyKind::Enum(id) => self.def_in(*id)?,
            TyKind::Array(..) | TyKind::Tuple(_) | TyKind::Span(_) | TyKind::FnPtr(_) | TyKind::Buf(_) => {
                if let Some(n) = self.synthetic.get(&ty) {
                    return Ok(n.clone());
                }
                let n = self.synthetic_name(ty)?;
                self.synthetic.insert(ty, n.clone());
                self.order.push(Entry::Synth(ty, n.clone()));
                n
            }
            // The scalars, named in one place.
            scalar => scalar_c(scalar).expect("every other type is a scalar").into(),
        })
    }

    fn tag_in(&mut self, ty: CTy) -> N<String> {
        let m = self.m;
        Ok(match m.tys.kind(ty) {
            TyKind::Int(k) => int_tag(*k).into(),
            TyKind::Float(k) => float_tag(*k).into(),
            TyKind::Bool => "bool".into(),
            TyKind::Char => "char".into(),
            TyKind::Unit => "unit".into(),
            TyKind::Struct(id) | TyKind::Enum(id) => self.def_in(*id)?,
            TyKind::Array(e, n) => format!("arr_{}_{}", self.tag_in(*e)?, n),
            TyKind::Tuple(ts) => {
                let parts: Vec<String> = ts.iter().map(|t| self.tag_in(*t)).collect::<N<_>>()?;
                format!("tup_{}", parts.join("_"))
            }
            TyKind::Span(e) => format!("span_{}", self.tag_in(*e)?),
            TyKind::FnPtr(_) => "fnptr".into(),
            TyKind::Buf(e) => format!("buf_{}", self.tag_in(*e)?),
        })
    }

    fn synthetic_name(&mut self, ty: CTy) -> N<String> {
        // Register the element types first so definitions come out in order.
        let m = self.m;
        match m.tys.kind(ty) {
            TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e) => {
                self.name_in(*e)?;
            }
            TyKind::Tuple(ts) => {
                for t in ts {
                    self.name_in(*t)?;
                }
            }
            _ => {}
        }
        Ok(format!("onsa_{}", self.tag_in(ty)?))
    }

    /// Register `root` and the definitions its fields need, on a stack of
    /// its own (a chain of declarations takes no stack of Rust, R-319): the
    /// field types first (dependency order), then each definition. A field
    /// that stops at a definition not registered is named again after it.
    fn register_def(&mut self, root: TypeId) {
        let mut stack = vec![self.open(root)];
        while let Some((id, parts, next)) = stack.last_mut() {
            let Some(&t) = parts.get(*next) else {
                self.order.push(Entry::Def(*id));
                stack.pop();
                continue;
            };
            match self.name_in(t) {
                Ok(_) => *next += 1,
                Err(Unregistered(d)) => {
                    let open = self.open(d);
                    stack.push(open);
                }
            }
        }
    }

    /// Name the definition `id`, and the types of its fields to name, from
    /// the first.
    fn open(&mut self, id: TypeId) -> (TypeId, Vec<CTy>, usize) {
        let m = self.m;
        let def = m.ty(id);
        self.defs.insert(id, qualified(&def.name));
        let parts = match &def.kind {
            TypeDefKind::Struct { fields } => fields.iter().map(|(_, t)| *t).collect(),
            TypeDefKind::Enum { variants } => variants.iter().flat_map(|(_, ts)| ts.iter().copied()).collect(),
            TypeDefKind::Opaque => Vec::new(),
        };
        (id, parts, 0)
    }
}
