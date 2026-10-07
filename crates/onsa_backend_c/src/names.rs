//! C identifiers and type names (D-10).

use std::collections::{HashMap, HashSet};

use onsa_core::{FloatKind, IntKind, Module, Ty, TypeDefKind, TypeId};

const C_KEYWORDS: &[&str] = &[
    "auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum", "extern", "float",
    "for", "goto", "if", "inline", "int", "long", "register", "restrict", "return", "short", "signed", "sizeof",
    "static", "struct", "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "bool", "true", "false",
    "main", "NULL", "NAN", "INFINITY",
];

/// A C identifier from an Onsa name: `.` and `@` become `_`, C keywords and
/// reserved spellings get a suffix, leading underscores get a prefix.
pub fn ident(name: &str) -> String {
    let mut s: String = name.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
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
pub fn scalar_c(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::Int(k) => Some(int_c(*k)),
        Ty::Float(k) => Some(float_c(*k)),
        Ty::Bool => Some("bool"),
        Ty::Char => Some("uint32_t"),
        _ => None,
    }
}

/// Registry of the C spellings of Core types, in dependency order.
pub struct TypeNames<'m> {
    pub m: &'m Module,
    /// C names of arrays, tuples, spans.
    synthetic: HashMap<Ty, String>,
    /// Struct / enum typedef names.
    pub defs: HashMap<TypeId, String>,
    /// Struct tags that differ from the typedef name (exported flow states).
    pub tags: HashMap<TypeId, String>,
    /// Every type definition the unit needs, dependencies first.
    pub order: Vec<Entry>,
    def_seen: HashSet<TypeId>,
}

/// One type definition to emit.
#[derive(Debug, Clone)]
pub enum Entry {
    Def(TypeId),
    /// An array / tuple / span typedef, with its C name.
    Synth(Ty, String),
}

impl<'m> TypeNames<'m> {
    pub fn new(m: &'m Module) -> Self {
        TypeNames {
            m,
            synthetic: HashMap::new(),
            defs: HashMap::new(),
            tags: HashMap::new(),
            order: Vec::new(),
            def_seen: HashSet::new(),
        }
    }

    /// The C type name of `ty`, registering synthetic types on first use.
    pub fn name(&mut self, ty: &Ty) -> String {
        match ty {
            Ty::Unit => "onsa_unit".into(),
            Ty::Struct(id) | Ty::Enum(id) => {
                self.register_def(*id);
                self.defs[id].clone()
            }
            Ty::Array(..) | Ty::Tuple(_) | Ty::Span(_) | Ty::FnPtr(_) | Ty::Buf(_) => {
                if let Some(n) = self.synthetic.get(ty) {
                    return n.clone();
                }
                let n = self.synthetic_name(ty);
                self.synthetic.insert(ty.clone(), n.clone());
                self.order.push(Entry::Synth(ty.clone(), n.clone()));
                n
            }
            // The scalars, named in one place.
            scalar => scalar_c(scalar).expect("every other type is a scalar").into(),
        }
    }

    /// A short mangled tag for use inside synthetic names.
    pub fn tag(&mut self, ty: &Ty) -> String {
        match ty {
            Ty::Int(k) => int_tag(*k).into(),
            Ty::Float(k) => float_tag(*k).into(),
            Ty::Bool => "bool".into(),
            Ty::Char => "char".into(),
            Ty::Unit => "unit".into(),
            Ty::Struct(id) | Ty::Enum(id) => {
                self.register_def(*id);
                self.defs[id].clone()
            }
            Ty::Array(e, n) => format!("arr_{}_{}", self.tag(e), n),
            Ty::Tuple(ts) => {
                let parts: Vec<String> = ts.iter().map(|t| self.tag(t)).collect();
                format!("tup_{}", parts.join("_"))
            }
            Ty::Span(e) => format!("span_{}", self.tag(e)),
            Ty::FnPtr(_) => "fnptr".into(),
            Ty::Buf(e) => format!("buf_{}", self.tag(e)),
        }
    }

    fn synthetic_name(&mut self, ty: &Ty) -> String {
        // Register the element types first so definitions come out in order.
        match ty {
            Ty::Array(e, _) | Ty::Span(e) | Ty::Buf(e) => {
                self.name(e);
            }
            Ty::Tuple(ts) => {
                for t in ts {
                    self.name(t);
                }
            }
            _ => {}
        }
        format!("onsa_{}", self.tag(ty))
    }

    fn register_def(&mut self, id: TypeId) {
        if self.def_seen.contains(&id) {
            return;
        }
        self.def_seen.insert(id);
        let def = self.m.ty(id);
        self.defs.insert(id, qualified(&def.name));
        // Field types first (dependency order), then this definition.
        match &def.kind {
            TypeDefKind::Struct { fields } => {
                for (_, t) in fields.clone() {
                    self.name(&t);
                }
            }
            TypeDefKind::Enum { variants } => {
                for (_, ts) in variants.clone() {
                    for t in ts {
                        self.name(&t);
                    }
                }
            }
            TypeDefKind::Opaque => {}
        }
        self.order.push(Entry::Def(id));
    }
}
