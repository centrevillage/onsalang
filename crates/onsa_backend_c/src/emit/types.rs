//! The C definitions of the types of the unit ([`type_def`]).

use super::*;

// ------------------------------------------------------------ types

pub(super) fn type_def(cx: &mut Cx, entry: &Entry) -> R<String> {
    let mut s = String::new();
    match entry {
        Entry::Synth(ty, name) => match ty {
            Ty::Array(e, n) => {
                let et = cx.names.name(e);
                let n = (*n).max(1);
                let _ = writeln!(s, "typedef struct {name} {{ {et} a[{n}]; }} {name};");
            }
            Ty::Tuple(ts) => {
                let _ = write!(s, "typedef struct {name} {{");
                if ts.is_empty() {
                    let _ = write!(s, " uint8_t onsa_empty;");
                }
                for (i, t) in ts.iter().enumerate() {
                    let tn = cx.names.name(t);
                    let _ = write!(s, " {tn} f{i};");
                }
                let _ = writeln!(s, " }} {name};");
            }
            Ty::Span(e) => {
                let et = cx.names.name(e);
                let tag = cx.names.tag(e);
                let _ = writeln!(s, "ONSA_DEFINE_SPAN({tag}, {et})");
                match &**e {
                    Ty::Float(FloatKind::F32) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_F32({tag})");
                    }
                    Ty::Float(FloatKind::F64) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_F64({tag})");
                    }
                    Ty::Int(k) => {
                        let _ = writeln!(s, "ONSA_DEFINE_SPAN_ADD_INT({tag}, {})", int_tag(*k));
                    }
                    _ => {}
                }
            }
            Ty::FnPtr(_) => return Err(unsupported(no_span(), Feature::FnValues, &[])),
            Ty::Buf(_) => return Err(unsupported(no_span(), Feature::Buf, &[])),
            _ => {}
        },
        Entry::Def(id) => {
            let name = cx.names.defs[id].clone();
            match &cx.m.ty(*id).kind {
                TypeDefKind::Struct { fields } => {
                    let fields = fields.clone();
                    if let Some(hdr) = cx.header_params.get(id).cloned() {
                        let _ = writeln!(s, "typedef {hdr} {name};");
                        return Ok(s);
                    }
                    let tag = cx.names.tags.get(id).cloned().unwrap_or_else(|| name.clone());
                    if let Some(b) = cx.bulk.get(id).cloned() {
                        let _ = write!(s, "typedef struct {} {{", b.struct_name);
                        for (i, (fname, fty)) in fields.iter().enumerate() {
                            if b.fields.contains(&(i as u32)) {
                                let tn = cx.names.name(fty);
                                let _ = write!(s, " {tn} {};", ident(fname));
                            }
                        }
                        let _ = writeln!(s, " }} {};", b.struct_name);
                        let _ = write!(s, "struct {tag} {{ void* bulk;");
                        for (i, (fname, fty)) in fields.iter().enumerate() {
                            if !b.fields.contains(&(i as u32)) {
                                let tn = cx.names.name(fty);
                                let _ = write!(s, " {tn} {};", ident(fname));
                            }
                        }
                        let _ = writeln!(s, " }};");
                    } else {
                        let _ = write!(s, "struct {tag} {{");
                        if fields.is_empty() {
                            let _ = write!(s, " uint8_t onsa_empty;");
                        }
                        for (fname, fty) in &fields {
                            let tn = cx.names.name(fty);
                            let _ = write!(s, " {tn} {};", ident(fname));
                        }
                        let _ = writeln!(s, " }};");
                    }
                    let _ = writeln!(s, "typedef struct {tag} {name};");
                }
                TypeDefKind::Enum { variants } => {
                    let variants = variants.clone();
                    let tag_ty = cx.tag_c(*id);
                    let _ = write!(s, "typedef struct {name} {{ {tag_ty} tag;");
                    if variants.iter().any(|(_, ts)| !ts.is_empty()) {
                        let _ = write!(s, " union {{");
                        for (vname, ts) in &variants {
                            if ts.is_empty() {
                                continue;
                            }
                            let _ = write!(s, " struct {{");
                            for (i, t) in ts.iter().enumerate() {
                                let tn = cx.names.name(t);
                                let _ = write!(s, " {tn} f{i};");
                            }
                            let _ = write!(s, " }} v_{};", ident(vname));
                        }
                        let _ = write!(s, " }} u;");
                    }
                    let _ = writeln!(s, " }} {name};");
                }
                TypeDefKind::Opaque => {
                    return Err(unsupported(no_span(), Feature::OpaqueType, &[&cx.m.ty(*id).name]));
                }
            }
        }
    }
    Ok(s)
}
