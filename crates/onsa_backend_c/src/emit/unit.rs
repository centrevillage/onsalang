//! The unit: [`emit_unit`] makes the C unit of a Core module (the exports,
//! what they reach, the types, the constants and the functions in their
//! order), and the entries it starts from ([`export_roots`]).

use super::*;

// ------------------------------------------------------------ the unit

pub(crate) fn emit_unit(m: &Module, opts: &EmitOptions) -> Result<CUnit, Vec<Diagnostic>> {
    let mut diags = Vec::new();
    let mut cx = Cx {
        m,
        opts,
        names: TypeNames::new(m),
        bulk: HashMap::new(),
        fn_names: HashMap::new(),
        const_names: HashMap::new(),
        exports: Vec::new(),
        header_params: HashMap::new(),
        guarded_names: HashMap::new(),
    };

    // 1. Exports, and what they reach ([`export_roots`]).
    for e in &opts.exports {
        let Some(i) = find_flow(m, &e.flow) else {
            diags.push(Diagnostic::new(
                Stage::Build,
                Code::E0302,
                no_span(),
                format!("cannot find the flow `{}` to export", e.flow),
            ));
            continue;
        };
        let meta = &m.flows[i];
        let short = meta.name.rsplit('.').next().unwrap_or(&meta.name).to_string();
        let symbol = format!("{}{}", opts.prefix(), ident(&short));
        let upper: String =
            symbol.chars().map(|c| if c.is_ascii_alphanumeric() { c.to_ascii_uppercase() } else { '_' }).collect();
        let layout = onsa_core::flow_layout_for(m, meta.fns.state, opts.bulk_threshold, opts.ptr_size);
        cx.exports.push(Export { meta_index: i, symbol, upper, layout });
    }
    let mut export_fns: Vec<FnId> = Vec::new();
    for name in &opts.export_fns {
        match find_fn(m, name) {
            Some(f) => export_fns.push(f),
            None => diags.push(Diagnostic::new(
                Stage::Build,
                Code::E0302,
                no_span(),
                format!("cannot find the function `{name}` to export"),
            )),
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }
    let reach = onsa_core::reach(m, &export_roots(m, opts));
    let (lacking, lacking_fns) = crate::prims::check(m, &reach);
    let consts = named_consts(m, &reach);

    // 2. Bulk regions of exported states (spec §12.4). A bulk-split state
    //    embedded in another reachable type is not supported yet.
    for e in &cx.exports {
        if e.layout.bulk_size > 0 {
            let state = m.flows[e.meta_index].fns.state;
            let bulk_names: HashSet<&str> = e.layout.bulk_fields.iter().map(|f| f.name.as_str()).collect();
            let fields = cx
                .fields(state)
                .iter()
                .enumerate()
                .filter(|(_, (n, _))| bulk_names.contains(n.as_str()))
                .map(|(i, _)| i as u32)
                .collect();
            cx.bulk.insert(state, BulkInfo { struct_name: format!("{}__Bulk", qualified(&m.ty(state).name)), fields });
        }
    }
    for (i, t) in m.types.iter().enumerate() {
        if let TypeDefKind::Struct { fields } = &t.kind {
            for (_, fty) in fields {
                if let Some(id) = contains_bulk(&cx, fty) {
                    diags.push(unsupported(no_span(), Feature::BulkInType, &[&m.ty(id).name, &m.types[i].name]));
                }
            }
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }

    // 3. Names of functions and constants.
    for f in &reach.fns {
        cx.fn_names.insert(*f, qualified(&m.fn_(*f).name));
    }
    for c in &consts {
        cx.const_names.insert(*c, qualified(&m.const_(*c).name));
    }
    // The guarded twins (R-167): the functions a `poison` wrapper calls after
    // its `setjmp`, named here with the other names so that no name of the
    // unit is taken twice (a function of the source may be called `f__guarded`).
    if opts.panic == PanicMode::Poison {
        let mut called: Vec<FnId> = export_fns.clone();
        for e in &cx.exports {
            let f = &m.flows[e.meta_index].fns;
            called.extend([f.init, f.process]);
        }
        let mut taken: HashSet<String> = cx.fn_names.values().chain(cx.const_names.values()).cloned().collect();
        taken.extend(m.types.iter().map(|t| qualified(&t.name)));
        for f in called {
            if cx.guarded_names.contains_key(&f) {
                continue;
            }
            let base = format!("{}{GUARDED_SUFFIX}", cx.fn_name(f));
            let mut name = base.clone();
            let mut n = 1;
            while taken.contains(&name) {
                name = format!("{base}_{n}");
                n += 1;
            }
            taken.insert(name.clone());
            cx.guarded_names.insert(f, name);
        }
    }
    // Exported states keep the public tag; exported params come from the header.
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        cx.names.tags.insert(f.state, e.symbol.clone());
        cx.header_params.insert(f.params, format!("{}_params", e.symbol));
    }

    // 4. Register every type the unit needs (dependency order falls out),
    //    and the pairs of `narrow_from` the runtime instantiates.
    for c in &consts {
        cx.names.name(&m.const_(*c).ty);
    }
    let mut narrows: Vec<(IntKind, IntKind)> = Vec::new();
    for f in &reach.fns {
        let def = m.fn_(*f);
        for p in &def.params {
            cx.names.name(&p.ty);
        }
        cx.names.name(&def.ret);
        for l in &def.locals {
            cx.names.name(&l.ty);
        }
        if let Some(b) = &def.body {
            let mut tys = Vec::new();
            walk_block(b, &mut |e| {
                tys.push(e.ty.clone());
                if let ExprKind::Prim { prim: Prim::NarrowParts { from, to }, .. } = &e.kind
                    && !narrows.contains(&(*from, *to))
                {
                    narrows.push((*from, *to));
                }
            });
            for t in tys {
                cx.names.name(&t);
            }
        }
    }
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        cx.names.name(&Ty::Struct(f.state));
        cx.names.name(&Ty::Struct(f.config));
        cx.names.name(&Ty::Struct(f.params));
    }

    // 5. Headers (T4-3) and the translation unit.
    let mut headers = Vec::new();
    let mut flows = Vec::new();
    for e in cx.exports.clone() {
        match crate::export::header(&mut cx, &e) {
            Ok((h, parts)) => {
                let header = format!("{}.h", e.symbol);
                flows.push(crate::FlowApi {
                    flow: m.flows[e.meta_index].name.clone(),
                    symbol: e.symbol.clone(),
                    upper: e.upper.clone(),
                    header: header.clone(),
                    init_args: parts.init_args,
                    params_fields: parts.params_fields,
                    process_args: parts.process_args,
                });
                headers.push((header, h));
            }
            Err(d) => diags.push(d),
        }
    }
    let mut fns = Vec::new();
    if !export_fns.is_empty() {
        let header = format!("{}{}.h", opts.prefix(), ident(&opts.package));
        match crate::export::fn_header(&mut cx, &export_fns, &header) {
            Ok((h, apis)) => {
                headers.push((header, h));
                fns = apis;
            }
            Err(d) => diags.push(d),
        }
    }

    let mut out = String::new();
    // The flags the code needs head the file (spec §13.4): a build outside
    // `onsa build` reads them there.
    let _ = writeln!(
        out,
        "/* {} — generated by onsa build from package `{}`; do not edit.\n *\n \
         * Compile it with the flags of the target (spec §13.4): {}\n \
         * In a GNU mode, GCC also needs -ffp-contract=off with the define ONSA_FP_CONTRACT_OFF.\n \
         * {} stops the compile when a flag the code needs is seen to be missing; the define\n \
         * ONSA_ALLOW_INEXACT_FP removes those checks and gives up the bit-exact results. */",
        CUnit::source_name(&opts.package),
        opts.package,
        opts.cflags.join(" "),
        crate::INTERNAL_HEADER_NAME
    );
    let _ = writeln!(out, "#define {}", opts.panic.define());
    let _ = writeln!(out, "#include \"{}\"", crate::INTERNAL_HEADER_NAME);
    if opts.provides_alloc {
        let _ = writeln!(out, "#include <stdlib.h>");
    }
    for (name, _) in &headers {
        let _ = writeln!(out, "#include \"{name}\"");
    }
    out.push('\n');

    // Types.
    let _ = writeln!(out, "/* ---- types ---- */");
    let order = cx.names.order.clone();
    for entry in &order {
        match type_def(&mut cx, entry) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }
    for e in &cx.exports {
        let f = &m.flows[e.meta_index].fns;
        let state = cx.names.defs[&f.state].clone();
        // The C compiler verifies the header's SIZE / ALIGN against the real
        // struct (spec §12.4). The `poison` jmp_buf is a wrapper local (S-26),
        // so the layout is the same on every target.
        let _ = writeln!(
            out,
            "ONSA_STATIC_ASSERT(sizeof({state}) == {}_SIZE, \"{} fast region size (spec §12.4)\");",
            e.upper, e.upper
        );
        let _ = writeln!(
            out,
            "ONSA_STATIC_ASSERT(ONSA_ALIGNOF({state}) == {}_ALIGN, \"{} alignment (spec §12.4)\");",
            e.upper, e.upper
        );
        for mark in ["poisoned", "initialized"] {
            if let Some(p) = e.layout.fast_fields.iter().find(|f| f.name == mark) {
                let _ = writeln!(
                    out,
                    "ONSA_STATIC_ASSERT(offsetof({state}, {mark}) == {}, \"{} layout prefix (spec §12.4)\");",
                    p.offset, e.upper
                );
            }
        }
        if let Some(b) = cx.bulk.get(&f.state) {
            let _ = writeln!(
                out,
                "ONSA_STATIC_ASSERT(sizeof({}) == {}, \"{} bulk region size (spec §12.4)\");",
                b.struct_name, e.layout.bulk_size, e.upper
            );
        }
    }
    out.push('\n');

    // The range checks of `narrow_from` (spec §3.3), from the runtime.
    if !narrows.is_empty() {
        let _ = writeln!(out, "/* ---- narrow ---- */");
        for (from, to) in &narrows {
            let _ = writeln!(
                out,
                "ONSA_DEFINE_NARROW({}, {}, {}, {}, {}, {})",
                int_tag(*from),
                crate::names::int_c(*from),
                u8::from(from.signed()),
                int_tag(*to),
                crate::names::int_c(*to),
                u8::from(to.signed())
            );
        }
        out.push('\n');
    }

    // Constants.
    if !consts.is_empty() {
        let _ = writeln!(out, "/* ---- constants ---- */");
        for c in &consts {
            let def = m.const_(*c);
            let ty = cx.names.name(&def.ty);
            match const_init(&mut cx, &def.init) {
                Ok(init) => {
                    let _ = writeln!(out, "static const {ty} {} = {init};", cx.const_names[c]);
                }
                Err(d) => diags.push(d),
            }
        }
        out.push('\n');
    }

    // Functions: prototypes, then definitions.
    let _ = writeln!(out, "/* ---- functions ---- */");
    let mut protos = String::new();
    let mut bodies = String::new();
    let mut twins = String::new();
    for f in reach.fns.difference(&lacking_fns) {
        let def = m.fn_(*f);
        // A panic names this function (S-67).
        let _scope = onsa_diag::internal::item_scope(def.span);
        match FnEmitter::new(&mut cx, *f).emit() {
            Ok((proto, body, twin)) => {
                let _ = writeln!(protos, "{proto};");
                bodies.push_str(&body);
                bodies.push('\n');
                if let Some(twin) = twin {
                    let _ = writeln!(twins, "{twin}");
                }
            }
            Err(d) => diags.push(Diagnostic::new(
                d.stage,
                d.code,
                if d.span == no_span() { def.span } else { d.span },
                d.message,
            )),
        }
    }
    out.push_str(&protos);
    out.push('\n');
    out.push_str(&bodies);
    if !twins.is_empty() {
        let _ = writeln!(out, "/* ---- called after the setjmp of a wrapper, never inlined there (R-167) ---- */");
        out.push_str(&twins);
        out.push('\n');
    }

    // Export wrappers; `<prefix>take_panic` is theirs (a build without exports has no prefix).
    let poison = opts.panic == PanicMode::Poison && opts.exports_any();
    if poison {
        out.push_str(&crate::export::take_panic(&cx));
    }
    for e in cx.exports.clone() {
        match crate::export::wrappers(&mut cx, &e) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }
    for f in &export_fns {
        match crate::export::fn_wrapper(&mut cx, *f) {
            Ok(s) => out.push_str(&s),
            Err(d) => diags.push(d),
        }
    }

    diags.extend(lacking);
    if !diags.is_empty() {
        return Err(diags);
    }
    let take_panic = poison.then(|| crate::export::take_panic_name(opts));
    Ok(CUnit {
        source: out,
        headers,
        runtime_header: crate::PUBLIC_HEADER.to_string(),
        internal_header: crate::internal_header(),
        flows,
        fns,
        take_panic,
    })
}

/// The `const`s the unit names: those the reached functions read (the one
/// place C refers to a `const` by its name). A `const` that only an
/// initializer reads is reached ([`onsa_core::reach`]) but is written into
/// that initializer ([`const_init`]), so it gets no `static const` of its
/// own (it would be an unused variable, `-Wunused-const-variable`).
fn named_consts(m: &Module, reach: &onsa_core::Reach) -> BTreeSet<ConstId> {
    let mut named = BTreeSet::new();
    for &f in &reach.fns {
        if let Some(b) = &m.fn_(f).body {
            walk_block(b, &mut |e| {
                if let ExprKind::Const(c) = &e.kind {
                    named.insert(*c);
                }
            });
        }
    }
    named
}

/// The entries of the unit (spec §15.2, S-242): the entries of each
/// exported flow ([`onsa_core::FlowFns::entries`]) and each exported
/// function. A name that names nothing is left out; [`emit_unit`] reports it
/// (E0302).
pub(crate) fn export_roots(m: &Module, opts: &EmitOptions) -> Vec<FnId> {
    let mut roots = Vec::new();
    for e in &opts.exports {
        if let Some(i) = find_flow(m, &e.flow) {
            roots.extend(m.flows[i].fns.entries());
        }
    }
    roots.extend(opts.export_fns.iter().filter_map(|name| find_fn(m, name)));
    roots
}

fn find_fn(m: &Module, name: &str) -> Option<FnId> {
    m.fns.iter().position(|f| f.name == name).map(|i| FnId(i as u32))
}

/// Index into `Module::flows` by qualified name, or by a unique suffix.
pub(crate) fn find_flow(m: &Module, name: &str) -> Option<usize> {
    if let Some(i) = m.flows.iter().position(|f| f.name == name) {
        return Some(i);
    }
    let suffix = format!(".{name}");
    let hits: Vec<usize> =
        m.flows.iter().enumerate().filter(|(_, f)| f.name.ends_with(&suffix)).map(|(i, _)| i).collect();
    if hits.len() == 1 { Some(hits[0]) } else { None }
}

fn contains_bulk(cx: &Cx, ty: &Ty) -> Option<TypeId> {
    match ty {
        Ty::Struct(id) if cx.bulk.contains_key(id) => Some(*id),
        Ty::Array(e, _) => contains_bulk(cx, e),
        Ty::Tuple(ts) => ts.iter().find_map(|t| contains_bulk(cx, t)),
        _ => None,
    }
}
