//! Unit tests on hand-built Core modules (T4-2 rules that need no source).

use onsa_core::*;
use onsa_diag::{FileId, Span};

use crate::emit::{c_string, f32_lit, f64_lit, int_lit};
use crate::names::{ident, qualified};
use crate::{EmitOptions, emit};

fn sp() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn e(ty: Ty, kind: ExprKind) -> Expr {
    Expr::new(ty, sp(), kind)
}

fn lit_f32(x: f32) -> Expr {
    e(Ty::Float(FloatKind::F32), ExprKind::Lit(Lit::F32(x)))
}

fn lit_i32(x: i128) -> Expr {
    e(Ty::Int(IntKind::I32), ExprKind::Lit(Lit::Int(x)))
}

fn local(l: u32, ty: Ty) -> Expr {
    e(ty, ExprKind::Local(LocalId(l)))
}

fn binary(op: BinOp, overflow: Overflow, ty: Ty, a: Expr, b: Expr) -> Expr {
    e(ty, ExprKind::Binary { op, overflow, lhs: Box::new(a), rhs: Box::new(b) })
}

/// A module with one exported function `m.f(x: T, y: T) -> T { body }`.
fn one_fn(ty: Ty, body: Expr, extra_types: Vec<TypeDef>) -> Module {
    Module {
        types: extra_types,
        consts: Vec::new(),
        fns: vec![FnDef {
            name: "m.f".into(),
            params: vec![
                Param { local: LocalId(0), mode: Mode::Borrow, ty: ty.clone() },
                Param { local: LocalId(1), mode: Mode::Borrow, ty: ty.clone() },
            ],
            ret: ty.clone(),
            sret: false,
            rt: true,
            locals: vec![Local { name: "x".into(), ty: ty.clone() }, Local { name: "y".into(), ty }],
            body: Some(Block { stmts: Vec::new(), value: Some(Box::new(body)) }),
            span: sp(),
            test: None,
        }],
        messages: Vec::new(),
        flows: Vec::new(),
        moves: Vec::new(),
    }
}

fn emit_fn(m: &Module) -> String {
    let opts = EmitOptions { export_fns: vec!["m.f".into()], ..Default::default() };
    emit(m, &opts).unwrap_or_else(|d| panic!("{d:?}")).source
}

#[test]
fn names_are_mangled() {
    assert_eq!(qualified("dsp.voice.State"), "dsp__voice__State");
    assert_eq!(qualified("clamp__F32"), "clamp__F32");
    assert_eq!(qualified("__eq.Option__U8"), "onsa__eq__Option__U8");
    assert_eq!(ident("vdelay_0.buf"), "vdelay_0_buf");
    assert_eq!(ident("y1@7"), "y1_7");
    assert_eq!(ident("float"), "float_");
    assert_eq!(ident("_x"), "onsa_x");
    assert_eq!(ident("onsa_t1"), "onsa_t1_");
}

#[test]
fn literals_round_trip() {
    assert_eq!(f32_lit(std::f32::consts::PI), "3.1415927f");
    assert_eq!(f32_lit(1.0), "1.0f");
    assert_eq!(f32_lit(1e-7), "1e-7f");
    assert_eq!(f32_lit(f32::INFINITY), "INFINITY");
    assert_eq!(f64_lit(2.5e-3), "0.0025");
    assert_eq!(int_lit(IntKind::I32, i32::MIN as i128), "INT32_MIN");
    assert_eq!(int_lit(IntKind::U64, 7), "UINT64_C(7)");
    assert_eq!(int_lit(IntKind::I8, -5), "((int8_t)-5)");
    assert_eq!(c_string("a\"b\n"), "\"a\\\"b\\n\"");
}

#[test]
fn f32_ops_are_wrapped_and_f64_are_not() {
    let f32t = Ty::Float(FloatKind::F32);
    let body = binary(
        BinOp::Mul,
        Overflow::Checked,
        f32t.clone(),
        binary(BinOp::Add, Overflow::Checked, f32t.clone(), local(0, f32t.clone()), local(1, f32t.clone())),
        lit_f32(2.0),
    );
    let c = emit_fn(&one_fn(f32t, body, vec![]));
    assert!(c.contains("return (float)((float)(x + y) * 2.0f);"), "{c}");
    let f64t = Ty::Float(FloatKind::F64);
    let body = binary(BinOp::Add, Overflow::Checked, f64t.clone(), local(0, f64t.clone()), local(1, f64t.clone()));
    let c = emit_fn(&one_fn(f64t, body, vec![]));
    assert!(c.contains("return (x + y);"), "{c}");
}

#[test]
fn integer_overflow_modes_pick_helpers() {
    let i32t = Ty::Int(IntKind::I32);
    for (ov, helper) in [
        (Overflow::Checked, "onsa_add_i32(x, y, \"\", 0)"),
        (Overflow::Wrap, "onsa_wadd_i32(x, y)"),
        (Overflow::Sat, "onsa_sadd_i32(x, y)"),
    ] {
        let body = binary(BinOp::Add, ov, i32t.clone(), local(0, i32t.clone()), local(1, i32t.clone()));
        let c = emit_fn(&one_fn(i32t.clone(), body, vec![]));
        assert!(c.contains(helper), "{ov:?}: {c}");
    }
    let body = binary(
        BinOp::Shl,
        Overflow::Checked,
        i32t.clone(),
        local(0, i32t.clone()),
        e(Ty::u32(), ExprKind::Lit(Lit::Int(3))),
    );
    let c = emit_fn(&one_fn(i32t.clone(), body, vec![]));
    assert!(c.contains("onsa_shl_i32(x, UINT32_C(3), \"\", 0)"), "{c}");
    let body = binary(BinOp::Div, Overflow::Checked, i32t.clone(), local(0, i32t.clone()), lit_i32(2));
    let c = emit_fn(&one_fn(i32t, body, vec![]));
    assert!(c.contains("onsa_div_i32(x, INT32_C(2), \"\", 0)"), "{c}");
}

#[test]
fn array_wrappers_are_shared_and_enums_switch() {
    // enum E { A, B(I32) }; fn f(x: E, y: E) -> E { switch x { A => y, B => E.B(payload) } }
    let et = TypeDef {
        name: "m.E".into(),
        kind: TypeDefKind::Enum { variants: vec![("A".into(), vec![]), ("B".into(), vec![Ty::Int(IntKind::I32)])] },
    };
    let ety = Ty::Enum(TypeId(0));
    let payload =
        e(Ty::Int(IntKind::I32), ExprKind::Payload { base: Box::new(local(0, ety.clone())), tag: 1, index: 0 });
    let body = e(
        ety.clone(),
        ExprKind::Switch {
            scrutinee: Box::new(local(0, ety.clone())),
            arms: vec![
                (0, Block { stmts: vec![], value: Some(Box::new(local(1, ety.clone()))) }),
                (
                    1,
                    Block {
                        stmts: vec![],
                        value: Some(Box::new(e(
                            ety.clone(),
                            ExprKind::Variant { ty: TypeId(0), tag: 1, fields: vec![payload] },
                        ))),
                    },
                ),
            ],
            default: None,
        },
    );
    let m = one_fn(ety, body, vec![et]);
    // Exporting an enum-returning fn is unsupported; emit through a reachable internal fn instead.
    let opts = EmitOptions::default();
    let c = emit(&m, &opts).unwrap().source;
    // Nothing reachable: no function emitted.
    assert!(!c.contains("m__f"), "{c}");
    // Reach it via an export of a scalar function that calls it.
    let mut m2 = m.clone();
    m2.fns.push(FnDef {
        name: "m.g".into(),
        params: vec![],
        ret: Ty::Int(IntKind::I32),
        sret: false,
        rt: true,
        locals: vec![Local { name: "v".into(), ty: Ty::Enum(TypeId(0)) }],
        body: Some(Block {
            stmts: vec![Stmt {
                span: sp(),
                kind: StmtKind::Let(
                    LocalId(0),
                    e(
                        Ty::Enum(TypeId(0)),
                        ExprKind::Call {
                            fn_: FnId(0),
                            args: vec![
                                Arg {
                                    mode: Mode::Borrow,
                                    expr: e(
                                        Ty::Enum(TypeId(0)),
                                        ExprKind::Variant { ty: TypeId(0), tag: 0, fields: vec![] },
                                    ),
                                },
                                Arg {
                                    mode: Mode::Borrow,
                                    expr: e(
                                        Ty::Enum(TypeId(0)),
                                        ExprKind::Variant { ty: TypeId(0), tag: 1, fields: vec![lit_i32(4)] },
                                    ),
                                },
                            ],
                        },
                    ),
                ),
            }],
            value: Some(Box::new(e(Ty::Int(IntKind::I32), ExprKind::Tag(Box::new(local(0, Ty::Enum(TypeId(0)))))))),
        }),
        span: sp(),
        test: None,
    });
    let opts = EmitOptions { export_fns: vec!["m.g".into()], ..Default::default() };
    let c = emit(&m2, &opts).unwrap_or_else(|d| panic!("{d:?}")).source;
    assert!(c.contains("typedef struct m__E { uint8_t tag; union { struct { int32_t f0; } v_B; } u; } m__E;"), "{c}");
    assert!(c.contains("if ((*x).tag == 0) {"), "{c}");
    assert!(c.contains("} else if ((*x).tag == 1) {"), "{c}");
    assert!(c.contains(".u = { .v_B = { .f0 = (*x).u.v_B.f0 } }"), "{c}");
}

/// The API of an exported function is recorded as the header declares it
/// (`CUnit::fns`, plan D-15): the tools that call it read the names here.
#[test]
fn exported_functions_are_recorded() {
    let m = one_fn(Ty::Int(IntKind::I32), local(0, Ty::Int(IntKind::I32)), Vec::new());
    let opts = EmitOptions {
        package: "pk".into(),
        prefix: "vc_".into(),
        export_fns: vec!["m.f".into()],
        panic: crate::PanicMode::Poison,
        ..Default::default()
    };
    let unit = emit(&m, &opts).unwrap_or_else(|d| panic!("{d:?}"));
    assert_eq!(unit.fns.len(), 1);
    let f = &unit.fns[0];
    assert_eq!((f.fn_.as_str(), f.symbol.as_str(), f.header.as_str()), ("m.f", "vc_f", "vc_pk.h"));
    assert_eq!(f.ret.as_deref(), Some("int32_t"));
    let params: Vec<(&str, &str, &str, crate::FnParamKind)> = f
        .params
        .iter()
        .map(|p| (p.field.name.as_str(), p.field.c_name.as_str(), p.field.c_type.as_str(), p.kind))
        .collect();
    assert_eq!(
        params,
        [("x", "x", "int32_t", crate::FnParamKind::Scalar), ("y", "y", "int32_t", crate::FnParamKind::Scalar)]
    );
    let header = &unit.headers.iter().find(|(n, _)| n == "vc_pk.h").expect("the header").1;
    assert!(header.contains("int32_t vc_f(int32_t x, int32_t y);"), "{header}");
    assert_eq!(unit.take_panic.as_deref(), Some("vc_take_panic"));
    assert!(header.contains("int vc_take_panic(void);"), "{header}");
    let trap = emit(&m, &EmitOptions { panic: crate::PanicMode::Trap, ..opts }).unwrap_or_else(|d| panic!("{d:?}"));
    assert_eq!(trap.take_panic, None);
}

/// The `onsa_panic` of `mode` in the runtime header: the text of its branch
/// of the `#if defined(ONSA_PANIC_POISON)` chain.
fn panic_branch(header: &str, mode: crate::PanicMode) -> &str {
    let start = |marker: &str| header.find(marker).unwrap_or_else(|| panic!("`{marker}` is not in onsa.h"));
    let (from, to) = match mode {
        crate::PanicMode::Poison => ("#if defined(ONSA_PANIC_POISON)", "#elif defined(ONSA_PANIC_RESET)"),
        crate::PanicMode::Reset => ("#elif defined(ONSA_PANIC_RESET)", "#elif defined(ONSA_PANIC_HALT)"),
        crate::PanicMode::Halt => ("#elif defined(ONSA_PANIC_HALT)", "#else /* ONSA_PANIC_TRAP (default) */"),
        crate::PanicMode::Trap => ("#else /* ONSA_PANIC_TRAP (default) */", "/* ---- bounds checks"),
    };
    let (a, b) = (start(from), start(to));
    assert!(a < b, "the branches of onsa_panic are out of order in onsa.h");
    &header[a..b]
}

/// R-10 (plan decision; the spec does not word it, W2-05/t): under
/// `panic = "trap"` / `"reset"` a checked operation is a comparison and a
/// branch to the trap or the reset hook. The generated C has no `setjmp`
/// machinery, the panic is the trap / the hook alone, and the checks of
/// `+ - *` are the compiler's overflow builtins followed by that branch.
#[test]
fn checks_under_trap_and_reset_are_a_compare_and_a_branch() {
    let i32t = Ty::Int(IntKind::I32);
    let body = binary(
        BinOp::Mul,
        Overflow::Checked,
        i32t.clone(),
        binary(BinOp::Add, Overflow::Checked, i32t.clone(), local(0, i32t.clone()), local(1, i32t.clone())),
        local(1, i32t.clone()),
    );
    let m = one_fn(i32t, body, vec![]);
    let header = crate::runtime_header();
    for (mode, define, panic_body) in [
        (crate::PanicMode::Trap, "#define ONSA_PANIC_TRAP", "__builtin_trap();"),
        (crate::PanicMode::Reset, "#define ONSA_PANIC_RESET", "onsa_reset_hook();"),
    ] {
        let opts = EmitOptions { export_fns: vec!["m.f".into()], panic: mode, ..Default::default() };
        let unit = emit(&m, &opts).unwrap_or_else(|d| panic!("{d:?}"));
        assert!(unit.source.contains(define), "{mode:?}: {}", unit.source);
        assert!(unit.source.contains("onsa_mul_i32(onsa_add_i32(x, y, \"\", 0), y, \"\", 0)"), "{}", unit.source);
        for (name, text) in std::iter::once(("the source", unit.source.as_str()))
            .chain(unit.headers.iter().map(|(n, t)| (n.as_str(), t.as_str())))
        {
            for word in ["setjmp", "longjmp", "jmp_buf", "onsa_current_jmp"] {
                assert!(!text.contains(word), "{mode:?}: `{word}` in {name}:\n{text}");
            }
        }
        assert_eq!(unit.runtime_header, header);
        let branch = panic_branch(&header, mode);
        assert!(branch.contains(panic_body), "{mode:?}:\n{branch}");
        for word in ["setjmp", "longjmp", "onsa_current_jmp"] {
            assert!(!branch.contains(word), "{mode:?}: `{word}` in its onsa_panic:\n{branch}");
        }
    }
    // The setjmp machinery is the poison branch's alone.
    let poison = panic_branch(&header, crate::PanicMode::Poison);
    assert_eq!(header.matches("#include <setjmp.h>").count(), 1);
    assert!(poison.contains("#include <setjmp.h>"), "{poison}");
    assert_eq!(header.matches("longjmp(").count(), 1);
    assert!(poison.contains("longjmp("), "{poison}");
    // The checks: the builtins, and a branch to onsa_panic on their result.
    for (op, builtin) in [("cadd", "add"), ("csub", "sub"), ("cmul", "mul")] {
        let check = format!(
            "ONSA_INLINE bool onsa_{op}_##N(T a, T b, T* r) {{ return !__builtin_{builtin}_overflow(a, b, r); }}"
        );
        assert!(header.contains(&check), "no `{check}` in onsa.h");
        assert!(header.contains(&format!("if (!onsa_{op}_##N(a, b, &r)) onsa_panic(")), "the panic of {op}");
    }
    // Every integer type takes the builtins when the compiler has them.
    let builtins = &header[header.find("#if ONSA_HAS_BUILTIN_OVERFLOW").expect("the builtin branch")..];
    let builtins = &builtins[..builtins.find("#else").expect("its end")];
    assert!(builtins.contains("#define ONSA_INT_CHECKED_64 ONSA_INT_CHECKED"), "{builtins}");
}

/// Plan D-15, S-106: the bits `to_bits()` gives for a NaN are written into
/// `onsa.h` from onsa_core's constants, the ones the interpreter reads.
#[test]
fn the_runtime_header_takes_the_nan_bits_from_core() {
    use onsa_core::prim::{NAN_BITS_F32, NAN_BITS_F64};
    assert_eq!(crate::RUNTIME_HEADER_SOURCE.matches(crate::CONSTANTS_MARKER).count(), 1);
    let header = crate::runtime_header();
    assert!(!header.contains(crate::CONSTANTS_MARKER), "the marker is left in onsa.h");
    let value = |name: &str, wrap: &str| -> u64 {
        let line = header
            .lines()
            .find(|l| l.starts_with(&format!("#define {name} ")))
            .unwrap_or_else(|| panic!("no `#define {name}` in onsa.h"));
        let v = line[format!("#define {name} ").len()..].trim();
        let hex = v.strip_prefix(&format!("{wrap}(0x")).and_then(|h| h.strip_suffix(')')).unwrap_or(v);
        u64::from_str_radix(hex, 16).unwrap_or_else(|e| panic!("`{line}`: {e}"))
    };
    assert_eq!(value("ONSA_NAN_BITS_F32", "UINT32_C"), u64::from(NAN_BITS_F32));
    assert_eq!(value("ONSA_NAN_BITS_F64", "UINT64_C"), NAN_BITS_F64);
    // The definitions come before onsa.h's check of them and its use of them.
    let defined = header.find("#define ONSA_NAN_BITS_F32").expect("the definition");
    assert!(defined < header.find("#if !defined(ONSA_NAN_BITS_F32)").expect("the check"));
    assert!(defined < header.find("return ONSA_NAN_BITS_F32;").expect("the use"));
}

/// R-11: `narrow_*` from an unsigned type compares the upper bound alone, in
/// the source's own type (a signed lower bound converted to unsigned made
/// every value fall outside); from a signed type it compares both bounds.
#[test]
fn narrow_from_unsigned_compares_the_upper_bound_alone() {
    let opt = TypeDef {
        name: "m.Opt".into(),
        kind: TypeDefKind::Enum {
            variants: vec![("None".into(), vec![]), ("Some".into(), vec![Ty::Int(IntKind::I32)])],
        },
    };
    for (from, fits) in [
        (IntKind::U32, "if (onsa_t1 <= (uint32_t)INT32_MAX) {"),
        (IntKind::U64, "if (onsa_t1 <= (uint64_t)INT32_MAX) {"),
        (IntKind::I64, "if (onsa_t1 >= INT32_MIN && onsa_t1 <= INT32_MAX) {"),
    ] {
        let narrow = e(
            Ty::Enum(TypeId(0)),
            ExprKind::Prim {
                prim: onsa_core::prim::Prim::Narrow { from, to: IntKind::I32 },
                args: vec![Arg { mode: Mode::Borrow, expr: local(0, Ty::Int(from)) }],
            },
        );
        let m = Module {
            types: vec![opt.clone()],
            consts: Vec::new(),
            fns: vec![FnDef {
                name: "m.f".into(),
                params: vec![Param { local: LocalId(0), mode: Mode::Borrow, ty: Ty::Int(from) }],
                ret: Ty::Int(IntKind::I32),
                sret: false,
                rt: true,
                locals: vec![
                    Local { name: "x".into(), ty: Ty::Int(from) },
                    Local { name: "v".into(), ty: Ty::Enum(TypeId(0)) },
                ],
                body: Some(Block {
                    stmts: vec![Stmt { span: sp(), kind: StmtKind::Let(LocalId(1), narrow) }],
                    value: Some(Box::new(e(
                        Ty::Int(IntKind::I32),
                        ExprKind::Tag(Box::new(local(1, Ty::Enum(TypeId(0))))),
                    ))),
                }),
                span: sp(),
                test: None,
            }],
            messages: Vec::new(),
            flows: Vec::new(),
            moves: Vec::new(),
        };
        let c = emit_fn(&m);
        assert!(c.contains(fits), "{from:?}: {c}");
        if !from.signed() {
            assert!(!c.contains("INT32_MIN"), "{from:?}: {c}");
        }
    }
}
