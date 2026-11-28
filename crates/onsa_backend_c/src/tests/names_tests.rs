//! The C names of the types (`names.rs`) and the types read through them:
//! definitions in the order of their dependencies, registered on a stack of
//! their own (R-319), the tags of the synthetic types, the type of the tag
//! of an enum, and the type of an element of a tuple place.

use std::collections::HashMap;

use onsa_core::*;

use super::{e, lit_f32, lit_i32, local, sp};
use crate::emit::Cx;
use crate::names::{Entry, TypeNames};
use crate::{EmitOptions, emit};

fn module(tys: Types, types: Vec<TypeDef>) -> Module {
    Module { tys, types, ..Module::default() }
}

fn cx<'m>(m: &'m Module, opts: &'m EmitOptions) -> Cx<'m> {
    Cx {
        m,
        opts,
        names: TypeNames::new(m),
        bulk: HashMap::new(),
        fn_names: HashMap::new(),
        const_names: HashMap::new(),
        exports: Vec::new(),
        header_params: HashMap::new(),
        guarded_names: HashMap::new(),
    }
}

/// `m.S<i> { a: S<i+1>, t: ([F32; 2], S<i+1>) }` down to a last `{ x: U32 }`:
/// each definition after the types of its fields, an array before the tuple
/// that holds it.
fn chain(n: u32) -> Module {
    let mut tys = Types::default();
    let arr = tys.intern(TyKind::Array(Types::float(FloatKind::F32), 2));
    let mut types = Vec::new();
    for i in 0..n {
        let kind = if i + 1 == n {
            TypeDefKind::Struct { fields: vec![("x".into(), Types::U32)] }
        } else {
            let next = tys.intern(TyKind::Struct(TypeId(i + 1)));
            let pair = tys.intern(TyKind::Tuple(Box::new([arr, next])));
            TypeDefKind::Struct { fields: vec![("a".into(), next), ("t".into(), pair)] }
        };
        types.push(TypeDef { name: format!("m.S{i}"), kind });
    }
    module(tys, types)
}

#[test]
fn definitions_come_after_the_types_of_their_fields() {
    let m = chain(3);
    let mut names = TypeNames::new(&m);
    assert_eq!(names.def(TypeId(0)), "m__S0");
    let order: Vec<String> = names
        .order
        .iter()
        .map(|e| match e {
            Entry::Def(id) => m.ty(*id).name.clone(),
            Entry::Synth(_, n) => n.clone(),
        })
        .collect();
    let want = ["m.S2", "onsa_arr_f32_2", "onsa_tup_arr_f32_2_m__S2", "m.S1", "onsa_tup_arr_f32_2_m__S1", "m.S0"];
    assert_eq!(order, want);
}

/// The registration of a chain of 10000 definitions takes no stack of Rust:
/// on the thread of a command, as `onsa build` runs it.
#[test]
fn a_chain_of_ten_thousand_definitions_is_registered() {
    let len = onsa_diag::stack::spawn("chain", || {
        let m = chain(10000);
        let mut names = TypeNames::new(&m);
        names.def(TypeId(0));
        names.order.len()
    });
    assert_eq!(len.unwrap().join().unwrap(), 10000 + 1 + 9999);
}

/// The members of the tag of a tuple are apart: `(I32, U8)` and `(I32U8)`
/// would be one name.
#[test]
fn the_tag_of_a_tuple_separates_its_members() {
    let mut tys = Types::default();
    let t = tys.intern(TyKind::Tuple(Box::new([Types::int(IntKind::I32), Types::int(IntKind::U8)])));
    let m = module(tys, Vec::new());
    assert_eq!(TypeNames::new(&m).tag(t), "tup_i32_u8");
}

/// The tag of an enum is the smallest type of its count of variants: 256
/// fit a `uint8_t`.
#[test]
fn the_tag_of_an_enum_of_256_variants_is_a_byte() {
    let of = |n: u32| TypeDef {
        name: format!("m.E{n}"),
        kind: TypeDefKind::Enum { variants: (0..n).map(|i| (format!("V{i}"), Vec::new())).collect() },
    };
    let m = module(Types::default(), vec![of(256), of(257), of(65536), of(65537)]);
    let opts = EmitOptions::default();
    let cx = cx(&m, &opts);
    let tags: Vec<&str> = (0..4).map(|i| cx.tag_c(TypeId(i))).collect();
    assert_eq!(tags, ["uint8_t", "uint16_t", "uint16_t", "uint32_t"]);
}

/// The type of a place `t.1[0]` is of the second element of `t`: an array,
/// which is indexed, not the `I32` of the first.
#[test]
fn the_place_of_an_element_of_a_tuple_has_its_type() {
    let mut tys = Types::default();
    let (i32t, f32t) = (Types::int(IntKind::I32), Types::float(FloatKind::F32));
    let arr = tys.intern(TyKind::Array(f32t, 4));
    let pair = tys.intern(TyKind::Tuple(Box::new([i32t, arr])));
    let init =
        e(pair, ExprKind::Tuple(vec![lit_i32(1), e(arr, ExprKind::Repeat { elem: Box::new(lit_f32(0.0)), n: 4 })]));
    let zero = e(Types::U32, ExprKind::Lit(Lit::Int(0)));
    let at = Place::Index(
        Box::new(Place::Field(Box::new(Place::Local(LocalId(0))), 1)),
        Box::new(zero),
        sp(),
        Bounds::Checked,
    );
    let stmts = vec![
        Stmt { span: sp(), kind: StmtKind::Let(LocalId(0), init) },
        Stmt { span: sp(), kind: StmtKind::Assign(at, lit_f32(1.0)) },
    ];
    let first = e(i32t, ExprKind::Field { base: Box::new(local(0, pair)), index: 0 });
    let f = FnDef {
        name: "m.f".into(),
        params: Vec::new(),
        ret: i32t,
        sret: false,
        rt: true,
        locals: vec![Local::value("t", pair)],
        body: Some(Block { stmts, value: Some(Box::new(first)) }),
        span: sp(),
        fp_relaxed: false,
        test: None,
        decl: None,
        hoisted: Vec::new(),
    };
    let m = Module { fns: vec![f], ..module(tys, Vec::new()) };
    let opts = EmitOptions { prefix: Some("t_".into()), export_fns: vec!["m.f".into()], ..Default::default() };
    let c = emit(&m, &opts).unwrap_or_else(|d| panic!("{d:?}")).source;
    assert!(c.contains(".f1.a["), "{c}");
}

/// The members of a tuple are registered in their order, each new struct
/// before the next: `(m.A, m.B)` defines `m.A`, `m.B`, then the tuple.
#[test]
fn the_new_members_of_a_tuple_are_defined_in_their_order() {
    let mut tys = Types::default();
    let (a, b) = (tys.intern(TyKind::Struct(TypeId(0))), tys.intern(TyKind::Struct(TypeId(1))));
    let pair = tys.intern(TyKind::Tuple(Box::new([a, b])));
    let field = |n: &str| TypeDefKind::Struct { fields: vec![(n.into(), Types::U32)] };
    let types =
        vec![TypeDef { name: "m.A".into(), kind: field("x") }, TypeDef { name: "m.B".into(), kind: field("y") }];
    let m = module(tys, types);
    let mut names = TypeNames::new(&m);
    names.name(pair);
    let order: Vec<String> = names
        .order
        .iter()
        .map(|e| match e {
            Entry::Def(id) => m.ty(*id).name.clone(),
            Entry::Synth(_, n) => n.clone(),
        })
        .collect();
    assert_eq!(order, ["m.A", "m.B", "onsa_tup_m__A_m__B"]);
}

/// A `Span` and a `Buf` of one element have two tags, in one unit.
#[test]
fn a_span_and_a_buf_of_one_element_have_two_tags() {
    let mut tys = Types::default();
    let span = tys.intern(TyKind::Span(Types::int(IntKind::U8)));
    let buf = tys.intern(TyKind::Buf(Types::int(IntKind::U8)));
    let m = module(tys, Vec::new());
    let mut names = TypeNames::new(&m);
    assert_eq!([names.tag(span), names.tag(buf)], ["span_u8", "buf_u8"]);
}
