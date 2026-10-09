//! The stack of the interpreter (R-05, R-112, spec §12.5, S-222): the call
//! depth limit over Onsa source, the safety net under it, and the thread every
//! run goes on. The limit counts the calls nested in one evaluation, whose
//! entry (the body of a `test`, a function called from outside, a `const`
//! initializer) is depth 0: `f(n)` called from outside makes `n` nested calls,
//! and from the body of a `test`, `n + 1`.

use onsa_diag::stack::{STACK_SIZE, with_stack_left};
use onsa_interp::{Interp, MAX_CALL_DEPTH, STACK_RESERVE, Value};

/// A one-module package `t`, checked and lowered, on the stack of a command
/// (the front end recurses over the nesting of the source).
fn lower(src: &str) -> onsa_core::Module {
    onsa_diag::stack::run(|| lower_here(src))
}

/// `onsa test`'s report of every test of `module`, which holds nothing the
/// interpreter cannot run.
fn tests_of(module: &onsa_core::Module) -> onsa_driver::TestReport {
    match onsa_driver::run_tests(&onsa_diag::SourceMap::default(), module, &onsa_driver::TestOptions::default()) {
        Ok(onsa_driver::TestRun::Ran(r)) => r,
        other => panic!("the tests did not run: {other:?}"),
    }
}

fn lower_here(src: &str) -> onsa_core::Module {
    let input = onsa_driver::PackageInput {
        manifest: None,
        files: vec![onsa_driver::SourceFile { path: "t.onsa".into(), text: src.into() }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)))
}

/// The recursive shapes of `tests/spec/semantics/recursion_deep.onsa`: each
/// `t.<name>(n)` recurses `n` levels deep.
const SHAPES: &str = "
pub fn dive(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    1 + dive(n - 1)
  }
}

pub fn dive_tail(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    dive_tail(n - 1)
  }
}

pub fn dive_nested(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    dive_nested(dive_nested(0) + n - 1)
  }
}

pub fn dive_match(n: U32) -> U32 {
  let o: Option[U32] = if n == 0 {
    None
  } else {
    Some(n - 1)
  }
  match o {
    Some(k) => 1 + dive_match(k),
    None => 0,
  }
}

fn dive_for_go(n: U32) {
  if n > 0 {
    for i in 0..<1 {
      dive_for_go(n - 1 + i)
    }
  }
}

pub fn dive_for(n: U32) -> U32 {
  dive_for_go(n)
  0
}

fn dive_inout_go(inout x: U32, n: U32) {
  if n > 0 {
    x = 1
    dive_inout_go(inout x, n - 1)
  }
}

pub fn dive_inout(n: U32) -> U32 {
  var x: U32 = 0
  dive_inout_go(inout x, n)
  x
}

pub fn is_even(n: U32) -> U32 {
  if n == 0 {
    1
  } else {
    is_odd(n - 1)
  }
}

pub fn is_odd(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    is_even(n - 1)
  }
}

// The call under a `while`, a `match`, an `if` and a block, as an operand.
pub fn nested(n: U32) -> U32 {
  var r: U32 = 0
  var go = true
  while go {
    go = false
    let o: Option[U32] = Some(n)
    match o {
      Some(k) => {
        if k > 0 {
          let s = {
            let t = 2 * (1 + nested(k - 1))
            t / 2
          }
          r = s
        }
      },
      None => {},
    }
  }
  r
}

pub fn sqrt_chain(n: U32) -> U32 {
  if n == 0 {
    0
  } else {
    let x: F64 = (sqrt_chain(n - 1) as F64).sqrt()
    1
  }
}
";

const NAMES: [&str; 9] =
    ["dive", "dive_tail", "dive_nested", "dive_match", "dive_for", "dive_inout", "is_even", "sqrt_chain", "nested"];

/// `t.<name>(depth)` called from outside on the stack of a command, with
/// `left` bytes of its stack left when given (`with_stack_left`): the result,
/// or the internal error.
fn run_left(
    module: &onsa_core::Module,
    name: &str,
    depth: u32,
    left: Option<usize>,
) -> Result<Result<Option<i128>, onsa_interp::Failure>, onsa_driver::InternalError> {
    onsa_driver::guard_on_stack(|| {
        let go = || {
            let interp = Interp::new(module);
            let f = interp.fn_by_name(&format!("t.{name}")).unwrap_or_else(|| panic!("no `{name}`"));
            interp.call(f, vec![Value::U32(depth)]).map(|v| v.to_i128())
        };
        match left {
            Some(left) => with_stack_left(left, go),
            None => go(),
        }
    })
}

/// [`run_left`] on the whole stack; an internal error fails the test.
fn run(module: &onsa_core::Module, name: &str, depth: u32) -> Result<Option<i128>, onsa_interp::Panic> {
    match run_left(module, name, depth, None) {
        Ok(Ok(v)) => Ok(v),
        Ok(Err(onsa_interp::Failure::Panic(p))) => Err(p),
        Ok(Err(f)) => panic!("`{name}({depth})`: {f:?}"),
        Err(e) => panic!("`{name}({depth})` is an internal error: {}", e.message),
    }
}

/// The largest `n` for which `t.<name>(n)`, called from outside, stays within
/// the limit: it makes `n` nested calls, and `dive_for` and `dive_inout` one
/// more (the call of their `_go`). In `dive_nested`, the inner
/// `dive_nested(0)` ends before the outer call starts, so it is not nested in
/// it and adds nothing.
fn deepest(name: &str) -> u32 {
    match name {
        "dive_for" | "dive_inout" => MAX_CALL_DEPTH - 1,
        _ => MAX_CALL_DEPTH,
    }
}

/// The rule of [`MAX_CALL_DEPTH`] over source: every shape, as deep as the
/// limit lets it go, fits in half of the stack the safety net leaves (R-05).
#[test]
fn every_shape_fits_at_the_limit_with_half_the_stack_to_spare() {
    let module = lower(SHAPES);
    let half = STACK_RESERVE + (STACK_SIZE - STACK_RESERVE) / 2;
    for name in NAMES {
        let r = run_left(&module, name, deepest(name), Some(half));
        assert!(matches!(r, Ok(Ok(_))), "{name}: {r:?}");
    }
}

/// Spec §12.5: a call beyond the limit is a panic of the program at the call,
/// for every shape, however deep the program asks (the depth in the panic is
/// the limit, not the request); never the safety net.
#[test]
fn beyond_the_limit_is_a_panic_of_the_program() {
    let module = lower(SHAPES);
    let message = format!("the call depth reached its limit of {MAX_CALL_DEPTH}");
    for name in NAMES {
        for depth in [deepest(name) + 1, deepest(name) + 2, 10_000_000] {
            let p = run(&module, name, depth).expect_err(name);
            assert_eq!(p.message, message, "{name}({depth})");
        }
    }
}

/// The boundary, from outside: `dive_tail(n)` makes `n` nested calls, a tail
/// call counted as any other.
#[test]
fn the_limit_is_exact() {
    let module = lower(SHAPES);
    assert_eq!(run(&module, "dive_tail", MAX_CALL_DEPTH).unwrap(), Some(0));
    assert!(run(&module, "dive_tail", MAX_CALL_DEPTH + 1).is_err());
}

/// The panic names the call that went beyond the limit (spec §9.2: a panic
/// names its position), in `onsa test`'s report.
#[test]
fn the_panic_is_at_the_call() {
    let src = "fn dive(n: U32) -> U32 {\n  if n == 0 {\n    0\n  } else {\n    1 + dive(n - 1)\n  }\n}\n\ntest \"deep\" {\n  assert dive(10000000) == 10000000\n}\n";
    let module = lower(src);
    let report = tests_of(&module);
    let t = &report.tests[0];
    assert_eq!(t.message(), Some(format!("the call depth reached its limit of {MAX_CALL_DEPTH}").as_str()));
    let span = t.failure.as_ref().expect("a failure").span;
    assert_eq!(&src[span.start as usize..span.end as usize], "dive(n - 1)");
}

/// A `const` initializer that recurses beyond the limit: a panic of the
/// evaluation (S-222), in `onsa test` (the test that reads it fails) and from
/// outside, as a build reads it (no internal error). E0419 is W9-03's.
#[test]
fn a_const_beyond_the_limit_is_a_panic_of_the_evaluation() {
    let src = "fn dive(n: U32) -> U32 {\n  if n == 0 {\n    0\n  } else {\n    1 + dive(n - 1)\n  }\n}\n\nconst DEEP: U32 = dive(10000000)\n\ntest \"reads it\" {\n  assert DEEP == 10000000\n}\n";
    let module = lower(src);
    let report = tests_of(&module);
    let message = format!("the call depth reached its limit of {MAX_CALL_DEPTH}");
    assert_eq!(report.tests[0].message(), Some(message.as_str()));
    let r = onsa_driver::guard_on_stack(|| {
        let interp = Interp::new(&module);
        interp.const_value(onsa_core::ConstId(0)).map(|_| ())
    })
    .unwrap();
    assert!(matches!(r, Err(onsa_interp::Failure::Panic(p)) if p.message == message));
}

/// R-05's input (`tests/review-phase1/core/deep_*.onsa`): `depth(200)` ended
/// the debug build of `onsa test` by SIGABRT, and no other test reported.
/// Through `onsa test`'s path, with the limit of 128 (S-222): `depth(n)` from
/// the body of a test makes `n + 1` nested calls, so 50, 100 and 127 pass,
/// and 128 and the depths of the inputs beyond it (200 to 5000) fail their
/// test only.
#[test]
fn r05_recursion_below_the_limit_passes_in_onsa_test() {
    let mut src = String::from("fn depth(n: U32) -> U32 {\n  if n == 0 { 0 } else { depth(n - 1) + 1 }\n}\n");
    let below = [50u32, 100, MAX_CALL_DEPTH - 1];
    let beyond = [MAX_CALL_DEPTH, 200, 300, 400, 500, 1000, 2000, 3000, 5000];
    for n in below.iter().chain(&beyond) {
        src.push_str(&format!("\ntest \"recursion {n} deep\" {{\n  assert depth({n}) == {n}\n}}\n"));
    }
    let module = lower(&src);
    let report = tests_of(&module);
    assert_eq!(report.tests.len(), below.len() + beyond.len());
    // The report is ordered by name (§18.1), so each test is found by its name.
    for n in below.iter().chain(&beyond) {
        let name = format!("recursion {n} deep");
        let t = report.tests.iter().find(|t| t.name == name).unwrap_or_else(|| panic!("no test {name:?}"));
        assert_eq!(t.message().is_none(), below.contains(n), "{}: {:?}", t.name, t.message());
    }
}
