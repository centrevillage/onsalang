//! A `panic` put between the statements of a block leaves the diagnostics of a program as they are (spec
//! §9.2, §12.2, §10 rule 4, §7; S-873; W6-02 U0b/t). A panic leaves by a way on which no value that is
//! alive is dropped (§9.2: no unwinding, and what is dropped on the way is not counted for `Alloc`, §12.2),
//! and the prelude's `panic` is an `rt` function (S-873), so that a program the check passes cannot
//! gain an `Alloc` error (E0601) or a call of a function that is not `rt` in an `rt` function (E0901)
//! from a `panic` in a place that was reached before. The tests are the guard of the units that read the
//! ways out of a block (the drop points of an owned value, W6-02 U2a to U7): a drop point put on a way
//! that a `panic` ends, or a state that meets a way that does not arrive, would make the check change.
//!
//! The input: the programs of `tests/spec` that carry no mark (`//~`, `#~`), are not in a package and
//! pass `check` with no diagnostic, 60 of them from a fixed seed, and more until 20 of them have an
//! `rt fn`. The places: the borders between the statements of the blocks of the functions, the methods and the anonymous functions of each (the
//! start of a block, after each statement), found in the syntax tree; no border follows a statement
//! that diverges (§7: `return`, `break`, `continue`, `panic`, a block, an `if` or a `match` that all
//! end so, a `while true` that is not left by a `break`), which would be E0503.
//!
//! Property 1: `\nif false {\npanic("x") }\n` put at a border leaves the program with no diagnostic (the
//! program has none, so that the set of the diagnostics with their positions put back is the empty
//! set). Property 2: `\npanic("x")\n` put after the last statement of a block that has no final
//! expression leaves the program with no E0601 and no E0901 (another diagnostic is not looked at: a way
//! that no longer arrives may remove an error). A form that gets E0503 there is out of the property and
//! is counted. The checks run in this process (`check_input`), with no file written (`rules/common.md`
//! 3.7); a failure names the file, the property, the place (line and column in the program as it was),
//! the seed and the diagnostics after.

use std::path::{Path, PathBuf};

use onsa_diag::FileId;
use onsa_driver::PackageInput;
use onsa_syntax::ast::{Ast, ExprId, ExprKind, ItemKind, Lit, StmtId, StmtKind};

use crate::test_support::sweep::*;

const SEED: u64 = 0x0b02_0602;
/// How many programs are taken.
const PROGRAMS: usize = 60;
/// At least this many of the programs have an `rt fn` (the places where E0601 and E0901 are decided).
const RT_PROGRAMS: usize = 20;
/// How many borders of each program property 1 puts the panic at, and how many ends property 2 does.
const BORDERS: usize = 4;
const ENDS: usize = 3;

/// Put at a border (property 1): the `if` has no `else`, so the way that does not panic is as before.
const INSERT_BORDER: &str = "\nif false {\npanic(\"x\") }\n";
/// Put after the last statement of a block that has no final expression (property 2).
const INSERT_END: &str = "\npanic(\"x\")\n";

fn spec_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec")
}

/// The `.onsa` files under `dir`, sorted by path, with no directory that holds an `onsa.toml` (a package
/// is not one file).
fn onsa_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> =
        std::fs::read_dir(dir).expect("read a directory").map(|e| e.expect("an entry").path()).collect();
    entries.sort();
    if entries.iter().any(|p| p.file_name().is_some_and(|n| n == "onsa.toml")) {
        return;
    }
    for p in entries {
        if p.is_dir() {
            onsa_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "onsa") {
            out.push(p);
        }
    }
}

/// A place in the text: the 1-based line and the column in characters.
fn line_col(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

fn is_path_named(ast: &Ast, e: ExprId, name: &str) -> bool {
    matches!(&ast.expr(e).kind, ExprKind::Path(p) if p.segments.len() == 1 && p.segments[0].name == name)
}

/// Whether a `break` of the loop of `body` is in it (one of an inner loop is of that loop).
fn has_break(ast: &Ast, e: ExprId) -> bool {
    let ExprKind::Block(b) = &ast.expr(e).kind else {
        return ast.sub_exprs(e).into_iter().any(|x| has_break(ast, x));
    };
    for &s in &b.stmts {
        match &ast.stmt(s).kind {
            StmtKind::Break => return true,
            // An inner loop's own `break` is not this loop's; its head and the rest are looked at.
            StmtKind::While { cond, .. } => {
                if has_break(ast, *cond) {
                    return true;
                }
            }
            StmtKind::For { iter, .. } => {
                if has_break(ast, *iter) {
                    return true;
                }
            }
            StmtKind::Let { init, .. } | StmtKind::Var { init, .. } => {
                if has_break(ast, *init) {
                    return true;
                }
            }
            StmtKind::Assign { target, value } => {
                if has_break(ast, *target) || has_break(ast, *value) {
                    return true;
                }
            }
            StmtKind::Return(Some(x)) | StmtKind::Assert(x) | StmtKind::Expr(x) => {
                if has_break(ast, *x) {
                    return true;
                }
            }
            StmtKind::Return(None) | StmtKind::Continue => {}
        }
    }
    b.tail.is_some_and(|t| has_break(ast, t))
}

/// Whether an expression diverges by its structure alone (§7).
fn diverges(ast: &Ast, e: ExprId) -> bool {
    match &ast.expr(e).kind {
        ExprKind::Call { callee, args, .. } => is_path_named(ast, *callee, "panic") && args.len() == 1,
        ExprKind::Paren(x) | ExprKind::Unsafe(x) => diverges(ast, *x),
        ExprKind::Block(b) => {
            b.stmts.iter().any(|&s| stmt_diverges(ast, s)) || b.tail.is_some_and(|t| diverges(ast, t))
        }
        ExprKind::If { then, else_: Some(else_), .. } => diverges(ast, *then) && diverges(ast, *else_),
        ExprKind::Match { arms, .. } => !arms.is_empty() && arms.iter().all(|a| diverges(ast, a.body)),
        _ => false,
    }
}

fn stmt_diverges(ast: &Ast, s: StmtId) -> bool {
    match &ast.stmt(s).kind {
        StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue => true,
        StmtKind::Expr(x) => diverges(ast, *x),
        StmtKind::Let { init, .. } | StmtKind::Var { init, .. } => diverges(ast, *init),
        StmtKind::While { cond, body } => {
            let mut c = *cond;
            while let ExprKind::Paren(x) = &ast.expr(c).kind {
                c = *x;
            }
            matches!(&ast.expr(c).kind, ExprKind::Lit(Lit::Bool(true))) && !has_break(ast, *body)
        }
        StmtKind::Assign { .. } | StmtKind::For { .. } | StmtKind::Assert(_) => false,
    }
}

/// The places of a program: the byte offsets of its borders and of the ends of its blocks that have no
/// final expression.
#[derive(Default)]
struct Places {
    borders: Vec<usize>,
    ends: Vec<usize>,
}

fn collect_blocks(ast: &Ast, text: &str, e: ExprId, out: &mut Places) {
    if let ExprKind::Block(b) = &ast.expr(e).kind {
        let span = ast.expr(e).span;
        let (start, end) = (span.start as usize, span.end as usize);
        // Only a block written with its braces, which is every block of a body.
        if text.as_bytes().get(start) == Some(&b'{') && end > start && text.as_bytes().get(end - 1) == Some(&b'}') {
            out.borders.push(start + 1);
            for (i, &s) in b.stmts.iter().enumerate() {
                if stmt_diverges(ast, s) {
                    continue;
                }
                let at = ast.stmt(s).span.end as usize;
                out.borders.push(at);
                if i + 1 == b.stmts.len() && b.tail.is_none() {
                    out.ends.push(at);
                }
            }
        }
    }
    for x in ast.sub_exprs(e) {
        collect_blocks(ast, text, x, out);
    }
}

fn places_of(text: &str) -> Places {
    let parsed = onsa_syntax::parse(FileId(0), text);
    let ast = &parsed.ast;
    let mut out = Places::default();
    for item in &ast.items {
        if item.failed.is_some() {
            continue;
        }
        let mut kind = &item.kind;
        while let ItemKind::Target(inner) = kind {
            kind = inner;
        }
        if let ItemKind::Fn(f) = kind {
            if let Some(body) = f.body {
                collect_blocks(ast, text, body, &mut out);
            }
        }
    }
    out.borders.sort_unstable();
    out.borders.dedup();
    out.ends.sort_unstable();
    out.ends.dedup();
    out
}

fn check_text(name: &str, text: &str) -> Checked {
    check_input(&PackageInput::single_file(name, text))
}

fn shown(c: &Checked) -> String {
    if !ended_well(c) {
        return format!("exit {}: {}", c.code, c.stderr);
    }
    c.diags
        .iter()
        .map(|d| format!("    {} at {}:{}:{}: {}", d.code, d.file, d.line, d.col, d.message))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn a_panic_between_the_statements_of_a_block_leaves_the_diagnostics_as_they_are() {
    onsa_diag::stack::run(run_sweep);
}

fn run_sweep() {
    let root = spec_dir();
    let mut files = Vec::new();
    onsa_files(&root, &mut files);
    let mut rng = Rng::new(SEED);
    rng.shuffle(&mut files);

    let (mut taken, mut border_runs, mut end_runs, mut end_skipped, mut with_rt) = (0, 0, 0, 0, 0);
    let mut failed: Vec<String> = Vec::new();
    for path in &files {
        if taken >= PROGRAMS && with_rt >= RT_PROGRAMS {
            break;
        }
        let Ok(text) = std::fs::read_to_string(path) else { continue };
        if text.contains("//~") || text.contains("#~") {
            continue;
        }
        let has_rt = text.contains("rt fn");
        // The programs past the first `PROGRAMS` are the ones with an `rt fn`, up to `RT_PROGRAMS` of them.
        if taken >= PROGRAMS && !has_rt {
            continue;
        }
        let rel = path.strip_prefix(&root).unwrap().to_string_lossy().into_owned();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let base = check_text(&name, &text);
        if !ended_well(&base) || !base.diags.is_empty() {
            continue;
        }
        let mut places = places_of(&text);
        if places.borders.is_empty() {
            continue;
        }
        taken += 1;
        with_rt += usize::from(has_rt);
        rng.shuffle(&mut places.borders);
        rng.shuffle(&mut places.ends);
        for &at in places.borders.iter().take(BORDERS) {
            let mut after = text.clone();
            after.insert_str(at, INSERT_BORDER);
            border_runs += 1;
            let c = check_text(&name, &after);
            if !ended_well(&c) || !c.diags.is_empty() {
                let (line, col) = line_col(&text, at);
                failed.push(format!(
                    "property 1: {rel} (seed {SEED:#x}), border at {line}:{col} (offset {at}); diagnostics after, with the positions of the text after the insertion:\n{}",
                    shown(&c)
                ));
            }
        }
        for &at in places.ends.iter().take(ENDS) {
            let mut after = text.clone();
            after.insert_str(at, INSERT_END);
            let c = check_text(&name, &after);
            if !ended_well(&c) {
                end_runs += 1;
                let (line, col) = line_col(&text, at);
                failed.push(format!("property 2: {rel} (seed {SEED:#x}), end at {line}:{col}: {}", shown(&c)));
                continue;
            }
            if !c.of_code("E0503").is_empty() {
                end_skipped += 1;
                continue;
            }
            end_runs += 1;
            if c.diags.iter().any(|d| d.code == "E0601" || d.code == "E0901") {
                let (line, col) = line_col(&text, at);
                failed.push(format!(
                    "property 2: {rel} (seed {SEED:#x}), end at {line}:{col} (offset {at}); diagnostics after, with the positions of the text after the insertion:\n{}",
                    shown(&c)
                ));
            }
        }
    }
    eprintln!(
        "panic_insertions: {taken} programs, {border_runs} borders (property 1), {end_runs} ends (property 2), \
         {end_skipped} ends skipped for E0503; {with_rt} programs have an `rt fn`"
    );
    assert!(taken >= PROGRAMS && with_rt >= RT_PROGRAMS, "the programs taken ({taken}, {with_rt} with an `rt fn`)");
    assert!(border_runs > 0 && end_runs > 0, "every property ran ({border_runs}, {end_runs})");
    // The first few say where to look; the count says how many there are.
    let shown_failures = failed.iter().take(20).cloned().collect::<Vec<_>>().join("\n");
    assert!(
        failed.is_empty(),
        "{} of the insertions changed the diagnostics (the first 20):\n{shown_failures}",
        failed.len()
    );
}
