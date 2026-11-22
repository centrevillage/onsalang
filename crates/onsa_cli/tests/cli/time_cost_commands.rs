//! What the time costs, read in the text of `onsa dump --core` (W7-16 U6a3/t; spec §11.4, §12.4; S-1217, S-1211, S-1127, S-1129 (1), S-1179): the decision of S-1217 promises
//!
//! - a flow that neither reads `sample_tick()` nor runs a flow that does has no field, no argument and no operation for the time (the counter of the phase of a flow with a stage of `sample / N` is another thing);
//! - the counter of a flow that only reads the time (it has no stage of its own) is advanced by the `process` of the outermost flow, once for each frame, and not by `tick`, so a flow embedded twice does not count twice;
//! - a function of a stage takes the time (`t`, and `t_hi` where the time goes through a `.down~` before it is read) only when it reads it or runs a function that does, and then it uses what it takes (no argument that
//!   nothing reads).
//!
//! The text of the Core is read for the heads of the functions (`rt fn <name>(<parameters>) -> …`), the lines of their bodies and the `State` types. The names of the parameters (`t`, `t_hi`) are the ones the work ticket
//! of U6a3 fixes; that a field is `s.<k>` in a body is the Core's own way to write the field `k` of the type. The spec does not fix the Core, so only what the decision promises is read: whether a parameter is there,
//! whether a body uses it, and how many `+% 1` a body has. None of the cases is taken from the output of the compiler.

use crate::test_support::{Dir, run};

struct CoreFn {
    name: String,
    params: Vec<String>,
    body: String,
}

impl CoreFn {
    fn takes(&self, param: &str) -> bool {
        self.params.iter().any(|p| p == param)
    }

    fn uses(&self, name: &str) -> bool {
        has_token(&self.body, name)
    }

    fn advances(&self) -> usize {
        self.body.matches("+% 1").count()
    }

    /// Whether the body reads the field `k` of the state (`s.k`, not `s.k2`).
    fn reads_field(&self, k: usize) -> bool {
        let key = format!("s.{k}");
        self.body
            .match_indices(&key)
            .any(|(i, _)| !self.body[i + key.len()..].starts_with(|c: char| c.is_ascii_digit()))
    }
}

fn has_token(text: &str, token: &str) -> bool {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_')).any(|w| w == token)
}

/// The parameters of a head, by name (`inout s: T` is `s`); the commas inside brackets do not split.
fn param_names(list: &str) -> Vec<String> {
    let (mut out, mut depth, mut cur) = (Vec::new(), 0i32, String::new());
    for c in list.chars() {
        match c {
            '[' | '(' | '<' => depth += 1,
            ']' | ')' | '>' => depth -= 1,
            _ => {}
        }
        if c == ',' && depth == 0 {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
    }
    out.push(cur);
    out.iter()
        .filter(|p| !p.trim().is_empty())
        .map(|p| p.trim().trim_start_matches("inout ").split(':').next().unwrap_or("").trim().to_string())
        .collect()
}

fn core_fns(text: &str) -> Vec<CoreFn> {
    let mut fns = Vec::new();
    let mut lines = text.lines();
    while let Some(l) = lines.next() {
        let Some(head) = l.strip_prefix("rt fn ").or_else(|| l.strip_prefix("fn ")) else { continue };
        if !l.ends_with('{') {
            continue;
        }
        let open = head.find('(').unwrap_or_else(|| panic!("a head with no `(`: {l}"));
        let close = head.rfind(") ->").unwrap_or_else(|| panic!("a head with no `) ->`: {l}"));
        let body: Vec<&str> = lines.by_ref().take_while(|b| *b != "}").collect();
        fns.push(CoreFn {
            name: head[..open].to_string(),
            params: param_names(&head[open + 1..close]),
            body: body.join("\n"),
        });
    }
    fns
}

/// The index of the field `name` of the type `main.<flow>.State` in the line `type main.<flow>.State = struct { … }`.
fn field_index(text: &str, flow: &str, name: &str) -> Option<usize> {
    let head = format!("type main.{flow}.State = struct {{ ");
    let line = text.lines().find(|l| l.starts_with(&head)).unwrap_or_else(|| panic!("no State of {flow} in:\n{text}"));
    let inner = line[head.len()..].trim_end_matches(" }");
    param_names(inner).iter().position(|n| n == name)
}

fn core_of(tag: &str, flows: &str) -> String {
    let d = Dir::pkg(tag);
    d.write("main.onsa", flows);
    let out = run(d.root(), &["dump", "--core", &d.arg()]);
    assert_eq!(out.code, 0, "{flows}: {}{}", out.stdout, out.stderr);
    assert!(
        !out.stderr.contains("internal error") && !out.stdout.contains("E0200"),
        "{flows}: {}{}",
        out.stdout,
        out.stderr
    );
    out.stdout
}

fn find<'a>(fns: &'a [CoreFn], name: &str) -> &'a CoreFn {
    fns.iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("a function `{name}` in {:?}", fns.iter().map(|f| &f.name).collect::<Vec<_>>()))
}

/// What holds of every function of a Core: it takes `t_hi` only with `t`, and it uses what it takes.
fn assert_takes_only_what_it_uses(fns: &[CoreFn], what: &str) {
    for f in fns {
        if f.takes("t_hi") {
            assert!(f.takes("t"), "{what}: {} takes `t_hi` with no `t`: {:?}", f.name, f.params);
            assert!(f.uses("t_hi"), "{what}: {} takes `t_hi` and does not use it:\n{}", f.name, f.body);
        }
        if f.takes("t") {
            assert!(f.uses("t"), "{what}: {} takes `t` and does not use it:\n{}", f.name, f.body);
        }
    }
}

/// The flow of the review of the design (S-1217): `so` reads the time in its output at `sample / 4`, `mid` reads that output at `sample`, `top` calls `mid`. Only the function of the stage of `sample / 4` of each
/// takes the time (`tick_4`): `tick` of `mid` and of `top` run no part that reads it, so they take nothing. The functions that take `t` use it (`mid.tick_4` passes it to `so.tick_4`), no function takes `t_hi`
/// (there is no `.down~`), and the `process` of `mid` and `top` hands the time to the stage that takes it.
#[test]
fn only_the_function_of_the_stage_that_reads_the_time_takes_it() {
    let flows = "flow so() -> U32 at (sample / 4) {\n  sample_tick()\n}\n\nflow mid() -> U32 at sample {\n  so~() at sample\n}\n\npub flow top() -> U32 at sample {\n  mid~()\n}\n";
    let fns = core_fns(&core_of("time_cost_stage", flows));
    for flow in ["so", "mid", "top"] {
        let slow = find(&fns, &format!("main.{flow}.tick_4"));
        assert!(
            slow.takes("t") && slow.uses("t"),
            "{flow}.tick_4 takes the time and uses it: {:?}\n{}",
            slow.params,
            slow.body
        );
        let fast = find(&fns, &format!("main.{flow}.tick"));
        assert!(!fast.takes("t"), "{flow}.tick reads no time and runs no part that does: {:?}", fast.params);
    }
    for flow in ["mid", "top"] {
        let process = find(&fns, &format!("main.{flow}.process"));
        assert!(process.uses("t"), "{flow}.process hands the time to the stage of sample / 4:\n{}", process.body);
    }
    assert!(fns.iter().all(|f| !f.takes("t_hi")), "no `.down~`, no upper word");
    assert_takes_only_what_it_uses(&fns, "the stages of the slow output");
}

/// A flow that neither reads the time nor runs a flow that does has no argument, no field and no operation for it, also when it has a stage of its own and a parent that has a stage: the counter of its stage is the
/// phase, not the time. No function takes `t`, none uses a name `t`, and `plain` (no stage, no reader) has no `_tick` and no `+% 1` in any function.
#[test]
fn a_flow_that_reads_no_time_has_nothing_of_the_time() {
    let flows = "flow lag(p: F32 at block) -> F32 at sample {\n  let a = prev~(p at (sample / 4))\n  a at sample\n}\n\nflow plain(x: F32 at sample) -> F32 at sample {\n  x * 0.5\n}\n\npub flow slow_parent(p: F32 at block, x: F32 at sample) -> F32 at sample {\n  lag~(p) * plain~(x)\n}\n";
    let text = core_of("time_cost_none", flows);
    let fns = core_fns(&text);
    for f in &fns {
        assert!(!f.takes("t") && !f.takes("t_hi"), "{} takes the time: {:?}", f.name, f.params);
        assert!(!f.uses("t") && !f.uses("t_hi"), "{} has a name of the time:\n{}", f.name, f.body);
    }
    assert_eq!(field_index(&text, "plain", "_tick"), None, "a flow with no stage and no reader has no counter");
    for f in fns.iter().filter(|f| f.name.starts_with("main.plain.")) {
        assert_eq!(f.advances(), 0, "{} advances nothing:\n{}", f.name, f.body);
    }
}

/// A flow that reads the time but runs no part that does not read it: the call of the part that reads none (`plain`) carries no time, the call of the reader (`tk`) does.
#[test]
fn a_call_of_a_flow_that_reads_no_time_carries_no_time() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\nflow plain(x: F32 at sample) -> F32 at sample {\n  x * 0.5\n}\n\npub flow mixed(x: F32 at sample) -> F32 at sample {\n  plain~(x) * F32.round_from(tk~())\n}\n";
    let fns = core_fns(&core_of("time_cost_calls", flows));
    let mixed = find(&fns, "main.mixed.tick");
    let call = |callee: &str| -> &str {
        mixed
            .body
            .lines()
            .find(|l| l.contains(&format!("{callee}(")))
            .unwrap_or_else(|| panic!("a call of {callee}:\n{}", mixed.body))
    };
    assert!(
        !has_token(call("main.plain.tick"), "t"),
        "the call of `plain` carries no time: {}",
        call("main.plain.tick")
    );
    assert!(has_token(call("main.tk.tick"), "t"), "the call of `tk` carries the time: {}", call("main.tk.tick"));
    assert_takes_only_what_it_uses(&fns, "a reader beside a flow that reads no time");
}

/// S-1217 (b): a flow that reads the time and has no stage of its own (`tk`) and a caller that embeds two of it (`two`) do not advance the counter in `tick`: only the `process` of the flow that runs outermost does,
/// once (`tk.process` for `tk` alone, `two.process` for `two`), so the two children of `two` cannot count the frame twice. The functions that run the time take it and use it, and they have a field for it (`_tick`,
/// which `process` reads: any flow can be the outermost). There is no upper word (no `.down~`).
#[test]
fn the_counter_of_a_flow_that_only_reads_the_time_is_advanced_once_by_process_and_not_by_tick() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow two() -> U32 at sample {\n  tk~() * 100 + tk~()\n}\n";
    let text = core_of("time_cost_advance", flows);
    let fns = core_fns(&text);
    for flow in ["tk", "two"] {
        let tick = find(&fns, &format!("main.{flow}.tick"));
        assert!(tick.takes("t") && tick.uses("t"), "{flow}.tick reads or passes the time: {:?}", tick.params);
        assert_eq!(
            tick.advances(),
            0,
            "{flow}.tick does not count: it is run again for each embedding:\n{}",
            tick.body
        );
        let process = find(&fns, &format!("main.{flow}.process"));
        assert_eq!(process.advances(), 1, "{flow}.process counts once for each frame:\n{}", process.body);
        let k = field_index(&text, flow, "_tick").unwrap_or_else(|| panic!("{flow} has `_tick`"));
        assert!(
            process.reads_field(k),
            "{flow}.process reads the counter for the time of the frame:\n{}",
            process.body
        );
        assert_eq!(field_index(&text, flow, "_tick_hi"), None, "no `.down~`, no upper word");
    }
    assert!(fns.iter().all(|f| !f.takes("t_hi")));
    assert_takes_only_what_it_uses(&fns, "the time-only flows");
}

/// A flow with a stage of its own that also reads the time (the counter is the phase of its stage and the time at once) advances it once for each frame, in `tick` or in `process`, not in both and not in neither
/// (the choice of the place is the implementation's, the decision is only for the flows with no stage): a count of 1 over the two functions.
#[test]
fn a_flow_with_a_stage_that_also_reads_the_time_counts_each_frame_once() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow grid_and_time(p: U32 at block) -> U32 at sample {\n  let a = prev~(p at (sample / 4))\n  tk~() + (a at sample)\n}\n";
    let fns = core_fns(&core_of("time_cost_grid", flows));
    let both = find(&fns, "main.grid_and_time.tick").advances() + find(&fns, "main.grid_and_time.process").advances();
    assert_eq!(both, 1, "one count for each frame in all");
}

/// §11.4, S-1217: a `.down~` before a read puts the upper word in the arguments of the functions that run the part: the function of the stage that runs `tk` under `.down~(2)` takes `t` and `t_hi` and uses both,
/// the function of the `sample` stage that only reads the held output takes none, the `process` of the outermost flow reads the field of the upper word, and `tk` (which reads the low word of the time it is given)
/// takes `t` and uses it. A `t_hi` is never taken without a `t`, and never without a use.
#[test]
fn a_down_before_a_read_gives_the_upper_word_to_the_functions_that_fold_the_time() {
    let flows = "flow tk() -> U32 at sample {\n  sample_tick()\n}\n\npub flow over() -> U32 at sample {\n  tk~().down~(2) at sample\n}\n";
    let text = core_of("time_cost_wide", flows);
    let fns = core_fns(&text);
    let stages: Vec<&CoreFn> = fns.iter().filter(|f| f.name.starts_with("main.over.tick_")).collect();
    assert!(
        stages.iter().any(|f| f.takes("t") && f.takes("t_hi")),
        "a stage of `over` takes the two words: {:?}",
        fns.iter().filter(|f| f.name.starts_with("main.over.")).map(|f| (&f.name, &f.params)).collect::<Vec<_>>()
    );
    let sample = find(&fns, "main.over.tick");
    assert!(
        !sample.takes("t") && !sample.takes("t_hi"),
        "the stage that reads the held output takes no time: {:?}",
        sample.params
    );
    let k = field_index(&text, "over", "_tick_hi").expect("`over` has `_tick_hi`");
    assert!(
        find(&fns, "main.over.process").reads_field(k),
        "`over.process` reads the upper word:\n{}",
        find(&fns, "main.over.process").body
    );
    let part = find(&fns, "main.tk.tick");
    assert!(part.takes("t") && part.uses("t"), "{:?}", part.params);
    assert_takes_only_what_it_uses(&fns, "a read under `.down~`");
}
