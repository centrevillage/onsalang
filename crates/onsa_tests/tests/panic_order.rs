//! Where the first panic of a flow is (W7-17 L1/t, from the model of the break side of W7-11 U2b): a flow of divisions that all panic at the frame 4 (`K / (x - 4)`; a delay of the
//! slower stage `sample / 4` whose `d4` is 0 there, `K / d4`), in which the model says which one panics first: the slower stage of a frame runs before its `sample` stage, the
//! work of a delay (its first argument, its store) comes after what reads it, and a read of a `^name` or a part of a later stage comes after the first (§11.3, §11.4, §11.10).
//! The programs are in `data/panic_order.txt` (the generated ones that the model gives the order of; `## <name> <the site that panics first>`), one flow `f` and one `render` of
//! 8 frames each. The test finds the site by the number at the start of the text of the span of the panic.

use onsa_driver::{Loaded, PackageInput, TestOptions, TestRun};

/// The sections of the data: (name, the site, the text).
fn programs() -> Vec<(String, u32, String)> {
    let data = include_str!("data/panic_order.txt");
    let mut out: Vec<(String, u32, String)> = Vec::new();
    for line in data.lines() {
        if let Some(head) = line.strip_prefix("## ") {
            let (name, site) = head.rsplit_once(' ').expect("`## <name> <site>`");
            out.push((name.to_string(), site.parse().expect("a site number"), String::new()));
        } else if let Some((_, _, text)) = out.last_mut() {
            text.push_str(line);
            text.push('\n');
        }
    }
    out
}

/// The number of the site that the first failed test of `src` panics at.
fn site_of(src: &str) -> u32 {
    let mut loaded = Loaded::from_input(PackageInput::single_file("p.onsa", src)).expect("the input loads");
    let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    assert!(analyzed.diagnostics.is_empty(), "{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
    let module = onsa_driver::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
    let report = match onsa_driver::run_tests(&loaded.sources, &module, &TestOptions::default()) {
        Ok(TestRun::Ran(r)) => r,
        _ => panic!("the tests of the program did not run"),
    };
    let failure = report.tests.iter().find_map(|t| t.failure.as_ref()).expect("the test of the program fails");
    let text = &src[failure.span.start as usize..failure.span.end as usize];
    let digits: String = text.chars().skip_while(|c| !c.is_ascii_digit()).take_while(char::is_ascii_digit).collect();
    digits.parse().unwrap_or_else(|_| panic!("no site in the span `{text}`: {}", failure.message))
}

#[test]
fn the_first_panic_of_a_flow_is_where_the_model_of_the_order_of_the_stages_says() {
    let programs = programs();
    assert_eq!(programs.len(), 5, "the sections of the data");
    for (name, site, text) in programs {
        assert_eq!(site_of(&text), site, "{name}");
    }
}
