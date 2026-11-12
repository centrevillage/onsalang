//! The integration tests of the `onsa` command: one test executable (RF-16), each module one
//! file of tests that runs the built `onsa` (`env!("CARGO_BIN_EXE_onsa")`), with the shared
//! harness in `test_support`.

mod test_support;

mod alias_sameness;
mod binding_clock_notes;
mod block_operands;
mod body_paths;
mod bound_list_model;
mod call_forms_syntax;
mod candidate_headings;
mod candidate_shapes;
mod check_json_document;
mod command_paths;
mod const_placement_model;
mod declaration_headings;
mod declaration_order;
mod deep_recursion;
mod diagnostics_json;
mod diff_ast_sets;
mod doc_comment_targets;
mod effect_names;
mod empty_brackets;
mod error_type_sweep;
mod excluded_readings_notes;
mod exit_codes;
mod explain_e0200;
mod failed_names;
mod flow_syntax;
mod flow_syntax_decisions;
mod fmt_comments;
mod fmt_lines_lists;
mod fmt_many_files;
mod fmt_rewrites;
mod fmt_same_program;
mod fmt_spaces_lists;
mod fmt_spellings_columns_ranges;
mod fmt_syntax_failures;
mod fmt_write;
mod foreign_candidates;
mod gap_forms;
mod generated_order;
mod heading_names;
mod heading_reach_grid;
mod instance_limits;
mod interface_const_floats;
mod interface_fn_return;
mod interface_generic_kinds;
mod interface_visibility;
mod lexical_syntax;
mod manifest_diagnostics;
mod manifest_host;
mod manifest_platform;
mod manifest_plugin;
mod manifest_prefix;
mod manifest_required;
mod manifest_targets;
mod manifest_values;
mod name_overlaps;
mod naming_shapes;
mod nesting;
mod nesting_boundary;
mod operator_groups;
mod outside_flow_held_operands;
mod package_input;
mod package_links;
mod package_model;
mod package_naming;
mod package_tests_dir;
mod package_tree;
mod pattern_guard_candidates;
mod pattern_rows;
mod prelude_names;
mod range_syntax;
mod std_privilege;
mod syntax_units;
mod test_failure_positions;
mod test_file_selection;
mod test_identity;
mod test_json_document;
mod test_reach;
mod type_args_syntax;
mod type_param_members;
mod types_holding_themselves;
mod use_clash_edges;
mod use_cycles;
mod use_generated_items;
mod use_list_forms;
mod use_list_words;
mod use_model;
mod use_name_rules;
mod use_paths;
mod use_reexport;
mod use_repair_loop;
mod use_shapes;
mod visibility;

/// Every file of tests in this directory is a module above: a file with no `mod` line is not
/// compiled, and its tests go unrun without a failure.
#[test]
fn every_file_of_the_directory_is_a_module() {
    let main = include_str!("main.rs");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cli");
    let mut missing = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let module = path.is_dir() || path.extension().is_some_and(|e| e == "rs");
        if module && name != "main" && !main.lines().any(|l| l == format!("mod {name};")) {
            missing.push(name);
        }
    }
    assert!(missing.is_empty(), "files of tests with no `mod` line in `main.rs`: {missing:?}");
}
