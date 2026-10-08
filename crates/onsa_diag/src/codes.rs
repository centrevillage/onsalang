//! Registry of diagnostic codes (spec §18.1, `docs/implementation-tasks.md` §5).
//!
//! Every code of the spec is listed here, including the codes no stage emits
//! yet (K-12): the gate checks that this list equals the codes the spec text
//! names, minus the retired codes of the plan §5 (S-109). The category follows
//! the numeric range of the spec table; a test checks that each code lies in
//! the range of its category. The category is the spec's grouping only: no
//! decision reads it (R-87 (3)).
//!
//! Each row also holds what the commands and the tests read (plan D-04, R-87 (3)):
//! - the stages that may report the code ([`Stage`]). A diagnostic carries the
//!   stage that reported it (the stage passes it, [`crate::Diagnostic::new`]);
//!   a code several stages report (E0020, E0200, E0408, ...) has several.
//! - whether every diagnostic of the code carries a fix candidate ([`FixRule`]),
//! - whether it carries a note with the correct rule ([`NoteRule`], S-114).
//!
//! [`crate::contract`] checks the last two on every diagnostic of the tests.

/// The stage of the compiler that reports a diagnostic (S-78, plan D-04).
///
/// `onsa fmt` and `onsa diff --ast` stop on the diagnostics of [`Stage::Syntax`]
/// (spec §18.2, S-120, S-214). The order of the check stages within a unit is
/// [`Stage::CHECK_ORDER`] (spec §18.1); the declaration order of this enum
/// decides nothing. Not running the stages that depend on a failed one is W4-06's.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Stage {
    /// The lexer, the parser, and the operator groups checked on its tree.
    Syntax,
    /// Names: resolution, visibility, naming rules (E0320 runs in `onsa_syntax`
    /// but is of this stage, so it does not stop `fmt`, §18.2), signatures.
    Names,
    /// Types and the checks of the typing pass.
    Types,
    /// The checks of flows (§11).
    Flow,
    /// Argument modes and moves.
    Modes,
    /// `rt` and effects.
    Effects,
    /// Lowering to Core and the build (code generation, layout, export).
    Build,
    /// The manifest (`onsa.toml`).
    Manifest,
}

impl Stage {
    pub const ALL: &'static [Stage] = &[
        Stage::Syntax,
        Stage::Names,
        Stage::Types,
        Stage::Flow,
        Stage::Modes,
        Stage::Effects,
        Stage::Build,
        Stage::Manifest,
    ];

    /// The dependency order of the check stages (spec §18.1: syntax, names,
    /// types, argument modes and moves, rt and effects): in a unit, the
    /// diagnostic of the earliest stage is the one reported, wherever it is
    /// (S-214). The one list of that order (`onsa_driver::reduce`). Lowering,
    /// the build and the manifest are not check stages: their diagnostics are
    /// not chosen per unit (§18.1).
    // SPEC-GAP(S-267): §18.1 does not place the flow checks in the order; they
    // sit after the types and before the modes, as in this enum, until S-267.
    pub const CHECK_ORDER: &'static [Stage] =
        &[Stage::Syntax, Stage::Names, Stage::Types, Stage::Flow, Stage::Modes, Stage::Effects];

    /// The place of a check stage in [`Stage::CHECK_ORDER`]; `None` for the
    /// stages that are not checks.
    pub fn check_rank(self) -> Option<usize> {
        Stage::CHECK_ORDER.iter().position(|&s| s == self)
    }

    /// Lower-case name (`syntax`), for the lists of `onsa_cases --codes`.
    pub fn name(self) -> &'static str {
        match self {
            Stage::Syntax => "syntax",
            Stage::Names => "names",
            Stage::Types => "types",
            Stage::Flow => "flow",
            Stage::Modes => "modes",
            Stage::Effects => "effects",
            Stage::Build => "build",
            Stage::Manifest => "manifest",
        }
    }
}

/// Whether every diagnostic of a code carries a fix candidate (D-04).
///
/// `Required` only where the spec text says the code always shows a candidate:
/// E0003, E0004, E0020, E0320, E0713, E0714, E0811, E0812 (W3-02, D5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FixRule {
    Required,
    Optional,
}

/// Whether every diagnostic of a code carries a note with the correct rule
/// (E0020, S-114, spec §18.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NoteRule {
    Rule,
    Optional,
}

/// Category of a diagnostic, by the numeric range in spec §18.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Category {
    /// E00xx: lexing, parsing, operator groups.
    Syntax,
    /// E02xx: features not supported in this version (S-03).
    Unsupported,
    /// E03xx: modules, name resolution, shadowing, cycles.
    Names,
    /// E04xx: types, arity, fields, literal types.
    Types,
    /// E05xx: exhaustiveness, unreachable statements.
    Exhaustiveness,
    /// E06xx: effects, `Alloc`, target provides and supported widths, policy.
    Effects,
    /// E07xx: argument modes, exclusivity, affine values, second-class values.
    Modes,
    /// E08xx: flow (ordering, rates, delays, `@param`, `~`).
    Flow,
    /// E09xx: rt.
    Rt,
    /// E10xx: FFI, unsafe, transpile.
    Ffi,
    /// E11xx: the manifest (`onsa.toml`).
    Manifest,
}

impl Category {
    /// The hundreds digit range `[lo, hi]` of the category.
    pub fn range(self) -> (u16, u16) {
        match self {
            Category::Syntax => (0, 99),
            Category::Unsupported => (200, 299),
            Category::Names => (300, 399),
            Category::Types => (400, 499),
            Category::Exhaustiveness => (500, 599),
            Category::Effects => (600, 699),
            Category::Modes => (700, 799),
            Category::Flow => (800, 899),
            Category::Rt => (900, 999),
            Category::Ffi => (1000, 1099),
            Category::Manifest => (1100, 1199),
        }
    }
}

macro_rules! codes {
    ($( $name:ident = $num:literal, $cat:ident, [$($stage:ident),+], $fix:ident, $note:ident, $title:literal; )*) => {
        /// A stable diagnostic code.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[allow(clippy::upper_case_acronyms)]
        pub enum Code { $( $name, )* }

        impl Code {
            /// Every registered code, in numeric order.
            pub const ALL: &'static [Code] = &[ $( Code::$name, )* ];

            /// The numeric part (`E0010` -> 10).
            pub fn number(self) -> u16 {
                match self { $( Code::$name => $num, )* }
            }

            /// The category of the code.
            pub fn category(self) -> Category {
                match self { $( Code::$name => Category::$cat, )* }
            }

            /// The stages that may report the code.
            pub fn stages(self) -> &'static [Stage] {
                match self { $( Code::$name => &[ $( Stage::$stage, )+ ], )* }
            }

            /// Whether every diagnostic of the code carries a fix candidate.
            pub fn fix_rule(self) -> FixRule {
                match self { $( Code::$name => FixRule::$fix, )* }
            }

            /// Whether every diagnostic of the code carries a note with the rule.
            pub fn note_rule(self) -> NoteRule {
                match self { $( Code::$name => NoteRule::$note, )* }
            }

            /// Short English title (the `onsa explain` heading).
            pub fn title(self) -> &'static str {
                match self { $( Code::$name => $title, )* }
            }

            /// The code as written (`E0010`).
            pub fn as_str(self) -> &'static str {
                match self { $( Code::$name => stringify!($name), )* }
            }

            /// Parse `E0010` (case-sensitive).
            pub fn parse(s: &str) -> Option<Code> {
                match s { $( stringify!($name) => Some(Code::$name), )* _ => None }
            }

            /// Long-form explanation (markdown), if written yet (M9 fills all of them).
            /// E0200's ends with the list of what this version does not support
            /// ([`crate::unsupported::explain`]).
            pub fn explain(self) -> Option<String> {
                match self { $( Code::$name => explain_text(stringify!($name)), )* }
            }
        }
    };
}

codes! {
    E0001 = 1, Syntax, [Syntax], Optional, Optional,
        "invalid character or literal";
    E0002 = 2, Syntax, [Syntax, Names, Types], Optional, Optional,
        "unexpected token";
    E0003 = 3, Syntax, [Syntax], Required, Optional,
        "`else` / `with` must follow the `}` on its line, and a block's `{` the line of its header";
    E0004 = 4, Syntax, [Syntax], Required, Optional,
        "doc comment in a place it cannot document";
    E0005 = 5, Syntax, [Syntax], Optional, Optional,
        "unknown attribute, or an attribute in a place it cannot be attached to";
    E0006 = 6, Syntax, [Syntax], Optional, Optional,
        "syntax nested deeper than the limit";
    E0010 = 10, Syntax, [Syntax], Optional, Optional,
        "binary operators from different groups mixed without parentheses";
    E0011 = 11, Syntax, [Syntax], Optional, Optional,
        "`as` / `at` expression used as an operand, or chained, without parentheses";
    E0012 = 12, Syntax, [Syntax], Optional, Optional,
        "prefix operators stacked without parentheses";
    E0020 = 20, Syntax, [Syntax, Names, Types, Flow], Required, Rule,
        "syntax from another language; see the suggested Onsa form";
    E0200 = 200, Unsupported, [Syntax, Names, Types, Flow, Modes, Effects, Build, Manifest], Optional, Optional,
        "feature not supported in this version of the compiler";
    E0302 = 302, Names, [Names, Types, Build], Optional, Optional,
        "cannot find this name";
    E0303 = 303, Names, [Names, Build], Optional, Optional,
        "name is not visible here";
    E0304 = 304, Names, [Names, Types], Optional, Optional,
        "a binding with this name is already visible (no shadowing)";
    E0305 = 305, Names, [Names], Optional, Optional,
        "a declaration has the same name as a flow in this module";
    E0306 = 306, Names, [Names], Optional, Optional,
        "duplicate `test` name in this module";
    E0307 = 307, Names, [Names], Optional, Optional,
        "`impl` in a place, or for a target, the rules do not allow";
    E0308 = 308, Names, [Names], Optional, Optional,
        "the name is of a kind that does not fit this position";
    E0309 = 309, Names, [Names], Optional, Optional,
        "unused binding";
    E0310 = 310, Names, [Names], Optional, Optional,
        "cyclic module import";
    E0311 = 311, Names, [Names], Optional, Optional,
        "the type contains itself as a value";
    E0312 = 312, Names, [Names], Optional, Optional,
        "the initializer of a `const` refers to itself";
    E0320 = 320, Names, [Names], Required, Optional,
        "name does not follow the naming rule for its kind";
    E0401 = 401, Types, [Types, Flow], Optional, Optional,
        "type mismatch";
    E0405 = 405, Types, [Types], Optional, Optional,
        "the type of this literal cannot be determined";
    E0406 = 406, Types, [Types], Optional, Optional,
        "a type that an expression makes (a type parameter of a call, the type in `None`, the element of `[]`) is not determined by the end of the function";
    E0407 = 407, Types, [Types], Optional, Optional,
        "the result of a `const` is not Copy or a statically placeable Shared value";
    E0408 = 408, Types, [Syntax, Types, Flow], Optional, Optional,
        "literal is out of range for its type";
    E0409 = 409, Types, [Build], Optional, Optional,
        "the size of a type or of a flow's state does not fit in `U32`";
    E0410 = 410, Types, [Types, Flow], Optional, Optional,
        "struct literal field error (missing, unknown, or duplicate field)";
    E0411 = 411, Types, [Types], Optional, Optional,
        "`as` only widens; use a conversion method";
    E0412 = 412, Types, [Types, Flow], Optional, Optional,
        "wrong number of arguments";
    E0413 = 413, Types, [Types], Optional, Optional,
        "no such field or method";
    E0414 = 414, Types, [Types], Optional, Optional,
        "`?` needs a matching Option/Result return type";
    E0415 = 415, Types, [Types], Optional, Optional,
        "assignment target is not a place";
    E0416 = 416, Types, [Types], Optional, Optional,
        "type does not satisfy the bound";
    E0417 = 417, Types, [Types], Optional, Optional,
        "not a constant expression where one is required";
    E0418 = 418, Types, [Types], Optional, Optional,
        "a statement in the middle of a block has a value that is not `()`";
    E0419 = 419, Types, [Types], Optional, Optional,
        "compile-time evaluation panicked";
    E0420 = 420, Types, [Types], Optional, Optional,
        "the type of this operand must be known here; add an annotation";
    E0421 = 421, Types, [Types], Optional, Optional,
        "typed hole";
    E0501 = 501, Exhaustiveness, [Types], Optional, Optional,
        "`match` is not exhaustive";
    E0502 = 502, Exhaustiveness, [Types, Flow], Optional, Optional,
        "refutable pattern in `let`";
    E0503 = 503, Exhaustiveness, [Types], Optional, Optional,
        "unreachable statement after a diverging one";
    E0601 = 601, Effects, [Effects], Optional, Optional,
        "effect used but not in the function's effect row";
    E0610 = 610, Effects, [Effects, Build], Optional, Optional,
        "effect is not provided by the target";
    E0612 = 612, Effects, [Effects], Optional, Optional,
        "a handler of a non-`blocking` effect uses a `blocking` effect";
    E0613 = 613, Effects, [Effects], Optional, Optional,
        "the handler of an `rt` operation is not `rt`";
    E0614 = 614, Effects, [Effects], Optional, Optional,
        "an operation of a `blocking` effect is marked `rt`";
    E0620 = 620, Effects, [Effects, Build], Optional, Optional,
        "an effect row goes beyond what the policy allows";
    E0630 = 630, Effects, [Build], Optional, Optional,
        "the public signature or a parameter ID of a frozen item changed";
    E0640 = 640, Effects, [Effects], Optional, Optional,
        "the result of a `handle` of `Alloc` is not Copy";
    E0641 = 641, Effects, [Effects], Optional, Optional,
        "the body of a `handle` of `Alloc` modifies a heap value from outside";
    E0642 = 642, Effects, [Effects], Optional, Optional,
        "the body of a `handle` of `Alloc` uses an effect other than `Alloc`";
    E0650 = 650, Effects, [Build], Optional, Optional,
        "`Atomic` value wider than the target handles lock-free";
    E0701 = 701, Modes, [Modes], Optional, Optional,
        "cannot modify this place";
    E0702 = 702, Modes, [Modes], Optional, Optional,
        "the same place is passed as `inout` twice in one call";
    E0703 = 703, Modes, [Modes], Optional, Optional,
        "argument mode does not match the parameter";
    E0704 = 704, Modes, [Modes], Optional, Optional,
        "value used after it was moved";
    E0710 = 710, Modes, [Modes], Optional, Optional,
        "second-class value used outside an argument position";
    E0711 = 711, Modes, [Types, Modes], Optional, Optional,
        "borrowed Affine value passed as `move`";
    E0712 = 712, Modes, [Modes], Optional, Optional,
        "closure cannot capture this value";
    E0713 = 713, Modes, [Types, Modes], Required, Optional,
        "calling an `inout self` method needs `!` after the name";
    E0714 = 714, Modes, [Types, Flow, Modes], Required, Optional,
        "`!` on a method that does not take `inout self`";
    E0715 = 715, Modes, [Modes], Optional, Optional,
        "the place being iterated or matched is modified";
    E0801 = 801, Flow, [Flow], Optional, Optional,
        "name used before its definition in a flow (only `prev`/`delay`/`vdelay` may look back)";
    E0805 = 805, Flow, [Flow], Optional, Optional,
        "a function with effects cannot be called from a flow";
    E0806 = 806, Flow, [Flow], Optional, Optional,
        "this form is not allowed in a flow body";
    E0807 = 807, Flow, [Flow], Optional, Optional,
        "`delay` with length 1; write `prev` instead";
    E0808 = 808, Flow, [Flow], Optional, Optional,
        "delay length or `par` range out of its allowed values (a non-constant one is E0417)";
    E0809 = 809, Flow, [Flow, Build], Optional, Optional,
        "`@param` is missing, misplaced, or malformed";
    E0810 = 810, Flow, [Flow], Optional, Optional,
        "a flow input or output without `at`, an output clock other than `sample`, or a value type that cannot cross";
    E0811 = 811, Flow, [Flow], Required, Optional,
        "calling a flow creates a stateful instance and needs `~`";
    E0812 = 812, Flow, [Types, Flow], Required, Optional,
        "`~` used on something that is not a flow";
    E0813 = 813, Flow, [Flow], Optional, Optional,
        "first argument of `prev`/`delay`/`vdelay` must be `Sig` rate";
    E0815 = 815, Flow, [Flow], Optional, Optional,
        "a value's clock is faster than its place (flow input, delay `init`, non-`rt` fn argument)";
    E0816 = 816, Flow, [Flow], Optional, Optional,
        "`init` is omitted, but the value type does not satisfy `Default`";
    E0817 = 817, Flow, [Flow], Optional, Optional,
        "a flow makes an instance of itself";
    E0818 = 818, Flow, [Flow], Optional, Optional,
        "`@mem` in a wrong place or with an unknown memory name";
    E0819 = 819, Flow, [Flow], Optional, Optional,
        "state with bulk memory placed in a plain value";
    E0820 = 820, Flow, [Build], Optional, Optional,
        "the memory of an exported flow exceeds the budget of the target";
    E0821 = 821, Flow, [Flow], Optional, Optional,
        "flow-only syntax used outside a flow";
    E0901 = 901, Rt, [Effects], Optional, Optional,
        "`rt` function calls a non-`rt` function";
    E0902 = 902, Rt, [Effects], Optional, Optional,
        "`rt` function has `Alloc` in its effect row";
    E0903 = 903, Rt, [Effects], Optional, Optional,
        "`rt` function is recursive";
    E0904 = 904, Rt, [Effects], Optional, Optional,
        "`rt` function has a `blocking` effect in its effect row";
    E0905 = 905, Rt, [Effects], Optional, Optional,
        "`rt` function has an effect that is not an rt effect in its effect row";
    E1010 = 1010, Ffi, [Build], Optional, Optional,
        "the portable core reaches an `extern` function";
    E1011 = 1011, Ffi, [Build], Optional, Optional,
        "exported C names collide";
    E1101 = 1101, Manifest, [Manifest], Optional, Optional,
        "the manifest is not valid TOML";
    E1102 = 1102, Manifest, [Manifest], Optional, Optional,
        "unknown table or key in the manifest";
    E1103 = 1103, Manifest, [Manifest], Optional, Optional,
        "a manifest value has the wrong type or form";
    E1104 = 1104, Manifest, [Manifest], Optional, Optional,
        "a required manifest key is missing";
}

fn explain_text(code: &str) -> Option<String> {
    // Explanations live in `explain/<code>.md`; add an arm when one is written.
    match code {
        "E0010" => Some(include_str!("../explain/E0010.md").to_string()),
        "E0200" => Some(crate::unsupported::explain()),
        "E0811" => Some(include_str!("../explain/E0811.md").to_string()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_are_in_their_category_range() {
        for &c in Code::ALL {
            let (lo, hi) = c.category().range();
            assert!(lo <= c.number() && c.number() <= hi, "{} outside {:?}", c.as_str(), c.category());
        }
    }

    #[test]
    fn codes_are_sorted_and_unique() {
        let nums: Vec<u16> = Code::ALL.iter().map(|c| c.number()).collect();
        let mut sorted = nums.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(nums, sorted);
    }

    #[test]
    fn stages_are_sorted_and_unique() {
        for &c in Code::ALL {
            let st = c.stages();
            assert!(!st.is_empty(), "{}", c.as_str());
            assert!(st.windows(2).all(|w| w[0] < w[1]), "{}: stages not in order: {st:?}", c.as_str());
        }
    }

    #[test]
    fn the_codes_whose_fix_is_required_are_the_ones_the_spec_names() {
        // W3-02 D5: the spec text says these always show a candidate.
        let required: Vec<&str> =
            Code::ALL.iter().filter(|c| c.fix_rule() == FixRule::Required).map(|c| c.as_str()).collect();
        assert_eq!(required, ["E0003", "E0004", "E0020", "E0320", "E0713", "E0714", "E0811", "E0812"]);
        let rule: Vec<&str> =
            Code::ALL.iter().filter(|c| c.note_rule() == NoteRule::Rule).map(|c| c.as_str()).collect();
        assert_eq!(rule, ["E0020"]);
    }

    #[test]
    fn as_str_matches_number() {
        for &c in Code::ALL {
            assert_eq!(c.as_str(), format!("E{:04}", c.number()));
            assert_eq!(Code::parse(c.as_str()), Some(c));
        }
    }
}
