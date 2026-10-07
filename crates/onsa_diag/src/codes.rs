//! Registry of diagnostic codes (spec §18.1, `docs/implementation-tasks.md` §5).
//!
//! Every code of the spec is listed here, including the codes no stage emits
//! yet (K-12): the gate checks that this list equals the codes the spec text
//! names, minus the retired codes of the plan §5 (S-109). The category follows
//! the numeric range of the spec table; a test checks that each code lies in
//! the range of its category.

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
    ($( $name:ident = $num:literal, $cat:ident, $title:literal; )*) => {
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
            pub fn explain(self) -> Option<&'static str> {
                match self { $( Code::$name => explain_text(stringify!($name)), )* }
            }
        }
    };
}

codes! {
    E0001 = 1,    Syntax,         "invalid character or literal";
    E0002 = 2,    Syntax,         "unexpected token";
    E0003 = 3,    Syntax,         "`else` / `with` must follow the `}` on its line, and a block's `{` the line of its header";
    E0004 = 4,    Syntax,         "doc comment in a place it cannot document";
    E0005 = 5,    Syntax,         "unknown attribute, or an attribute in a place it cannot be attached to";
    E0006 = 6,    Syntax,         "syntax nested deeper than the limit";
    E0010 = 10,   Syntax,         "binary operators from different groups mixed without parentheses";
    E0011 = 11,   Syntax,         "`as` / `at` expression used as an operand, or chained, without parentheses";
    E0012 = 12,   Syntax,         "prefix operators stacked without parentheses";
    E0020 = 20,   Syntax,         "syntax from another language; see the suggested Onsa form";
    E0200 = 200,  Unsupported,    "feature not supported in this version of the compiler";
    E0302 = 302,  Names,          "cannot find this name";
    E0303 = 303,  Names,          "name is not visible here";
    E0304 = 304,  Names,          "a binding with this name is already visible (no shadowing)";
    E0305 = 305,  Names,          "a declaration has the same name as a flow in this module";
    E0306 = 306,  Names,          "duplicate `test` name in this module";
    E0307 = 307,  Names,          "`impl` in a place, or for a target, the rules do not allow";
    E0308 = 308,  Names,          "the name is of a kind that does not fit this position";
    E0309 = 309,  Names,          "unused binding";
    E0310 = 310,  Names,          "cyclic module import";
    E0311 = 311,  Names,          "the type contains itself as a value";
    E0312 = 312,  Names,          "the initializer of a `const` refers to itself";
    E0320 = 320,  Names,          "name does not follow the naming rule for its kind";
    E0401 = 401,  Types,          "type mismatch";
    E0405 = 405,  Types,          "the type of this literal cannot be determined";
    E0406 = 406,  Types,          "a type parameter cannot be determined from arguments or the expected type";
    E0407 = 407,  Types,          "the result of a `const` is not Copy or a statically placeable Shared value";
    E0408 = 408,  Types,          "literal is out of range for its type";
    E0409 = 409,  Types,          "the size of a type or of a flow's state does not fit in `U32`";
    E0410 = 410,  Types,          "struct literal field error (missing, unknown, or duplicate field)";
    E0411 = 411,  Types,          "`as` only widens; use a conversion method";
    E0412 = 412,  Types,          "wrong number of arguments";
    E0413 = 413,  Types,          "no such field or method";
    E0414 = 414,  Types,          "`?` needs a matching Option/Result return type";
    E0415 = 415,  Types,          "assignment target is not a place";
    E0416 = 416,  Types,          "type does not satisfy the bound";
    E0417 = 417,  Types,          "not a constant expression where one is required";
    E0418 = 418,  Types,          "a statement in the middle of a block has a value that is not `()`";
    E0419 = 419,  Types,          "compile-time evaluation panicked";
    E0420 = 420,  Types,          "the type of this operand must be known here; add an annotation";
    E0421 = 421,  Types,          "typed hole";
    E0501 = 501,  Exhaustiveness, "`match` is not exhaustive";
    E0502 = 502,  Exhaustiveness, "refutable pattern in `let`";
    E0503 = 503,  Exhaustiveness, "unreachable statement after a diverging one";
    E0601 = 601,  Effects,        "effect used but not in the function's effect row";
    E0610 = 610,  Effects,        "effect is not provided by the target";
    E0612 = 612,  Effects,        "a handler of a non-`blocking` effect uses a `blocking` effect";
    E0613 = 613,  Effects,        "the handler of an `rt` operation is not `rt`";
    E0614 = 614,  Effects,        "an operation of a `blocking` effect is marked `rt`";
    E0620 = 620,  Effects,        "an effect row goes beyond what the policy allows";
    E0630 = 630,  Effects,        "the public signature or a parameter ID of a frozen item changed";
    E0640 = 640,  Effects,        "the result of a `handle` of `Alloc` is not Copy";
    E0641 = 641,  Effects,        "the body of a `handle` of `Alloc` modifies a heap value from outside";
    E0642 = 642,  Effects,        "the body of a `handle` of `Alloc` uses an effect other than `Alloc`";
    E0650 = 650,  Effects,        "`Atomic` value wider than the target handles lock-free";
    E0701 = 701,  Modes,          "cannot modify this place";
    E0702 = 702,  Modes,          "the same place is passed as `inout` twice in one call";
    E0703 = 703,  Modes,          "argument mode does not match the parameter";
    E0704 = 704,  Modes,          "value used after it was moved";
    E0710 = 710,  Modes,          "second-class value used outside an argument position";
    E0711 = 711,  Modes,          "borrowed Affine value passed as `move`";
    E0712 = 712,  Modes,          "closure cannot capture this value";
    E0713 = 713,  Modes,          "calling an `inout self` method needs `!` after the name";
    E0714 = 714,  Modes,          "`!` on a method that does not take `inout self`";
    E0715 = 715,  Modes,          "the place being iterated or matched is modified";
    E0801 = 801,  Flow,           "name used before its definition in a flow (only `prev`/`delay`/`vdelay` may look back)";
    E0805 = 805,  Flow,           "a function with effects cannot be called from a flow";
    E0806 = 806,  Flow,           "this form is not allowed in a flow body";
    E0807 = 807,  Flow,           "`delay` with length 1; write `prev` instead";
    E0808 = 808,  Flow,           "delay length or `par` range out of its allowed values (a non-constant one is E0417)";
    E0809 = 809,  Flow,           "`@param` is missing, misplaced, or malformed";
    E0810 = 810,  Flow,           "a flow input or output without `at`, an output clock other than `sample`, or a value type that cannot cross";
    E0811 = 811,  Flow,           "calling a flow creates a stateful instance and needs `~`";
    E0812 = 812,  Flow,           "`~` used on something that is not a flow";
    E0813 = 813,  Flow,           "first argument of `prev`/`delay`/`vdelay` must be `Sig` rate";
    E0815 = 815,  Flow,           "a value's clock is faster than its place (flow input, delay `init`, non-`rt` fn argument)";
    E0816 = 816,  Flow,           "`init` is omitted, but the value type does not satisfy `Default`";
    E0817 = 817,  Flow,           "a flow makes an instance of itself";
    E0818 = 818,  Flow,           "`@mem` in a wrong place or with an unknown memory name";
    E0819 = 819,  Flow,           "state with bulk memory placed in a plain value";
    E0820 = 820,  Flow,           "the memory of an exported flow exceeds the budget of the target";
    E0821 = 821,  Flow,           "flow-only syntax used outside a flow";
    E0901 = 901,  Rt,             "`rt` function calls a non-`rt` function";
    E0902 = 902,  Rt,             "`rt` function has `Alloc` in its effect row";
    E0903 = 903,  Rt,             "`rt` function is recursive";
    E0904 = 904,  Rt,             "`rt` function has a `blocking` effect in its effect row";
    E0905 = 905,  Rt,             "`rt` function has an effect that is not an rt effect in its effect row";
    E1010 = 1010, Ffi,            "the portable core reaches an `extern` function";
    E1011 = 1011, Ffi,            "exported C names collide";
    E1101 = 1101, Manifest,       "the manifest is not valid TOML";
    E1102 = 1102, Manifest,       "unknown table or key in the manifest";
    E1103 = 1103, Manifest,       "a manifest value has the wrong type or form";
    E1104 = 1104, Manifest,       "a required manifest key is missing";
}

fn explain_text(code: &str) -> Option<&'static str> {
    // Explanations live in `explain/<code>.md`; add an arm when one is written.
    match code {
        "E0010" => Some(include_str!("../explain/E0010.md")),
        "E0811" => Some(include_str!("../explain/E0811.md")),
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
    fn as_str_matches_number() {
        for &c in Code::ALL {
            assert_eq!(c.as_str(), format!("E{:04}", c.number()));
            assert_eq!(Code::parse(c.as_str()), Some(c));
        }
    }
}
