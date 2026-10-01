//! Registry of diagnostic codes (spec §18.1, `docs/implementation-tasks.md` §5).
//!
//! Every code the compiler can emit is listed here. The category follows the
//! numeric range of the spec table; a test checks that each code lies in the
//! range of its category.

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
    /// E05xx: exhaustiveness.
    Exhaustiveness,
    /// E06xx: effects, `Alloc`, target provides, policy.
    Effects,
    /// E07xx: argument modes, exclusivity, affine values, second-class values.
    Modes,
    /// E08xx: flow (ordering, rates, delays, `@param`, `~`).
    Flow,
    /// E09xx: rt.
    Rt,
    /// E10xx: FFI, unsafe, transpile.
    Ffi,
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
    E0003 = 3,    Syntax,         "`else` must be on the same line as the closing `}`";
    E0010 = 10,   Syntax,         "binary operators from different groups mixed without parentheses";
    E0011 = 11,   Syntax,         "`as` expression used as an operand without parentheses";
    E0012 = 12,   Syntax,         "prefix operators stacked without parentheses";
    E0020 = 20,   Syntax,         "syntax from another language; see the suggested Onsa form";
    E0200 = 200,  Unsupported,    "feature not supported in this version of the compiler";
    E0302 = 302,  Names,          "cannot find this name";
    E0303 = 303,  Names,          "name is not visible here";
    E0304 = 304,  Names,          "a binding with this name is already visible (no shadowing)";
    E0305 = 305,  Names,          "a declaration has the same name as a flow in this module";
    E0306 = 306,  Names,          "duplicate `test` name in this module";
    E0310 = 310,  Names,          "cyclic module import";
    E0320 = 320,  Names,          "name does not follow the naming rule for its kind";
    E0401 = 401,  Types,          "type mismatch";
    E0405 = 405,  Types,          "the type of this literal cannot be determined";
    E0406 = 406,  Types,          "a type parameter cannot be determined from arguments or the expected type";
    E0407 = 407,  Types,          "the result of a `const` is not Copy or a statically placeable Shared value";
    E0408 = 408,  Types,          "literal is out of range for its type";
    E0410 = 410,  Types,          "struct literal field error (missing, unknown, or duplicate field)";
    E0411 = 411,  Types,          "`as` only widens; use a conversion method";
    E0412 = 412,  Types,          "wrong number of arguments";
    E0413 = 413,  Types,          "no such field or method";
    E0414 = 414,  Types,          "`?` needs a matching Option/Result return type";
    E0415 = 415,  Types,          "assignment target is not a place";
    E0416 = 416,  Types,          "type does not satisfy the bound";
    E0420 = 420,  Types,          "the type of this operand must be known here; add an annotation";
    E0421 = 421,  Types,          "typed hole";
    E0501 = 501,  Exhaustiveness, "`match` is not exhaustive";
    E0502 = 502,  Exhaustiveness, "refutable pattern in `let`";
    E0610 = 610,  Effects,        "effect is not provided by the target";
    E0701 = 701,  Modes,          "cannot modify this place";
    E0702 = 702,  Modes,          "the same place is passed as `inout` twice in one call";
    E0703 = 703,  Modes,          "argument mode does not match the parameter";
    E0704 = 704,  Modes,          "value used after it was moved";
    E0710 = 710,  Modes,          "second-class value used outside an argument position";
    E0711 = 711,  Modes,          "borrowed Affine value passed as `move`";
    E0712 = 712,  Modes,          "closure cannot capture this value";
    E0713 = 713,  Modes,          "calling an `inout self` method needs `!` after the name";
    E0714 = 714,  Modes,          "`!` on a method that does not take `inout self`";
    E0801 = 801,  Flow,           "name used before its definition in a flow (only `prev`/`delay`/`vdelay` may look back)";
    E0805 = 805,  Flow,           "a function with effects cannot be called from a flow";
    E0806 = 806,  Flow,           "this form is not allowed in a flow body";
    E0807 = 807,  Flow,           "`delay` with length 1; write `prev` instead";
    E0808 = 808,  Flow,           "delay length must be a compile-time constant";
    E0809 = 809,  Flow,           "`@param` is missing, misplaced, or malformed";
    E0810 = 810,  Flow,           "value type of a rate must be Copy, and nested arrays cannot cross the boundary";
    E0811 = 811,  Flow,           "calling a flow creates a stateful instance and needs `~`";
    E0812 = 812,  Flow,           "`~` used on something that is not a flow";
    E0813 = 813,  Flow,           "first argument of `prev`/`delay`/`vdelay` must be `Sig` rate";
    E0814 = 814,  Flow,           "`init` of `prev`/`delay`/`vdelay` must be `Init` rate or constant";
    E0815 = 815,  Flow,           "argument rate is higher than the flow input's declared rate";
    E0901 = 901,  Rt,             "`rt` function calls a non-`rt` function";
    E0902 = 902,  Rt,             "`rt` function has `Alloc` in its effect row";
    E0903 = 903,  Rt,             "`rt` function is recursive";
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
