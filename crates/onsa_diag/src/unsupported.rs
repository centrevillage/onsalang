//! What this version of the compiler cannot handle (E0200, spec §18.1, S-224):
//! the one closed list.
//!
//! Every E0200 names one [`Feature`] of this list, and is made here
//! ([`Feature::diagnostic`]). `onsa explain E0200` prints the same list
//! ([`explain`]), so the list and the places that report E0200 cannot
//! disagree (plan D-15). A self-test checks that no other code
//! makes an E0200 and that every feature of the list is reported somewhere.
//!
//! A feature is a noun phrase that completes "this version does not support
//! ..." (or "the C backend does not support ... in this version" for
//! [`Group::CBackend`]); `{}` in it is filled with a detail of the use (a
//! method's name, a type's name), in order. The note, when there is one, is a
//! form this version accepts (§18.1): it goes on the diagnostic as a note
//! without a position.

use crate::{Code, Diagnostic, Span, Stage};

/// Where a feature belongs, for the phrasing and for the groups of the list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Group {
    /// Declarations, expressions and types, whatever the target.
    Language,
    /// What the C backend does not generate.
    CBackend,
    /// Values of the manifest's targets.
    Manifest,
}

impl Group {
    pub const ALL: &'static [Group] = &[Group::Language, Group::CBackend, Group::Manifest];

    /// The heading of the group in `onsa explain E0200`.
    pub fn heading(self) -> &'static str {
        match self {
            Group::Language => "The language",
            Group::CBackend => "The C backend",
            Group::Manifest => "The manifest",
        }
    }
}

macro_rules! features {
    ($( $(#[$doc:meta])* $name:ident: $group:ident, $what:literal, $note:expr; )*) => {
        /// One feature or form this version cannot handle (see the module).
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Feature {
            $( $(#[$doc])* $name, )*
        }

        impl Feature {
            /// Every feature, in the order of the list.
            pub const ALL: &'static [Feature] = &[ $( Feature::$name, )* ];

            pub fn group(self) -> Group {
                match self { $( Feature::$name => Group::$group, )* }
            }

            /// The noun phrase, with `{}` for each detail.
            pub fn what(self) -> &'static str {
                match self { $( Feature::$name => $what, )* }
            }

            /// A form this version accepts in its place, if there is one.
            pub fn note(self) -> Option<&'static str> {
                match self { $( Feature::$name => $note, )* }
            }

            /// The variant's name (`ValueMatch`), for the self-test.
            pub fn name(self) -> &'static str {
                match self { $( Feature::$name => stringify!($name), )* }
            }
        }
    };
}

features! {
    // ------------------------------------------------------------ the language
    TraitDefinitions: Language, "trait definitions", None;
    TraitImpls: Language, "trait implementations (`impl Trait for Type`)", None;
    TraitBounds: Language, "user-defined traits as bounds", None;
    /// `{}`: the trait of the prelude that is not a bound in this version (R-312).
    PreludeBounds: Language, "the trait `{}` as a bound", None;
    /// S-862: the name is reserved in the prelude (W5-17).
    RelaxedEscape: Language, "the bound `?Escape`, which lets a type parameter take second-class types", None;
    EffectDefinitions: Language, "effect definitions", None;
    HandlerDefinitions: Language, "handler declarations", None;
    EffectHandlers: Language, "effect handlers (`handle ... with`)", None;
    /// `{}`: the effect's name.
    Effects: Language, "effects other than `Alloc` (`{}`)", None;
    /// S-888: which clock a `panic` of a flow body takes (§11.3) is open.
    PanicInFlow: Language, "`panic` in a flow body", None;
    Extern: Language, "`extern` blocks", None;
    /// S-596: with the dependencies other than `std` (§19.1). Its note is
    /// the `use` of the module that defines the names (`onsa_sema`).
    Reexports: Language, "re-exports (`pub use`)", None;
    Unsafe: Language, "`unsafe` blocks (FFI)", None;
    Ptr: Language, "`Ptr` (FFI)", None;
    UserTargets: Language, "`target` declarations outside `std` (they need a build target)", None;
    ConstGenericKinds: Language, "const generics other than `U32`", None;
    /// S-697: the defaults of the fields are checked from W5-22 U3.
    FieldDefaults: Language, "the default of a field (`y: F32 = 0.0`)", None;
    /// S-697: `...` fills the fields from W5-22 U4.
    StructLitRest: Language, "`...` at the end of a struct literal", None;
    /// `{}`: the derived trait.
    Derive: Language, "deriving `{}` at the head of a type", None;
    /// S-43: the placing of a delay line in the bulk storage, with E0818 to
    /// E0820 (W9-06).
    MemStorage: Language, "the storage attribute `@mem` of a `let`", None;
    ArrayLengthExprs: Language, "expressions as array lengths",
        Some("write the length as a literal or as the name of a constant");
    ComputedArrayLengths: Language, "constants computed by expressions as array lengths",
        Some("give the constant a literal value, or write the length as a literal");
    /// `{}`: `if~` or `match~` (S-110, W7-06; K-02).
    TildeBranches: Language, "`{}`, which evaluates every branch", None;
    /// K-08, S-110: what the branch does not evaluate holds state (W7-06).
    StatefulInBranch: Language,
        "a flow instance, a delay or a `par~` where it is evaluated on some samples only (a branch of `if` or `match`, a guard, the right of `&&` / `||`)",
        Some("bind it with a `let` before the expression that holds it");
    /// K-08, R-13: the store of the inner delay comes first (W7-07).
    NestedDelays: Language, "a delay inside the first argument of a delay",
        Some("bind the inner delay with a `let`, and delay that name");
    /// K-02: `e at k` evaluates `e` at its own clock (W7-02).
    ClockPromotion: Language, "`at` that makes a computed expression faster than its operands",
        Some("bind the expression with a `let`, and write `at` on its name");
    /// `{}`: the value type. K-02, S-29: `T.default()` (W7-07).
    DefaultInit: Language, "the omitted `init` of a delay whose value type `{}` is not a number",
        Some("write the `init`");
    /// `{}`: the clock. R-17, S-33: hoisting computes it at `init` (W7-05).
    NonRtCallAtClock: Language, "a call of a function that is not `rt` in an expression at the clock `{}`",
        Some("bind the call with a `let` of its own, which is computed at `init`");
    /// R-03: the look-back of a replica (W7-04).
    FeedbackInPar: Language, "a feedback reference `^name` inside a `par~`", None;
    /// §11.4, S-565: the time since `reset` in ticks (W7-09, R-288).
    SampleTick: Language, "the builtin `sample_tick()` of a flow", None;
    /// S-44, S-116: its E0020 is the names stage's (W7-04).
    CaretOnVisible: Language, "`^` on a name that is defined above it (a redundant mark)", None;
    Iteration: Language, "iteration over types other than arrays, `Span`, `Buf` and `Array`", None;
    Equality: Language, "equality on this type", None;
    OrderingAggregates: Language, "ordering comparisons of aggregate values", None;
    /// R-06: the general path of a value `match` (W8-06).
    ValueMatch: Language,
        "the value of a `match` that is not a plain switch on the variants of one enum (a guard, or a literal, tuple, struct, nested or alternative pattern)",
        Some("compute the value in a function of its own, where a `match` written as a statement assigns a `var` in each arm and the function returns it; or nest plain switches on one enum each");
    /// R-08, S-192: `?` leaves the anonymous function (W8-09).
    TryInFromFn: Language, "`?` inside an anonymous function passed to `array.from_fn`",
        Some("write the body as a named function `fn(i: U32) -> T` and pass it to `array.from_fn` by its name (`?` and `return` work there; it cannot read the caller's locals), or `match` on the `Option` or `Result` so that the anonymous function's last expression is the element");
    /// R-08, S-192: `return` leaves the anonymous function (W8-09).
    ReturnInFromFn: Language, "`return` inside an anonymous function passed to `array.from_fn`",
        Some("write the body as a named function `fn(i: U32) -> T` and pass it to `array.from_fn` by its name (`?` and `return` work there; it cannot read the caller's locals), or give the element as the anonymous function's last expression, with `if` / `else` for the early case");
    StrPatterns: Language, "`Str` patterns", None;
    StrValues: Language, "`Str` values", None;
    /// `{}`: the type's name.
    SharedTypes: Language, "the Shared type `{}`", None;
    /// S-610, R-85, W4-05 table 5: `{}`: the type of the `const`, holding a Shared
    /// value or a type parameter not `Copy` (placed statically from phase 2).
    SharedConsts: Language, "a `const` of the type `{}`, which holds or may hold a Shared value", None;
    /// R-85 (5), S-80: whether the capture copies or borrows is phase 2's (§5.4).
    CapturedShared: Language, "the capture of a Shared value by an anonymous function (phase 2)", None;
    OrPatternBindings: Language, "or-patterns with bindings", Some("write one arm for each alternative");
    Closures: Language, "anonymous functions anywhere but as the argument of `array.from_fn`", None;
    FnValues: Language, "function values", None;
    /// R-294: `{}`: a name the spec gives a builtin type (`Str.from_utf8`),
    /// of the table `MISSING` of `onsa_sema`'s `builtin.rs`.
    BuiltinName: Language, "the builtin name `{}`", None;
    /// S-239: the syntax reads `name::[…]` (W3-19); the name and type stages
    /// give the list to the item from W5-10.
    TypeArgsInExpressions: Language, "instantiating an item with type arguments written in an expression (`name::[…]`)", None;
    /// S-224, S-257: the `for` loop over `a..=b` that ends when `b` is the
    /// type's maximum (W8-03); never lowered as `..<` (R-81).
    InclusiveRangeFor: Language, "a range with its end (`a..=b`) in a `for` head",
        Some("write `a..<b + 1` when `b + 1` fits in the type");
    /// S-224, S-257: the `b - a + 1` instances of `par~ i in a..=b` (W7-04).
    InclusiveRangePar: Language, "a range with its end (`a..=b`) in a `par~` head", None;
    /// R-195: the values of the constant expressions of §4.5 other than an
    /// integer literal and a `const` with a literal value (W7-02).
    FlowConstExprs: Language, "computing the value of a constant expression in a flow (a `par~` bound, a delay length, the maximum of a `vdelay~`)",
        Some("write it as an integer literal, or as a `const` whose value is an integer literal");
    VariantCtorValues: Language, "variant constructors as function values", None;
    CallsThroughFnValues: Language, "calls through function values", None;
    /// S-85, X-8: the drop of the rest where a field is taken out (W8-04).
    TakenFields: Language, "taking a field out of a value (the rest is dropped)", None;
    FromFnValue: Language, "`array.from_fn` with a non-literal function value",
        Some("pass an anonymous function, or a function by its name");
    PlanarTemporary: Language, "planar spans of a temporary", Some("bind the value to a name with `let` first");
    /// `{}`, `{}`: the method's name and the receiver's type.
    Methods: Language, "the method `{}` on `{}`", None;
    ConstBindings: Language, "a `const` initializer with local bindings", None;
    /// `{}`: the function's path (`std.test.gen.f32`). W2-03: `onsa test`
    /// finds them before it runs the tests.
    InterpreterStdFn: Language, "the `std` function `{}` in `onsa test` (the interpreter)", None;
    /// `{}`, `{}`: the function's path and its type arguments (spec §15.2,
    /// S-69): the compiler has no primitive of it for them.
    StdTargetType: Language, "the `std` function `{}` for the type `{}`", None;
    /// The reserved words (§2.2, §19.1, S-169, S-279): wherever one is read
    /// (`onsa_syntax::token::KEYWORDS`).
    DerivedClocks: Language, "the declaration of a derived clock (the reserved word `clock`)", None;
    ConditionalInstances: Language, "running an instance on a condition (the reserved word `when`)", None;
    ResetInstances: Language, "resetting an instance to its initial state (the reserved word `reset_if`)", None;
    SerialFlows: Language, "the serial copies of a flow, `ser~` (the reserved word `ser`)", None;
    /// Not yet a keyword of the lexer (W5-11): read where a name is
    /// declared or taken (`onsa_sema`).
    StaticMarks: Language, "the mark of what is static only (the reserved word `static`)", None;
    /// S-96, R-122: the role of the root's `tests/` is the second phase's
    /// (§15.1, §19.1); each `.onsa` file there is one, at its head.
    PackageTests: Language, "the `tests/` directory of the package root (its `.onsa` files are not modules)",
        Some("put the file in a directory of another name, where it is a module of the package (the role of the root's `tests/` comes in a later version, §19.1)");

    // ----------------------------------------------------------- the C backend
    Buf: CBackend, "`Buf` (heap buffers)", None;
    /// `{}`: what is exported (a parameter, the result, a signal).
    ExportNonScalar: CBackend, "{} of a non-scalar type in an export", None;
    ProcessParams: CBackend, "this `process` parameter shape", None;
    ExportAggregateReturn: CBackend, "exporting a function that returns an aggregate", None;
    /// `{}`: the parameter's name.
    ExportParam: CBackend, "the parameter `{}` of an exported function (only scalars and spans of scalars)", None;
    /// `{}`, `{}`: the flow's state type and the type that holds it.
    BulkInType: CBackend, "a flow with a bulk region (`{}`) used inside another type (`{}`)",
        Some("export the flow on its own");
    BulkBuild: CBackend, "building a flow state with a bulk region anywhere but in its `init`", None;
    BulkCopy: CBackend, "copying a flow state with a bulk region", None;
    /// `{}`: the type's name.
    OpaqueType: CBackend, "the opaque type `{}`", None;
    ConstInitializer: CBackend, "this `const` initializer (evaluated at build time)", None;
    /// `{}`: the function's name.
    TargetFn: CBackend, "the `target` function `{}` (no implementation for C)", None;
    /// `{}`: the function's name.
    StdFn: CBackend, "the `std` function `{}` (no C implementation)", None;

    // ------------------------------------------------------------ the manifest
    /// `{}`: the value.
    ManifestLang: Manifest, "`lang = \"{}\"` (only `c`)", None;
    /// `{}`: the value.
    ManifestKind: Manifest, "`kind = \"{}\"` (only `staticlib` and `source`)", None;
    /// `{}`: the effect.
    ManifestProvides: Manifest, "`provides` other than `Alloc` (`{}`)", None;
    ManifestBind: Manifest, "`bind` in a target", None;
    /// `{}`: the value. R-166, §12.5.
    ManifestMainFrame: Manifest, "`main_frame = \"{}\"` (only `stack`)", None;
    /// `{}`: the value. §15.5 (W10-05).
    ManifestFp: Manifest, "`fp = \"{}\"` (only `strict`)", None;
    /// §12.4 (W9-06).
    ManifestBulk: Manifest, "`memory.bulk = true`", None;
    /// §12.4 (W9-05, W9-06).
    ManifestBudgets: Manifest, "the budgets of `memory` (`fast_budget`, `bulk_budget`)", None;
    /// `{}`: the value (S-824); its note, what this version knows, is the driver's.
    ManifestPlatform: Manifest, "the platform `\"{}\"`", None;
    /// `{}`: the kind; `{}`: the platform (§15.3, S-161).
    ManifestCross: Manifest, "`kind = \"{}\"` for a platform other than the host (`{}`)",
        Some("`kind = \"source\"` with `lang = \"c\"` gives the C sources for any platform");
    /// `{}`: the package (§15.3: reported by the check of the manifest, for every command).
    ManifestDependency: Manifest, "dependencies other than `std` (`{}`)", None;
}

impl Feature {
    /// The number of details the phrase takes (its `{}`).
    pub fn arity(self) -> usize {
        self.what().matches("{}").count()
    }

    /// The phrase with each `{}` filled by `details`, in order. A use that
    /// passes another number of details than the phrase takes is a bug of
    /// the compiler (an internal error, S-67), not a phrase to guess.
    pub fn phrase(self, details: &[&str]) -> String {
        self.phrase_at(None, details)
    }

    fn phrase_at(self, span: Option<Span>, details: &[&str]) -> String {
        if details.len() != self.arity() {
            crate::internal::bug(
                span,
                format!(
                    "the unsupported feature `{}` takes {} detail(s), given {}",
                    self.name(),
                    self.arity(),
                    details.len()
                ),
            );
        }
        let mut out = String::new();
        for (i, part) in self.what().split("{}").enumerate() {
            if i > 0 {
                out.push_str(details[i - 1]);
            }
            out.push_str(part);
        }
        out
    }

    /// The phrase as the list of `onsa explain E0200` shows it: `…` for
    /// each detail.
    pub fn list_phrase(self) -> String {
        self.what().replace("{}", "…")
    }

    fn message_at(self, span: Option<Span>, details: &[&str]) -> String {
        let phrase = self.phrase_at(span, details);
        match self.group() {
            Group::CBackend => format!("the C backend does not support {phrase} in this version"),
            Group::Language | Group::Manifest => format!("this version does not support {phrase}"),
        }
    }

    /// The message of the E0200.
    pub fn message(self, details: &[&str]) -> String {
        self.message_at(None, details)
    }

    /// The E0200 for a use of the feature at `span`, reported by `stage`,
    /// with the note of the form this version accepts.
    pub fn diagnostic(self, stage: Stage, span: Span, details: &[&str]) -> Diagnostic {
        let d = Diagnostic::new(stage, Code::E0200, span, self.message_at(Some(span), details));
        match self.note() {
            Some(n) => d.with_rule(n),
            None => d,
        }
    }
}

/// Whether `d` is an E0200: a feature this version does not have, which a
/// command that can go on without the stage leaves out.
pub fn is_unsupported(d: &Diagnostic) -> bool {
    d.code == Code::E0200
}

/// The long explanation of E0200: the text of `explain/E0200.md` and the
/// list of every feature, by group.
pub fn explain() -> String {
    let mut out = String::from(include_str!("../explain/E0200.md"));
    out.push_str("\n## What this version does not support\n");
    for &g in Group::ALL {
        out.push_str(&format!("\n### {}\n\n", g.heading()));
        for &f in Feature::ALL.iter().filter(|f| f.group() == g) {
            out.push_str(&list_line(f));
            out.push('\n');
        }
    }
    out
}

/// One line of the list in [`explain`].
pub fn list_line(f: Feature) -> String {
    match f.note() {
        Some(n) => format!("- {} — instead: {n}", f.list_phrase()),
        None => format!("- {}", f.list_phrase()),
    }
}

#[cfg(test)]
mod tests;
