//! What this version of the compiler cannot handle (E0200, spec §18.1, S-224):
//! the one closed list.
//!
//! Every E0200 names one [`Feature`] of this list, and is made here
//! ([`Feature::diagnostic`], or [`Feature::usage`] for the errors of a
//! target's settings that are not diagnostics yet). `onsa explain E0200`
//! prints the same list ([`explain`]), so the list and the places that report
//! E0200 cannot disagree (plan D-15). A self-test checks that no other code
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
    EffectDefinitions: Language, "effect definitions", None;
    HandlerDefinitions: Language, "handler declarations", None;
    EffectHandlers: Language, "effect handlers (`handle ... with`)", None;
    /// `{}`: the effect's name.
    Effects: Language, "effects other than `Alloc` (`{}`)", None;
    Extern: Language, "`extern` blocks", None;
    Unsafe: Language, "`unsafe` blocks (FFI)", None;
    Ptr: Language, "`Ptr` (FFI)", None;
    UserTargets: Language, "`target` declarations outside `std` (they need a build target)", None;
    ConstGenericKinds: Language, "const generics other than `U32`", None;
    /// `{}`: the derived trait.
    Derive: Language, "`@derive({})` (needs `Str`)", None;
    ArrayLengthExprs: Language, "expressions as array lengths",
        Some("write the length as a literal or as the name of a constant");
    ComputedArrayLengths: Language, "constants computed by expressions as array lengths",
        Some("give the constant a literal value, or write the length as a literal");
    CtlOutputs: Language, "`Ctl` outputs of flows (§19)", None;
    Iteration: Language, "iteration over types other than arrays, `Span`, `Buf` and `Array`", None;
    FlowSelfInstance: Language, "a flow that instantiates itself", None;
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
    OrPatternBindings: Language, "or-patterns with bindings", Some("write one arm for each alternative");
    Closures: Language, "anonymous functions anywhere but as the argument of `array.from_fn`", None;
    FnValues: Language, "function values", None;
    /// S-239: the syntax reads `name::[…]` (W3-19); the name and type stages
    /// give the list to the item from W4-13.
    TypeArgsInExpressions: Language, "instantiating an item with type arguments written in an expression (`name::[…]`)", None;
    VariantCtorValues: Language, "variant constructors as function values", None;
    CallsThroughFnValues: Language, "calls through function values", None;
    FromFnValue: Language, "`array.from_fn` with a non-literal function value",
        Some("pass an anonymous function, or a function by its name");
    PlanarTemporary: Language, "planar spans of a temporary", Some("bind the value to a name with `let` first");
    /// `{}`, `{}`: the method's name and the receiver's type.
    Methods: Language, "the method `{}` on `{}`", None;
    ConstBindings: Language, "a `const` initializer with local bindings", None;
    /// `{}`: the function's path (`std.test.gen.f32`). W2-03: `onsa test`
    /// finds them before it runs the tests.
    InterpreterStdFn: Language, "the `std` function `{}` in `onsa test` (the interpreter)", None;

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

    /// The text of an error that is not a diagnostic yet (a target's settings
    /// read by `onsa build`, until the manifest reports them, S-154).
    pub fn usage(self, details: &[&str]) -> String {
        format!("{} ({})", self.message(details), Code::E0200.as_str())
    }
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
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    #[test]
    fn names_are_distinct_and_details_fill_in_order() {
        let names: BTreeSet<&str> = Feature::ALL.iter().map(|f| f.name()).collect();
        assert_eq!(names.len(), Feature::ALL.len());
        assert_eq!(
            Feature::BulkInType.phrase(&["A", "B"]),
            "a flow with a bulk region (`A`) used inside another type (`B`)"
        );
        assert_eq!(Feature::Methods.list_phrase(), "the method `…` on `…`");
        assert_eq!(Feature::Methods.phrase(&["foo", "F32"]), "the method `foo` on `F32`");
        // another number of details than the phrase takes is an internal error
        for details in [&[][..], &["foo"][..], &["a", "b", "c"][..]] {
            let r = std::panic::catch_unwind(|| Feature::Methods.phrase(details));
            let bug = r.expect_err("a wrong number of details is a bug");
            assert!(bug.downcast_ref::<crate::internal::InternalBug>().is_some());
        }
        assert_eq!(Feature::Buf.message(&[]), "the C backend does not support `Buf` (heap buffers) in this version");
        let d = Feature::ValueMatch.diagnostic(Stage::Build, Span::empty(crate::FileId(0), 0), &[]);
        assert_eq!(d.code, Code::E0200);
        assert_eq!(d.notes.len(), 1);
        assert!(d.notes[0].span.is_none());
    }

    #[test]
    fn explain_lists_every_feature_once() {
        let text = Code::E0200.explain().expect("E0200 has an explanation");
        assert!(!Feature::ALL.is_empty());
        for &f in Feature::ALL {
            let line = list_line(f);
            assert_eq!(text.lines().filter(|l| *l == line).count(), 1, "{line}");
        }
    }

    /// The `.rs` files under `dir`, recursively.
    fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
            .map(|e| e.unwrap().path())
            .collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                rust_files(&p, out);
            } else if p.extension().is_some_and(|x| x == "rs") {
                out.push(p);
            }
        }
    }

    /// The text without comments (each comment a space), and for each
    /// character whether it is inside a string or character literal.
    fn lex(text: &str) -> (Vec<char>, Vec<bool>) {
        let c: Vec<char> = text.chars().collect();
        let (mut out, mut lit) = (Vec::new(), Vec::new());
        let at = |i: usize| c.get(i).copied();
        let mut i = 0;
        while i < c.len() {
            let ch = c[i];
            if ch == '/' && at(i + 1) == Some('/') {
                while i < c.len() && c[i] != '\n' {
                    i += 1;
                }
                out.push(' ');
                lit.push(false);
                continue;
            }
            if ch == '/' && at(i + 1) == Some('*') {
                let mut depth = 0;
                while i < c.len() {
                    if c[i] == '/' && at(i + 1) == Some('*') {
                        depth += 1;
                        i += 2;
                    } else if c[i] == '*' && at(i + 1) == Some('/') {
                        depth -= 1;
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        i += 1;
                    }
                }
                out.push(' ');
                lit.push(false);
                continue;
            }
            let ident_before = i > 0 && (c[i - 1].is_alphanumeric() || c[i - 1] == '_');
            // A literal from `i` to `end` (exclusive).
            let mut end = None;
            if !ident_before && (ch == 'r' || (ch == 'b' && at(i + 1) == Some('r'))) {
                let mut j = i + if ch == 'b' { 2 } else { 1 };
                let mut hashes = 0;
                while at(j) == Some('#') {
                    hashes += 1;
                    j += 1;
                }
                if at(j) == Some('"') {
                    j += 1;
                    while j < c.len() && !(c[j] == '"' && (1..=hashes).all(|k| at(j + k) == Some('#'))) {
                        j += 1;
                    }
                    end = Some(j + 1 + hashes);
                }
            }
            if end.is_none() && ch == '"' {
                let mut j = i + 1;
                while j < c.len() && c[j] != '"' {
                    j += if c[j] == '\\' { 2 } else { 1 };
                }
                end = Some(j + 1);
            }
            if end.is_none() && ch == '\'' {
                if at(i + 1) == Some('\\') {
                    let mut j = i + 2;
                    while j < c.len() && c[j] != '\'' {
                        j += 1;
                    }
                    end = Some(j + 1);
                } else if at(i + 2) == Some('\'') {
                    end = Some(i + 3);
                }
            }
            match end {
                Some(e) => {
                    let e = e.min(c.len());
                    out.extend_from_slice(&c[i..e]);
                    lit.extend(std::iter::repeat_n(true, e - i));
                    i = e;
                }
                None => {
                    out.push(ch);
                    lit.push(false);
                    i += 1;
                }
            }
        }
        (out, lit)
    }

    /// The end of the item that starts at `i` (after its attributes): its
    /// `;`, or the `}` that closes its first `{`, outside literals and
    /// outside `(...)` / `[...]`.
    fn item_end(c: &[char], lit: &[bool], mut i: usize) -> usize {
        let mut depth = 0i32;
        while i < c.len() {
            if !lit[i] {
                match c[i] {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    ';' if depth == 0 => return i + 1,
                    '{' if depth == 0 => {
                        let mut braces = 0;
                        while i < c.len() {
                            if !lit[i] {
                                if c[i] == '{' {
                                    braces += 1;
                                } else if c[i] == '}' {
                                    braces -= 1;
                                    if braces == 0 {
                                        return i + 1;
                                    }
                                }
                            }
                            i += 1;
                        }
                        return i;
                    }
                    _ => {}
                }
            }
            i += 1;
        }
        i
    }

    /// The code of a source file without comments and without the items
    /// marked `#[cfg(test)]` (a `mod x;` to its `;`, an item with a body to
    /// its closing brace), and the names of the `#[cfg(test)] mod x;` files.
    fn non_test_code(text: &str) -> (String, Vec<String>) {
        let (c, lit) = lex(text);
        let attr: Vec<char> = "#[cfg(test)]".chars().collect();
        let mut keep = vec![true; c.len()];
        let mut test_mods = Vec::new();
        let mut i = 0;
        while i + attr.len() <= c.len() {
            if lit[i] || c[i..i + attr.len()] != attr[..] {
                i += 1;
                continue;
            }
            let mut j = i + attr.len();
            // further attributes of the same item
            loop {
                while j < c.len() && c[j].is_whitespace() {
                    j += 1;
                }
                if c.get(j) == Some(&'#') && c.get(j + 1) == Some(&'[') {
                    // to the `]` that closes the attribute
                    let mut depth = 0;
                    j += 1;
                    while j < c.len() {
                        if !lit[j] {
                            match c[j] {
                                '[' => depth += 1,
                                ']' => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                _ => {}
                            }
                        }
                        j += 1;
                    }
                    j += 1;
                } else {
                    break;
                }
            }
            let end = item_end(&c, &lit, j);
            let item: String = c[j..end].iter().collect();
            let words: Vec<&str> =
                item.split(|x: char| !(x.is_alphanumeric() || x == '_')).filter(|w| !w.is_empty()).collect();
            if item.trim_end().ends_with(';')
                && let Some(k) = words.iter().position(|w| *w == "mod")
                && let Some(name) = words.get(k + 1)
            {
                test_mods.push(name.to_string());
            }
            for k in keep.iter_mut().take(end).skip(i) {
                *k = false;
            }
            i = end;
        }
        (c.iter().zip(&keep).filter(|(_, k)| **k).map(|(x, _)| *x).collect(), test_mods)
    }

    /// The files of the modules `test_mods` declared in `file`.
    fn module_paths(file: &Path, test_mods: &[String]) -> Vec<PathBuf> {
        let stem = file.file_stem().unwrap().to_string_lossy();
        let dir = if ["lib", "main", "mod"].contains(&stem.as_ref()) {
            file.parent().unwrap().to_path_buf()
        } else {
            file.with_extension("")
        };
        test_mods.iter().flat_map(|m| [dir.join(format!("{m}.rs")), dir.join(m)]).collect()
    }

    #[test]
    fn the_scan_drops_comments_and_test_items_only() {
        let src = "#[cfg(test)] mod t;\nfn a() { let s = \"// {\"; let c = '{'; }\n\
                   #[cfg(test)]\n#[allow(x)]\nfn b(x: [u8; 2]) {\n  if x { E0200 }\n}\n\
                   /* E0200 */ const K: u32 = 1; // E0200\nfn d() { E0200 }\n";
        let (code, mods) = non_test_code(src);
        assert_eq!(mods, ["t"]);
        assert!(code.contains("fn a()") && code.contains("\"// {\"") && code.contains("const K"), "{code}");
        assert!(!code.contains("fn b") && !code.contains("mod t"), "{code}");
        assert_eq!(code.matches("E0200").count(), 1, "{code}");
        assert!(code.contains("fn d() { E0200 }"), "{code}");
    }

    /// Every E0200 is made here, and every feature is reported somewhere
    /// (D-15): the other crates name a [`Feature`], never the code.
    #[test]
    fn every_e0200_comes_from_the_list_and_every_feature_is_reported() {
        let crates = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let mut files = Vec::new();
        for entry in std::fs::read_dir(crates).unwrap() {
            let src = entry.unwrap().path().join("src");
            if src.is_dir() {
                rust_files(&src, &mut files);
            }
        }
        let this = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut code_of = Vec::new();
        let mut test_files = Vec::new();
        for f in &files {
            let (code, test_mods) = non_test_code(&std::fs::read_to_string(f).unwrap());
            test_files.extend(module_paths(f, &test_mods));
            code_of.push((f, code));
        }
        let mut used = BTreeSet::new();
        let mut scanned = 0;
        for (f, code) in &code_of {
            if f.starts_with(&this) || test_files.iter().any(|t| f.starts_with(t)) {
                continue;
            }
            scanned += 1;
            // the code, a name of it (`use onsa_diag::Code as C; C::E0200`)
            // or a text that claims it: only this list makes an E0200
            assert!(!code.contains("E0200"), "{} names E0200 itself: name a `Feature`", f.display());
            for (i, _) in code.match_indices("Feature::") {
                let rest = &code[i + "Feature::".len()..];
                let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                used.insert(name);
            }
        }
        assert!(scanned > 50, "the scan found {scanned} source files only");
        let unused: Vec<&str> = Feature::ALL.iter().map(|f| f.name()).filter(|n| !used.contains(*n)).collect();
        assert!(unused.is_empty(), "features of the list that nothing reports: {unused:?}");
    }
}
