//! The table of the attributes (spec §6.5, S-103, S-133, R-36): the one place
//! that knows their names, the places each may be attached to and the closed
//! lists of their values. An attribute out of the table, in a place it cannot
//! be attached to, or with a value out of its list (`@repr`, `@fp`) is E0005
//! of the syntax stage; the parser asks [`check`] where it knows the place
//! (`Parser::check_attrs`). The conditions inside a place and the values of
//! `@param` and `@mem` are the codes of their own, checked later (E0809,
//! E0818). The old attributes (`@derive`, `@relaxed`, `@bulk`, `@mem(fast)`)
//! are rows of the table of the forms of other languages ([`crate::foreign`]),
//! asked first.

use onsa_diag::{Code, Diagnostic, Edit, FileId, Fix, Span, Stage};

use crate::token::{Token, TokenKind};

/// `@repr(c)`: the layout of C (§6.5).
pub const REPR: &str = "repr";
/// `@fp(relaxed)`: the operations may be contracted and reassociated (§15.5).
pub const FP: &str = "fp";
/// `@param(…)`: the metadata of an input of a flow (§11.7).
pub const PARAM: &str = "param";
/// `@mem(bulk)`: the storage of a delay line (§12.4).
pub const MEM: &str = "mem";
/// The value of `@fp` that relaxes.
pub const RELAXED: &str = "relaxed";
/// The value of `@repr` for the layout of C.
pub const C: &str = "c";
/// The storage `bulk` of `@mem` (§12.4).
pub const BULK: &str = "bulk";
/// The storage `fast` of `@mem`, the default one (§12.4: `@mem(fast)` is E0020).
pub const FAST: &str = "fast";

/// A place an attribute is written in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Place {
    Struct,
    Fn,
    Flow,
    /// An input of a flow.
    FlowInput,
    /// A `let` statement.
    Let,
    /// Any other place: what it is, for the message ("an enum").
    Other(&'static str),
}

impl Place {
    fn describe(self) -> &'static str {
        match self {
            Place::Struct => "a struct",
            Place::Fn => "a function",
            Place::Flow => "a flow",
            Place::FlowInput => "an input of a flow",
            Place::Let => "a `let`",
            Place::Other(what) => what,
        }
    }
}

/// One attribute of the table.
pub struct Attribute {
    pub name: &'static str,
    /// The places it may be attached to.
    pub places: &'static [Place],
    /// The closed list of its values, when this table checks them (one
    /// value, written as a name in the parentheses).
    pub values: Option<&'static [&'static str]>,
}

/// The attributes (§6.5): no others.
pub static ATTRIBUTES: &[Attribute] = &[
    Attribute { name: REPR, places: &[Place::Struct], values: Some(&[C]) },
    Attribute { name: FP, places: &[Place::Fn, Place::Flow], values: Some(&[RELAXED]) },
    Attribute { name: PARAM, places: &[Place::FlowInput], values: None },
    Attribute { name: MEM, places: &[Place::Let], values: None },
];

/// The attribute of `name` in the table.
pub fn attribute(name: &str) -> Option<&'static Attribute> {
    ATTRIBUTES.iter().find(|a| a.name == name)
}

/// Whether `@name(value)` (`value` the sole argument, a name; `None` for no
/// parentheses) is accepted at `place`: the one test that the table of the
/// forms of other languages asks of a candidate's attribute (S-463).
pub fn accepts(name: &str, value: Option<&str>, place: Place) -> bool {
    attribute(name)
        .is_some_and(|a| a.places.contains(&place) && a.values.is_none_or(|vs| value.is_some_and(|v| vs.contains(&v))))
}

/// The value of the attribute whose parentheses are the tokens `open` and
/// `close` (the tokens the parser reads): the index of the sole argument
/// when it is one name, a `,` after it allowed. Line breaks and comments in
/// parentheses mean nothing (§2.5). The one reading of the value the table
/// checks, for an attribute of Onsa (`Parser::parse_attr`) and for one of
/// other languages (`#[repr(C)]`, `foreign::decls::hash_attribute`).
pub(crate) fn sole_value(tokens: &[Token], open: usize, close: usize) -> Option<usize> {
    let mut code = (open + 1..close).filter(|&i| tokens[i].kind.is_code());
    let value = code.next().filter(|&i| tokens[i].kind == TokenKind::Ident)?;
    match code.next() {
        None => Some(value),
        Some(comma) if tokens[comma].kind == TokenKind::Comma && code.next().is_none() => Some(value),
        Some(_) => None,
    }
}

/// The place of the attributes of a declaration whose keyword is `kind` (§6.5).
pub fn place_of_declaration(kind: TokenKind) -> Place {
    match kind {
        TokenKind::KwFn | TokenKind::KwRt => Place::Fn,
        TokenKind::KwFlow => Place::Flow,
        TokenKind::KwStruct => Place::Struct,
        TokenKind::KwEnum => Place::Other("an enum"),
        TokenKind::KwType => Place::Other("a type alias"),
        TokenKind::KwTrait => Place::Other("a trait"),
        TokenKind::KwImpl => Place::Other("an `impl`"),
        TokenKind::KwEffect | TokenKind::KwBlocking => Place::Other("an effect"),
        TokenKind::KwHandler => Place::Other("a handler"),
        TokenKind::KwConst => Place::Other("a constant"),
        TokenKind::KwUse => Place::Other("a `use`"),
        TokenKind::KwExtern => Place::Other("an `extern` block"),
        TokenKind::KwTarget => Place::Other("a `target` declaration"),
        TokenKind::KwTest => Place::Other("a test"),
        _ => Place::Other("a declaration"),
    }
}

/// An attribute as written, for [`check`].
pub struct Written<'a> {
    /// From the `@` to its last token.
    pub span: Span,
    pub name: &'a str,
    /// The span of the parentheses with what is in them, if any.
    pub args: Option<Span>,
    /// The span and the text of the sole argument when it is one name.
    pub value: Option<(Span, &'a str)>,
    /// The tokens of code in the parentheses (blanks and comments aside).
    pub arguments: Vec<(Span, &'a str)>,
}

/// The rule of the table (the note of its E0005).
const RULE: &str = "the attributes are `@repr(c)` on a struct, `@fp(relaxed)` on a fn or a flow, `@param(…)` on an input of a flow and `@mem(bulk)` on a `let`, and no others (§6.5)";

/// The E0005 of the attribute `w` at `place`, if the table refuses it: a name
/// out of the table, a place it cannot be attached to, or a value out of its
/// list, whose candidates are the values of the list (§6.5).
pub fn check(file: FileId, text: &str, w: &Written, place: Place) -> Option<Diagnostic> {
    let error = |message: String| {
        Diagnostic::new(Stage::Syntax, Code::E0005, w.span, message)
            .with_found(&text[w.span.start as usize..w.span.end as usize])
            .with_rule(RULE)
    };
    let Some(a) = attribute(w.name) else {
        return Some(error(format!("there is no attribute `@{}`", w.name)));
    };
    if !a.places.contains(&place) {
        let places: Vec<&str> = a.places.iter().map(|p| p.describe()).collect();
        return Some(error(format!(
            "`@{}` cannot be attached to {}; it goes on {}",
            w.name,
            place.describe(),
            places.join(" or ")
        )));
    }
    let values = a.values?;
    if w.value.is_some_and(|(_, v)| values.contains(&v)) {
        return None;
    }
    let mut d = error(format!("the value of `@{}` is one of {}", w.name, quoted(values)));
    for v in values {
        let edits = match (w.value, w.args) {
            (Some((span, _)), _) => vec![Edit::replace(span, *v)],
            // The brackets stay, and so does the value among the arguments (S-251, R-238): what is
            // before it and after it goes.
            (None, Some(args)) => match w.arguments.iter().find(|(_, t)| t == v) {
                Some((at, _)) => [(args.start + 1, at.start), (at.end, args.end - 1)]
                    .into_iter()
                    .filter(|(s, e)| s < e)
                    .map(|(s, e)| Edit::delete(Span::new(args.file, s, e)))
                    .collect(),
                None => vec![Edit::replace(Span::new(args.file, args.start + 1, args.end - 1), *v)],
            },
            (None, None) => vec![Edit::insert(file, w.span.end, format!("({v})"))],
        };
        d = d.with_fix(Fix::new(format!("write `@{}({v})`", w.name), edits));
    }
    Some(d)
}

fn quoted(values: &[&str]) -> String {
    values.iter().map(|v| format!("`{v}`")).collect::<Vec<_>>().join(", ")
}
