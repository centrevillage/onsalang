//! The helpers that read or make the C text: the operands kept in order, the conditions, the names.

use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    /// A stable C expression: unaffected by later side effects.
    pub(super) fn is_stable(s: &str) -> bool {
        is_temp(s)
            || s.starts_with("INT")
            || s.starts_with("UINT")
            || s.starts_with("((int")
            || s.starts_with("((uint")
            || s.starts_with(|c: char| c.is_ascii_digit())
            || s == "true"
            || s == "false"
            || s == "NAN"
            || s == "INFINITY"
            || s == "(-INFINITY)"
    }

    /// Evaluate operands in order; earlier operands are saved in temporaries
    /// as soon as a later operand needs statements.
    pub(super) fn operands(&mut self, es: &[&Expr]) -> R<Vec<String>> {
        let mut strs: Vec<String> = Vec::new();
        for e in es {
            let mark = self.out.len();
            let s = self.expr(e)?;
            if self.out.len() != mark {
                // Statements were emitted: snapshot the earlier operands before them.
                let mut decls = String::new();
                for (j, prev) in strs.iter_mut().enumerate() {
                    if !Self::is_stable(prev) {
                        let (t, tn) = self.temp(es[j].ty);
                        for _ in 0..self.indent {
                            decls.push_str("  ");
                        }
                        let _ = writeln!(decls, "{tn} {t} = {prev};");
                        *prev = t;
                    }
                }
                self.out.insert_str(mark, &decls);
            }
            strs.push(s);
        }
        Ok(strs)
    }

    /// The value of `e` in a temporary (or as is when it is a literal, a
    /// temporary, or a plain local: evaluated exactly where it is used).
    pub(super) fn materialize(&mut self, e: &Expr) -> R<String> {
        let s = self.expr(e)?;
        if Self::is_stable(&s) || is_c_ident(&s) {
            return Ok(s);
        }
        let (t, tn) = self.temp(e.ty);
        self.line(&format!("{tn} {t} = {s};"));
        Ok(t)
    }

    /// A place-like C string for `e` (an lvalue, or a temporary holding it).
    pub(super) fn place_like(&mut self, e: &Expr) -> R<String> {
        if let Some(p) = e.as_place() { self.place(&p) } else { self.materialize(e) }
    }

    pub(super) fn materialize_str(&mut self, s: &str, ty: CTy) -> String {
        if Self::is_stable(s) {
            return s.to_string();
        }
        let (t, tn) = self.temp(ty);
        self.line(&format!("{tn} {t} = {s};"));
        t
    }
}

/// `if (cond)`: every `if` the backend writes is made here, so its condition
/// goes through [`condition`] (R-142).
pub(super) fn if_(cond: &str) -> String {
    format!("if ({})", condition(cond))
}

/// `while (cond)`, as [`if_`].
pub(super) fn while_(cond: &str) -> String {
    format!("while ({})", condition(cond))
}

/// Whether the C `body` names the result `(*out)` outside its string literals
/// (a message may read so, [`c_string`](super::c_string)).
pub(super) fn names_result(body: &str) -> bool {
    let unquoted = body.replace("\\\\", "").replace("\\\"", "");
    unquoted.split('"').step_by(2).any(|code| code.contains("(*out)"))
}

/// A C expression as the condition of `if (…)` / `while (…)`: without the
/// parentheses that wrap the whole of it (a comparison is emitted as
/// `(a == b)`, and `if ((a == b))` is clang's `-Wparentheses-equality`, R-142).
fn condition(s: &str) -> &str {
    let b = s.as_bytes();
    if b.first() != Some(&b'(') || b.last() != Some(&b')') {
        return s;
    }
    let mut depth = 0usize;
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return if i == b.len() - 1 { &s[1..s.len() - 1] } else { s };
                }
            }
            _ => {}
        }
    }
    s
}

/// The name of a C parameter declaration (`const T* x` → `x`).
pub(super) fn c_param_name(decl: &str) -> &str {
    let start = decl.rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).map_or(0, |i| i + 1);
    &decl[start..]
}

/// `base.` — or `p->` when `base` is a dereferenced pointer parameter `(*p)`.
pub(super) fn dot(base: &str) -> String {
    if let Some(inner) = base.strip_prefix("(*").and_then(|r| r.strip_suffix(')'))
        && inner.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return format!("{inner}->");
    }
    format!("{base}.")
}

/// The head of the name of a temporary ([`FnEmitter::temp`]), before its number.
pub(super) const TEMP: &str = "onsa_t";

/// Whether `s` is a temporary: [`TEMP`] and digits only, not a call of
/// `onsa_trunc_*` nor a local `onsa_t` (`onsa_t_`, R-438).
fn is_temp(s: &str) -> bool {
    s.strip_prefix(TEMP).is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

fn is_c_ident(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}
