//! The functions of the unit: the body of each, one [`FnEmitter`] for each,
//! and the helpers of the C text they write.

mod dest;
mod expr;
mod place;
mod prim;
mod signature;
mod stmt;
mod text;

use super::*;
use text::TEMP;

// ------------------------------------------------------------ functions

/// How a local is reached from C.
#[derive(Debug, Clone)]
struct LocalC {
    /// A complete C lvalue (`x`, `(*s)`, `(*out)`).
    lvalue: String,
}

pub(crate) struct FnEmitter<'a, 'm> {
    cx: &'a mut Cx<'m>,
    f: FnId,
    def: &'m FnDef,
    out: String,
    indent: usize,
    locals: HashMap<LocalId, LocalC>,
    used_names: HashSet<String>,
    temps: u32,
    /// The local returned through `out` without a copy (§12.7 NRVO).
    nrvo: Option<LocalId>,
    /// The definition of the guarded twin, once the signature is known.
    guarded: Option<String>,
    /// The locals the body reads ([`Self::unread_use`]).
    read: HashSet<LocalId>,
    /// The loops around the statement being emitted, the innermost last.
    loops: Vec<LoopC>,
    /// How many loops the body has opened: the number of the next one.
    loops_opened: u32,
}

/// A loop while its C is written. The C of the condition of a `while` can stand in a C loop of that
/// `while`, and a `break` or a `continue` written there is of the loop around it (§7), which a plain
/// `break;` would not reach: it jumps to a label of that loop, written only if something jumps to it.
struct LoopC {
    number: u32,
    /// The statement being emitted is in the condition of this loop.
    in_condition: bool,
    breaks_to_label: bool,
    continues_to_label: bool,
}

impl<'a, 'm> FnEmitter<'a, 'm> {
    pub fn new(cx: &'a mut Cx<'m>, f: FnId) -> Self {
        let def = cx.m.fn_(f);
        FnEmitter {
            cx,
            f,
            def,
            out: String::new(),
            indent: 1,
            locals: HashMap::new(),
            used_names: HashSet::new(),
            temps: 0,
            nrvo: None,
            guarded: None,
            read: HashSet::new(),
            loops: Vec::new(),
            loops_opened: 0,
        }
    }

    // -------------------------------------------------------- helpers

    fn line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn open(&mut self, s: &str) {
        self.line(s);
        self.indent += 1;
    }

    fn close(&mut self, s: &str) {
        self.indent -= 1;
        self.line(s);
    }

    /// `(void)x;` for a parameter or a binding the body never reads (S-288:
    /// an unused `let`, a pattern's binding, a `var` only assigned, a local
    /// whose comparisons Core folded), so the C has no `-Wunused-*`. The one
    /// place of that decision.
    fn unread_use(&self, l: LocalId, cname: &str) -> Option<String> {
        (!self.read.contains(&l)).then(|| format!("(void){cname};"))
    }

    fn enter_loop(&mut self, in_condition: bool) {
        self.loops_opened += 1;
        let number = self.loops_opened;
        self.loops.push(LoopC { number, in_condition, breaks_to_label: false, continues_to_label: false });
    }

    /// The body of the innermost loop, whose opening brace is written, its closing brace and its labels.
    fn loop_body(&mut self, body: &Block) -> R<()> {
        if let Some(l) = self.loops.last_mut() {
            l.in_condition = false;
        }
        self.block_into(body, None)?;
        let this = self.loops.pop().expect("the loop `enter_loop` opened");
        if this.continues_to_label {
            self.line(&format!("onsa_continue_{}:;", this.number));
        }
        self.close("}");
        if this.breaks_to_label {
            self.line(&format!("onsa_break_{}:;", this.number));
        }
        Ok(())
    }

    /// A `break`, or a `continue`: of the innermost loop whose condition this is not in (§7).
    fn leave_loop(&mut self, is_break: bool) {
        let word = if is_break { "break" } else { "continue" };
        let own = self.loops.iter().rposition(|l| !l.in_condition);
        match own.filter(|&i| i + 1 < self.loops.len()) {
            None => self.line(&format!("{word};")),
            Some(i) => {
                let l = &mut self.loops[i];
                *(if is_break { &mut l.breaks_to_label } else { &mut l.continues_to_label }) = true;
                let number = l.number;
                self.line(&format!("goto onsa_{word}_{number};"));
            }
        }
    }

    fn fresh_local(&mut self, l: LocalId) -> String {
        let base = ident(&self.def.locals[l.0 as usize].name);
        // A name already used, a parameter `t_5` too, is not taken again.
        let (mut name, mut n) = (base.clone(), 0);
        while self.used_names.contains(&name) {
            name = if n == 0 { format!("{base}_{}", l.0) } else { format!("{base}_{}_{n}", l.0) };
            n += 1;
        }
        self.used_names.insert(name.clone());
        name
    }

    fn temp(&mut self, ty: CTy) -> (String, String) {
        self.temps += 1;
        let name = format!("{TEMP}{}", self.temps);
        let tn = self.cx.names.name(ty);
        (name, tn)
    }

    fn loc(&self, span: Span) -> String {
        self.cx.loc(span)
    }

    /// What `t` is, one level deep.
    fn kind(&self, t: CTy) -> &'m TyKind {
        self.cx.m.tys.kind(t)
    }

    fn local_ty(&self, l: LocalId) -> CTy {
        self.def.locals[l.0 as usize].ty
    }
}

/// The suffix of the guarded twin of a function: what a `panic = "poison"`
/// wrapper calls after its `setjmp` (R-167). The twin is never inlined, so the
/// body's variables live in the twin's frame and not in the frame that
/// `longjmp` returns to (no gcc `-Wclobbered`, and nothing that the wrapper
/// changes after the `setjmp` is read after the `longjmp`, C11 §7.13.2.1).
pub(crate) const GUARDED_SUFFIX: &str = "__guarded";

/// A state the C backend cannot be in: an internal error (S-67), not E0200.
/// The driver's guard reports it with the function being emitted.
pub(crate) fn internal(msg: &str) -> Diagnostic {
    onsa_diag::internal::bug(None, format!("internal C backend error: {msg}"))
}
