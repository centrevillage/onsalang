//! The loops of the `let`s of a flow body (§11.3 "読み方", W7-02 U2a): the
//! strongly connected components of the graph of their reads, which the walk
//! of the clocks solves one by one (`flow::clocks`). It knows no clock.

/// A strongly connected component of the `let`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Scc {
    /// The numbers of its `let`s, in their order in the text.
    pub(crate) lets: Vec<usize>,
    /// A loop: two `let`s or more, or one that reads itself.
    pub(crate) looped: bool,
}

/// The components of the graph of the reads (`deps[v]` the `let`s the `let`
/// `v` reads, the `let`s numbered in their order in the text), each after the
/// components it reads. An iterative Tarjan: O(V + E) in time and memory, no
/// recursion. A read of no `let` is an internal error.
pub(crate) fn components(deps: &[Vec<usize>]) -> Vec<Scc> {
    tarjan(deps).0
}

const UNSEEN: usize = usize::MAX;

/// The state of the search: the numbers by `let`, and the stack of Tarjan.
struct Search {
    index: Vec<usize>,
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    comp: Vec<usize>,
    count: usize,
}

impl Search {
    fn discover(&mut self, v: usize, next: &mut usize) {
        self.index[v] = *next;
        self.low[v] = *next;
        *next += 1;
        self.stack.push(v);
        self.on_stack[v] = true;
    }

    /// Pops the component whose root is `v` and numbers it.
    fn close(&mut self, v: usize) {
        loop {
            let Some(w) = self.stack.pop() else {
                onsa_diag::internal::bug(None, format!("the component of the let {v} left the stack"))
            };
            self.on_stack[w] = false;
            self.comp[w] = self.count;
            if w == v {
                break;
            }
        }
        self.count += 1;
    }
}

/// [`components`] and the most frames the search held at once (the depth a
/// recursive search would have reached on the stack of the thread).
fn tarjan(deps: &[Vec<usize>]) -> (Vec<Scc>, usize) {
    let n = deps.len();
    let mut s = Search {
        index: vec![UNSEEN; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        comp: vec![UNSEEN; n],
        count: 0,
    };
    let (mut next, mut deepest) = (0, 0);
    // A frame is a `let` and the number of its reads already followed.
    let mut frames: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if s.index[root] != UNSEEN {
            continue;
        }
        s.discover(root, &mut next);
        frames.push((root, 0));
        while let Some(&(v, e)) = frames.last() {
            deepest = deepest.max(frames.len());
            if let Some(&w) = deps[v].get(e) {
                let top = frames.len() - 1;
                frames[top].1 += 1;
                if w >= n {
                    onsa_diag::internal::bug(None, format!("the let {v} reads {w} of {n} lets"));
                }
                if s.index[w] == UNSEEN {
                    s.discover(w, &mut next);
                    frames.push((w, 0));
                } else if s.on_stack[w] {
                    s.low[v] = s.low[v].min(s.index[w]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(u, _)) = frames.last() {
                s.low[u] = s.low[u].min(s.low[v]);
            }
            if s.low[v] == s.index[v] {
                s.close(v);
            }
        }
    }
    // Tarjan numbers a component after every component it reaches, so the
    // numbers are the order; the `let`s go in by their numbers, in the text.
    let mut out = vec![Scc { lets: Vec::new(), looped: false }; s.count];
    for (v, &c) in s.comp.iter().enumerate() {
        out[c].lets.push(v);
        out[c].looped |= deps[v].contains(&v);
    }
    for scc in &mut out {
        scc.looped |= scc.lets.len() > 1;
    }
    (out, deepest)
}

#[cfg(test)]
mod tests;
