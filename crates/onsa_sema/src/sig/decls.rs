//! The order of the declarations of types and their cycles (§4.4, §18.1;
//! S-730, S-734, S-744; R-02, R-182, R-298, R-303), at the head of the stage
//! of the signatures, from the AST and the names alone: no type is lowered
//! to make it.
//!
//! A struct, an enum and a struct a flow generates of its inputs (`Config`,
//! `Params`, §11.6) is a point "as a value"; an alias is two, "as a value"
//! and "anywhere"; a constant one, "anywhere". A point as a value has an
//! edge to what its declaration holds as a value (a field, the contents of a
//! variant, a tuple, a fixed array, an argument of a generic type where that
//! type holds its parameter as a value, of `Option` and `Result`) and to the
//! constants a length or a const argument there reads (§4.4). A point
//! anywhere has an edge to every alias and constant its type names: what is
//! lowered before it; a constant has the edges of both from its type
//! (S-744). Whether a generic type holds a parameter as a value
//! depends on the others: each place is gathered with the arguments it is
//! under, and the least solution of those Horn clauses is found by counting.
//!
//! A strongly connected component with an edge in it is a cycle, and the
//! cycles that share a declaration are one: an E0311 each. The aliases and
//! the constants of the modules are lowered in the order of the components,
//! sinks first, so that none reads another not lowered and none recurses
//! (a chain of 20 000 aliases, R-298), each once (R-303). The graph is O(D +
//! T) (D declarations, T nodes of the types written in them), and every walk
//! is as deep as a type written (§2.5).

use onsa_syntax::ast::ExprId;

use super::*;
use crate::names::builtin_ty;

/// What the order of the declarations leaves to the later stages.
#[derive(Debug, Default)]
pub struct Decls {
    /// The declarations of a cycle: a name of one is the error type, and a
    /// constant of one has no value, with no diagnostic (§18.1).
    pub(crate) cyclic: HashSet<DefId>,
    /// The aliases lowered (`true`) or being lowered (`false`).
    pub(crate) lowered: HashMap<DefId, bool>,
    /// What the head of the right side of each alias names, through the
    /// aliases there ([`Sema::alias_heads`]).
    pub(crate) heads: HashMap<DefId, Option<Entity>>,
}

/// The generic arguments `(e, k)` a place is under, a chain of
/// [`Graph::chains`] shared by the places under it (0: none): it is held as
/// a value when each of them is.
type Under = usize;

/// A point: a declaration, anywhere or as a value.
type Point = (DefId, bool);

struct Graph<'a> {
    a: &'a Analysis,
    points: HashMap<Point, usize>,
    of: Vec<Point>,
    edges: Vec<(usize, usize, Under)>,
    /// `(d, i)`: `d` holds its parameter `i` as a value if all of these do.
    clauses: Vec<((DefId, u32), Under)>,
    /// The last argument of a chain and the chain it is under.
    chains: Vec<((DefId, u32), Under)>,
}

/// One walk, from the point `from`, in the module `m` of `ast`: the names of
/// the parameters in scope and what `Self` names.
struct From<'w> {
    m: ModId,
    ast: &'w Ast,
    from: usize,
    anywhere: bool,
    generics: Vec<&'w str>,
    this: Option<Entity>,
}

impl Graph<'_> {
    fn point(&mut self, p: Point) -> usize {
        let n = self.of.len();
        let of = &mut self.of;
        *self.points.entry(p).or_insert_with(|| {
            of.push(p);
            n
        })
    }

    fn edge(&mut self, w: &From, to: Point, under: Under) {
        let to = self.point(to);
        self.edges.push((w.from, to, if w.anywhere { 0 } else { under }));
    }

    fn ty(&mut self, w: &From, t: TypeId, value: bool, under: Under) {
        if !value && !w.anywhere {
            return;
        }
        match &w.ast.ty(t).kind {
            TypeKind::Tuple(ts) => ts.iter().for_each(|&x| self.ty(w, x, value, under)),
            TypeKind::Array { elem, len } => {
                self.ty(w, *elem, value, under);
                self.expr(w, *len, value, under);
            }
            TypeKind::Fn { params, ret, .. } => {
                params.iter().map(|p| p.1).chain(*ret).for_each(|x| self.ty(w, x, false, under));
            }
            TypeKind::ConstArg(e) => self.expr(w, *e, value, under),
            TypeKind::Path { path, args } => self.named(w, path, args, value, under),
            TypeKind::Unit | TypeKind::Error => {}
        }
    }

    fn named(&mut self, w: &From, path: &Path, args: &[TypeId], value: bool, under: Under) {
        if let [seg] = &path.segments[..]
            && let Some(i) = w.generics.iter().position(|g| *g == seg.name)
        {
            if value && !w.anywhere {
                self.clauses.push(((self.of[w.from].0, i as u32), under));
            }
            return;
        }
        let a = self.a;
        let mut held: Option<(DefId, &[GenericDef])> = None;
        match self.resolve(w, path) {
            Some(Entity::Def(d) | Entity::Member(d)) => match &a.def(d).kind {
                DefKind::Struct(_) | DefKind::Enum(_) => {
                    if !w.anywhere {
                        self.edge(w, (d, false), under);
                    }
                    held = Some((d, a.def(d).generics()));
                }
                DefKind::Alias(_) => self.edge(w, (d, w.anywhere), under),
                // A constant here is no type (§18.1); in a const argument, `read`.
                _ => {}
            },
            Some(Entity::Builtin(Builtin::Generic(b))) => {
                return args.iter().for_each(|&x| self.ty(w, x, value && b.holds_values(), under));
            }
            _ => {}
        }
        for (k, &x) in args.iter().enumerate() {
            match (held.and_then(|(d, gs)| Some((d, &gs.get(k)?.kind))), &w.ast.ty(x).kind) {
                (Some((d, GenericKind::Type { .. })), _) => {
                    self.chains.push(((d, k as u32), under));
                    self.ty(w, x, value, self.chains.len() - 1);
                }
                (Some((_, GenericKind::Const(_))), TypeKind::Path { path, args }) if args.is_empty() => {
                    if value || w.anywhere {
                        self.read(w, path, under);
                    }
                }
                (Some((_, GenericKind::Const(_))), _) => self.ty(w, x, value, under),
                _ => self.ty(w, x, false, under),
            }
        }
    }

    /// The constants the constant expression `e` reads, and anywhere the
    /// aliases its paths pass (`Al.N`).
    fn expr(&mut self, w: &From, e: ExprId, value: bool, under: Under) {
        if !value && !w.anywhere {
            return;
        }
        let mut leaves = Vec::new();
        crate::constarg::operands(w.ast, e, &mut leaves);
        for p in leaves.into_iter().filter_map(|l| crate::constarg::path_of(w.ast, l)) {
            self.read(w, &p, under);
        }
    }

    /// The constant the path `p` of a constant expression reads (a const
    /// argument `B[K]` too), and anywhere the alias it passes.
    fn read(&mut self, w: &From, p: &Path, under: Under) {
        if let [seg] = &p.segments[..]
            && w.generics.contains(&seg.name.as_str())
        {
            return;
        }
        let before = Path { segments: p.segments[..p.segments.len() - 1].to_vec(), span: p.span };
        let mut read = self.resolve(w, p);
        if !before.segments.is_empty()
            && let Some(Entity::Def(al)) = self.resolve(w, &before)
            && matches!(self.a.def(al).kind, DefKind::Alias(_))
        {
            if w.anywhere {
                self.edge(w, (al, true), under);
            }
            // `Al.N`: of the type the alias stands for (R-299).
            let names = (&self.a.prelude, &self.a.defs[..], &self.a.builtin_key);
            let ty = self.a.decls.heads.get(&al).copied().flatten();
            read = ty.and_then(|t| self.a.modules.member(t, p.segments.last()?, w.m, names).ok());
        }
        if let Some(Entity::Def(c) | Entity::Member(c)) = read
            && matches!(self.a.def(c).kind, DefKind::Const(_))
        {
            self.edge(w, (c, true), under);
        }
    }

    /// What `p` names; `Self` and `Self.N` through the type of the `impl`
    /// (§2.2), whose members are named before ([`Sema::name_members`]).
    fn resolve(&self, w: &From, p: &Path) -> Option<Entity> {
        let a = self.a;
        let ([head, rest @ ..], Some(this)) = (&p.segments[..], w.this) else { return a.resolve_path(w.m, p).ok() };
        if head.name != "Self" {
            return a.resolve_path(w.m, p).ok();
        }
        let table = match this {
            Entity::Def(d) => a.modules.assoc.get(&d),
            e => builtin_ty(a, e).and_then(|t| a.modules.assoc_builtin.get(&t)),
        };
        match rest {
            [] => Some(this),
            [n] => table.and_then(|t| t.get(&n.name)).map(|&d| Entity::Member(d)),
            _ => None,
        }
    }
}

/// The least solution of the clauses, by counting: whether each chain holds
/// (its argument and the chain it is under do; chain 0 does).
fn solve(g: &Graph) -> Vec<bool> {
    let n = g.chains.len();
    let (mut left, mut holds) = (vec![2u8; n], vec![false; n]);
    let (mut below, mut gives) = (vec![Vec::new(); n], vec![Vec::new(); n]);
    let mut watch: HashMap<(DefId, u32), Vec<usize>> = HashMap::new();
    for (c, &(arg, up)) in g.chains.iter().enumerate().skip(1) {
        below[up].push(c);
        watch.entry(arg).or_default().push(c);
    }
    g.clauses.iter().for_each(|&(param, under)| gives[under].push(param));
    let (mut queue, mut params) = (vec![0], HashSet::new());
    while let Some(c) = queue.pop() {
        holds[c] = true;
        let freed = gives[c].iter().filter(|&&p| params.insert(p)).flat_map(|p| watch.get(p).into_iter().flatten());
        for &j in freed.chain(&below[c]) {
            left[j] -= 1;
            if left[j] == 0 {
                queue.push(j);
            }
        }
    }
    holds
}

impl<'p> Sema<'p> {
    /// The graph of the declarations (the module's doc): its cycles reported,
    /// and the aliases and the constants of the modules lowered in its order.
    pub(super) fn order_declarations(&mut self) {
        self.alias_heads();
        self.name_members();
        let mut g = Graph {
            a: &*self.a,
            points: HashMap::new(),
            of: Vec::new(),
            edges: Vec::new(),
            clauses: Vec::new(),
            chains: vec![((DefId(0), 0), 0)],
        };
        for i in 0..self.a.defs.len() {
            self.walk_def(&mut g, DefId(i as u32));
        }
        let holds = solve(&g);
        let mut adj = vec![Vec::new(); g.of.len()];
        for (u, v, _) in g.edges.iter().filter(|e| holds[e.2]) {
            adj[*u].push(*v);
        }
        let (comp, cycled) = crate::names::cyclic(&adj);
        let of = g.of;
        let cyclic: Vec<usize> = (0..of.len()).filter(|&p| cycled[p]).collect();
        let mut mods: HashMap<usize, Vec<ModId>> = HashMap::new();
        cyclic.iter().for_each(|&p| mods.entry(comp[p]).or_default().push(self.a.def(of[p].0).module));
        // A cycle in modules that are one cycle of the imports: its E0310 is
        // the one (§18.1, S-734).
        let silent: HashSet<usize> =
            mods.iter().filter(|(_, ms)| self.a.modules.across_one_cycle(ms)).map(|e| *e.0).collect();
        // The other cycles that share a declaration are one (a union of components).
        let mut root: Vec<usize> = (0..of.len()).collect();
        let find = |root: &mut Vec<usize>, mut c: usize| {
            while root[c] != c {
                (root[c], c) = (root[root[c]], root[c]);
            }
            c
        };
        let mut first: HashMap<DefId, usize> = HashMap::new();
        for &p in &cyclic {
            let d = of[p].0;
            self.a.decls.cyclic.insert(d);
            if matches!(self.a.def(d).kind, DefKind::Alias(_)) {
                self.a.decls.lowered.insert(d, true);
            }
            if silent.contains(&comp[p]) {
                continue;
            }
            let c = find(&mut root, comp[p]);
            let other = *first.entry(d).or_insert(c);
            let other = find(&mut root, other);
            root[c] = other;
        }
        let mut groups: Vec<Vec<DefId>> = vec![Vec::new(); of.len()];
        for (&d, &c) in &first {
            groups[find(&mut root, c)].push(d);
        }
        let mut order: Vec<usize> = (0..of.len()).filter(|&p| of[p].1).collect();
        order.sort_by_key(|&p| comp[p]);
        let order: Vec<DefId> = order.into_iter().map(|p| of[p].0).collect();
        for decls in groups.into_iter().filter(|ds| !ds.is_empty()) {
            let what = (Code::E0311, "cyclic type, §4.4");
            let (first, d) = crate::names::cycle_diagnostic((self.a, &self.flat), what, decls, None);
            self.report(first, d);
        }
        for d in order {
            if self.a.decls.cyclic.contains(&d) {
                continue;
            }
            let _scope = onsa_diag::internal::item_scope(self.a.def(d).span);
            match self.a.def(d).kind {
                DefKind::Alias(_) => _ = self.alias_ty(d),
                DefKind::Const(_) => self.const_ty(d),
                _ => {}
            }
        }
    }

    /// The edges from the declaration `d`.
    fn walk_def(&self, g: &mut Graph<'_>, d: DefId) {
        let def = self.a.def(d);
        let Some(module) = self.module(def.module) else { return };
        let ast = &module.parsed.ast;
        let kind = def.item.map(|i| item_kind(&ast.item(i).kind));
        let walk = |g: &mut Graph<'_>,
                    at: (bool, &'p [GenericParam], Option<Entity>),
                    ts: &mut dyn Iterator<Item = TypeId>| {
            let (anywhere, gs, this) = at;
            let generics = gs.iter().map(|g| crate::names::param_name(g).name.as_str()).collect();
            let at = (d, anywhere || matches!(def.kind, DefKind::Const(_)));
            let (w, held) = (From { m: def.module, ast, from: g.point(at), anywhere, generics, this }, g.clauses.len());
            ts.for_each(|t| g.ty(&w, t, true, 0));
            // What a heading whose parameters are an E0304 holds of its
            // arguments is not known (§18.1): none.
            if !crate::names::param_clashes(self.a, def.module, gs, &[]).is_empty() {
                g.clauses.truncate(held);
            }
        };
        match (&def.kind, kind) {
            (DefKind::Alias(_) | DefKind::Const(_), _) if self.a.heading_failed(d) => _ = g.point((d, true)),
            _ if self.a.heading_failed(d) => {}
            (DefKind::Struct(_), Some(ItemKind::Struct(s))) => {
                walk(g, (false, &s.generics, None), &mut s.fields.iter().map(|f| f.ty));
            }
            (DefKind::Enum(_), Some(ItemKind::Enum(e))) => {
                walk(g, (false, &e.generics, None), &mut e.variants.iter().flat_map(|v| v.fields.iter().copied()));
            }
            (DefKind::Alias(_), Some(ItemKind::TypeAlias { ty, .. })) => {
                walk(g, (false, &[], None), &mut std::iter::once(*ty));
                walk(g, (true, &[], None), &mut std::iter::once(*ty));
            }
            (DefKind::Const(_), Some(ItemKind::Const(c))) => {
                let owner = def.owner.map(|o| (o, self.a.def(o).item.map(|i| item_kind(&ast.item(i).kind))));
                let (gs, this, heading) = match owner {
                    Some((o, Some(ItemKind::Impl(i)))) => (&i.generics[..], self.impl_type(o), Some(i)),
                    _ => (&[][..], None, None),
                };
                walk(g, (true, gs, this), &mut std::iter::once(c.ty));
                // And what that type holds as a value (§4.4, S-744): `const K: S`.
                walk(g, (false, gs, this), &mut std::iter::once(c.ty));
                // The heading of its `impl`, lowered with it (`member_cx`).
                let consts = heading.into_iter().flat_map(|i| &i.generics).filter_map(|p| match p {
                    GenericParam::Const { ty, .. } => Some(*ty),
                    _ => None,
                });
                walk(g, (true, gs, this), &mut heading.map(|i| i.self_ty).into_iter().chain(consts));
            }
            (DefKind::Struct(sd), None) => {
                let (Some(rate), Some(flow)) = (sd.flow_ty.and_then(FlowTy::input_rate), def.owner) else { return };
                let Some(ItemKind::Flow(f)) = self.a.def(flow).item.map(|i| item_kind(&ast.item(i).kind)) else {
                    return;
                };
                let rated =
                    |p: &&Param| p.clock.as_ref().and_then(|c| crate::flow_names::clock_rate(c).ok()) == Some(rate);
                walk(g, (false, &[], None), &mut f.params.iter().filter(rated).filter_map(|p| p.ty));
            }
            (DefKind::Alias(_) | DefKind::Const(_), _) => _ = g.point((d, true)),
            _ => {}
        }
    }

    /// The type of the `impl` `id` names by its declaration, as written.
    fn impl_target(&self, id: DefId) -> Option<Entity> {
        let def = self.a.def(id);
        let ast = &self.module(def.module)?.parsed.ast;
        let Some(ItemKind::Impl(i)) = def.item.map(|it| item_kind(&ast.item(it).kind)) else { return None };
        let TypeKind::Path { path, .. } = &ast.ty(i.self_ty).kind else { return None };
        i.trait_.is_none().then(|| self.a.resolve_path(def.module, path).ok()).flatten()
    }

    /// What the head of the right side of each alias names ([`Decls::heads`]),
    /// from the AST and the names alone (S-748): through an alias there, to
    /// what is no alias, also when the alias is the error type (`type A =
    /// S[I32]`, S-752); none for a type with no name (a tuple, an array), a
    /// cycle of aliases and a heading that failed. Each alias once, with no
    /// recursion (a chain of 20 000, R-298).
    fn alias_heads(&mut self) {
        for i in 0..self.a.defs.len() {
            let (mut cur, mut chain) = (DefId(i as u32), Vec::new());
            let head = loop {
                if let Some(&h) = self.a.decls.heads.get(&cur) {
                    break h;
                }
                if !matches!(self.a.def(cur).kind, DefKind::Alias(_)) {
                    break Some(Entity::Def(cur));
                }
                self.a.decls.heads.insert(cur, None);
                chain.push(cur);
                match self.alias_rhs(cur) {
                    Some(Entity::Def(d)) => cur = d,
                    e => break e,
                }
            };
            chain.into_iter().for_each(|d| _ = self.a.decls.heads.insert(d, head));
        }
    }

    /// What the head of the right side of the alias `d` names: none for a
    /// type with no name, and when its heading failed.
    fn alias_rhs(&self, d: DefId) -> Option<Entity> {
        let def = self.a.def(d);
        let ast = &self.module(def.module)?.parsed.ast;
        let Some(ItemKind::TypeAlias { ty, .. }) = def.item.map(|i| item_kind(&ast.item(i).kind)) else { return None };
        let TypeKind::Path { path, .. } = &ast.ty(*ty).kind else { return None };
        (!self.a.heading_failed(d)).then(|| self.a.resolve_path(def.module, path).ok()).flatten()
    }

    /// The names of the members of every inherent `impl` (the one place,
    /// D-15), each in the table of its type ([`Sema::member_key`]), before
    /// any signature is lowered: a type and a constant read them in the
    /// order of the declarations (`Self.N`, `S.N`; §4.4). Those of an `impl`
    /// whose heading is an E0307 too (§18.1, S-748). In the order of the
    /// source (§6.2, R-307): a member of the name of one before, or of a
    /// variant of its enum, is an E0304 (S-134, S-737), and the first of the
    /// name is no name where it is used (§18.1).
    fn name_members(&mut self) {
        let mut subs = Vec::new();
        for i in 0..self.a.defs.len() {
            let DefKind::Impl(imp) = &self.a.defs[i].kind else { continue };
            let Some(key) = self.member_key(DefId(i as u32)) else { continue };
            subs.extend(imp.fns.iter().chain(&imp.consts).map(|&sub| (key, sub)));
        }
        subs.sort_by_cached_key(|&(_, d)| (self.file_key(self.a.def(d).module), self.a.def(d).name_span.start));
        let mut variants: HashMap<DefId, HashMap<String, Span>> = HashMap::new();
        for ((def, builtin), sub) in subs {
            let (name, at) = (self.a.def(sub).name.clone(), self.a.def(sub).name_span);
            let variant = def.and_then(|d| variants.entry(d).or_insert_with(|| self.variants(d)).get(&name).copied());
            let Some(table) = self.assoc_table(def, builtin) else { continue };
            let first = *table.entry(name.clone()).or_insert(sub);
            let note = match variant {
                Some(v) => (v, format!("the variant `{name}`")),
                None if first != sub => (self.a.def(first).name_span, "first defined here".to_string()),
                None => continue,
            };
            self.a.modules.clashed_assoc.insert(first);
            let msg = format!("`{name}` is defined twice for this type");
            self.report(sub, Diagnostic::new(Stage::Names, Code::E0304, at, msg).with_note(note.0, note.1));
        }
    }

    /// The names of the variants of `d` when it is an enum, as written (the
    /// variants are lowered later).
    fn variants(&self, d: DefId) -> HashMap<String, Span> {
        let def = self.a.def(d);
        let Some(ast) = self.module(def.module).map(|m| &m.parsed.ast) else { return HashMap::new() };
        let Some(ItemKind::Enum(e)) = def.item.map(|i| item_kind(&ast.item(i).kind)) else { return HashMap::new() };
        e.variants.iter().map(|v| (v.name.name.clone(), v.name.span)).collect()
    }

    /// The table of the members of the inherent `impl` `id` (D-15): of the
    /// struct or enum it names, of the builtin type by its key. None for
    /// another type.
    pub(super) fn member_key(&self, id: DefId) -> Option<(Option<DefId>, Option<TyId>)> {
        match self.impl_type(id)? {
            Entity::Def(d) | Entity::Member(d)
                if matches!(self.a.def(d).kind, DefKind::Struct(_) | DefKind::Enum(_)) =>
            {
                Some((Some(d), None))
            }
            e => builtin_ty(self.a, e).map(|t| (None, Some(t))),
        }
    }

    /// The type the inherent `impl` `id` is of: what it names, and of an
    /// alias (E0307), what the alias stands for ([`Decls::heads`]).
    fn impl_type(&self, id: DefId) -> Option<Entity> {
        match self.impl_target(id)? {
            Entity::Def(al) if matches!(self.a.def(al).kind, DefKind::Alias(_)) => {
                self.a.decls.heads.get(&al).copied().flatten()
            }
            e => Some(e),
        }
    }

    /// The visibility of the type of a table of members (`member_key`): a
    /// builtin type's is `pub`.
    pub(super) fn type_vis(&self, (def, builtin): (Option<DefId>, Option<TyId>)) -> Option<Vis> {
        def.map(|d| self.a.def(d).vis).or(builtin.map(|_| Vis::Pub))
    }

    /// The type of the constant `id`, lowered in the order of the
    /// declarations: of a module, or a member of an inherent `impl` in the
    /// context of its members.
    fn const_ty(&mut self, id: DefId) {
        let def = self.a.def(id);
        let cx = match def.owner {
            None => self.cx_for(id, Vec::new(), None),
            Some(o) => self.member_cx(o, id),
        };
        let Some(cx) = cx else { return };
        let Some(ItemKind::Const(c)) = self.a.def(id).item.map(|i| item_kind(&cx.ast.item(i).kind)) else { return };
        let ty = self.lower_type(&cx, c.ty);
        if let DefKind::Const(cd) = &mut self.a.defs[id.0 as usize].kind {
            cd.ty = ty;
        }
    }

    /// The context of the constant `id`, a member of the `impl` `o`: none
    /// of a trait's `impl` (`Sema::lower_def`). How far it reaches is
    /// reported (E0020) with the `impl`.
    fn member_cx(&mut self, o: DefId, id: DefId) -> Option<Cx<'p>> {
        let cx = self.cx_for(o, Vec::new(), None)?;
        let Some(ItemKind::Impl(i)) = self.a.def(o).item.map(|i| item_kind(&cx.ast.item(i).kind)) else { return None };
        if i.trait_.is_some() {
            return None;
        }
        let cx = self.impl_cx(cx, i);
        let key = self.member_key(o).unwrap_or((None, None));
        let reach = self.type_vis(key).map(|t| crate::resolve::narrower(self.a.def(id).vis, t));
        Some(Cx { def: id, reach, ..cx })
    }
}

/// The kind of an item, out of `target` (§14).
pub(super) fn item_kind(kind: &ItemKind) -> &ItemKind {
    match kind {
        ItemKind::Target(inner) => inner,
        k => k,
    }
}
