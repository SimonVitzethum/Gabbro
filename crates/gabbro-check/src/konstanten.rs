//! Lane 111 -- compile-time constants, first cut (PLAN-BITS.md section 6).
//!
//! The checker evaluates total, effect-free `const` initializers and const
//! tables element-wise and prints the values as a Lean certificate (encoding
//! N of the certificate measurement). This pass holds the fragment the
//! small interpreter (`Umgebung::konst_wert`) actually computes:
//!
//! | code | what falls |
//! |---|---|
//! | `K190` | a `const` initializer, or a table element, outside the evaluable fragment |
//! | `K191` | a table literal whose length differs from the declared count |
//! | `K192` | a `const` calling, directly or through `const fn`, a function that is not `pure` |
//! | `K193` | unbounded recursion in const evaluation: a reference cycle through a `const` |
//! | `K194` | a table element evaluating outside the declared element range |
//! | `N285` | a nested literal whose nesting does not match the type's: a row where a value stands, or a value where a row stands |
//! | `N286` | a nested row holding anything but the declared inner count |
//!
//! ## What this pass does NOT do (booked, not forgotten)
//!
//! * Scalar `const` ranges stay `M101`'s: `m1` types every scalar initializer,
//!   so a second range check here would refuse one fault twice. Table literals
//!   are `Unbekannt` at `m1` by construction, hence `K194` owns their range.
//! * Function-only recursion stays `K008`/`K009`/`H022`'s: a cycle with no
//!   `const` in it is refused where it stands, and this pass stays silent on
//!   it -- including the `K190` it would otherwise owe for the unfoldable
//!   call. Only a cycle through a `const` is unbounded *as const
//!   evaluation*, because a `const` carries no `decreases` by grammar shape.
//! * Non-recursive callees without `decreases` are accepted: the bound is
//!   owed where unboundedness lives, which is the same line `K008` draws.
//!   A `const fn` that calls itself WITH `decreases` still exceeds the
//!   single-unfolding folder and falls at `K190`, honestly named.
//! * Float `const` stay silent: the fragment is integers (`Gleitkomma` never
//!   folds, and neither does a use of a float `const` -- a bare `Ort` is not
//!   a foreign node, so float chains pass through untouched).
//! * `~` stays the emitter's (`C001`, gift 445): every `~` shape is refused
//!   elsewhere already (`M137` over literals), so a second refusal here
//!   would be the worse-than-one this tree forbids.
//! * Division by zero stays `M102`'s: the denominator range always contains
//!   zero there, so `K190` skips null denominators the same way.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

use crate::umgebung::{Umgebung, qualifiziere};

/// Purity of a declared function: exactly `effects { pure }` — or, since
/// lane 191, an omitted clause over a settled, empty derivation (`rein`).
/// A derived set with any deed in it is not pure, and neither is a lower
/// bound: purity is the strongest promise, and only a settled empty set
/// carries it.
fn is_pure(decl: &FnDecl, key: &str, rein: &HashSet<String>) -> bool {
    match &decl.effects {
        Some(w) => w.liste.len() == 1 && matches!(w.liste[0].art, WirkungArt::Rein),
        None => rein.contains(key),
    }
}

/// **Lane 191: the settled-empty derivations, by qualified key.**
/// See `is_pure`: purity travels as a settled empty set, never as a bound.
fn reine(baum: &Programm) -> HashSet<String> {
    let ab = crate::ableitung::leite_ab(baum, true);
    ab.je
        .iter()
        .filter(|(_, a)| {
            a.unvollstaendig.is_none()
                && a.wirkungen.iter().all(|w| w.as_str() == "pure")
        })
        .map(|(k, _)| k.clone())
        .collect()
}

/// The single return expression of a `const fn`, if it has that shape.
fn const_body(decl: &FnDecl) -> Option<&Expr> {
    if !matches!(decl.klasse, Some(FnKlasse::Konst)) {
        return None;
    }
    match &decl.rumpf {
        FnRumpf::Block(b) => match &b.anweisungen[..] {
            [s] => match &s.art {
                StmtArt::Return(Some(w)) => Some(w),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// The declaration index this pass reads: functions and consts by qualified
/// name. Owned clones: the module walk lends items to the closure body only,
/// so borrowed references cannot outlive it.
struct DeclIndex {
    functions: HashMap<String, (String, FnDecl)>,
    consts: HashMap<String, (String, KonstDecl)>,
}

impl DeclIndex {
    fn collect(tree: &Programm) -> DeclIndex {
        let mut index = DeclIndex {
            functions: HashMap::new(),
            consts: HashMap::new(),
        };
        crate::fuer_jedes_item_im_modul(tree, &mut |item, module| match &item.art {
            ItemArt::Funktion(f) => {
                index.functions.insert(
                    qualifiziere(module, &f.name.text),
                    (module.to_string(), f.clone()),
                );
            }
            ItemArt::Konst(c) => {
                index
                    .consts
                    .insert(qualifiziere(module, &c.name.text), (module.to_string(), c.clone()));
            }
            // **A table's own consts live in the enclosing module's path, not
            // the table's** (`umgebung.rs` files them under `pfad`, and the
            // grammar names no scope for `table`). The walk above never yields
            // them, so they are indexed here -- an unchecked initializer whose
            // value flows into counts and ranges through the folder would
            // otherwise pass this pass in silence.
            ItemArt::Tabelle(t) => {
                for c in &t.konstanten {
                    index.consts.insert(
                        qualifiziere(module, &c.name.text),
                        (module.to_string(), c.clone()),
                    );
                }
            }
            _ => {}
        });
        index
    }

    /// Resolve a call path the way the folder does: module chain, first hit.
    fn function(&self, env: &Umgebung, from: &str, path: &str) -> Option<(&String, &FnDecl)> {
        let hit = env
            .kandidaten_aufloesbar(from, path)
            .into_iter()
            .find(|k| self.functions.contains_key(k))?;
        self.functions.get(&hit).map(|(m, f)| (m, f))
    }

    /// Resolve a bare name to a `const`, if it names one.
    fn constant(&self, env: &Umgebung, from: &str, name: &str) -> Option<&(String, KonstDecl)> {
        let hit = env
            .kandidaten_aufloesbar(from, name)
            .into_iter()
            .find(|k| self.consts.contains_key(k))?;
        self.consts.get(&hit)
    }
}

/// Nodes of the const-evaluation graph: consts and transparent `const fn`s.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Node {
    Const(String),
    Func(String),
}

/// The outcome of the hull walk for one `const`: which refusals it owes.
#[derive(Default)]
struct Hull {
    impure: Vec<Span>,
    cycle_through_const: Vec<Span>,
    cycle_fn_only: bool,
}

/// Walk every `Ruf` and every bare-`const` `Ort` under `e`. `params` holds the
/// bound parameter names of the enclosing `const fn`, which shadow consts.
fn hull_expr(
    env: &Umgebung,
    index: &DeclIndex,
    from: &str,
    e: &Expr,
    params: &HashSet<String>,
    visited: &mut HashSet<Node>,
    stack: &mut Vec<Node>,
    out: &mut Hull,
    rein: &HashSet<String>,
) {
    for x in crate::alle_ausdruecke(e) {
        match &x.art {
            ExprArt::Ruf(r) => {
                let Some(path) = r.path() else { continue };
                let Some((func_module, decl)) = index.function(env, from, &path.text()) else {
                    continue;
                };
                let schluessel = qualifiziere(func_module, &decl.name.text);
                if !is_pure(decl, &schluessel, rein) {
                    out.impure.push(r.span);
                    continue;
                }
                if const_body(decl).is_none() {
                    continue;
                }
                let key = qualifiziere(func_module, &decl.name.text);
                hull_func(env, index, &key, visited, stack, out, rein);
            }
            ExprArt::Ort(o) => {
                if !o.suffixe.is_empty() || params.contains(&o.basis.text) {
                    continue;
                }
                let Some((const_module, _)) = index.constant(env, from, &o.basis.text) else {
                    continue;
                };
                let key = qualifiziere(const_module, &o.basis.text);
                hull_const(env, index, &key, visited, stack, out, rein);
            }
            _ => {}
        }
    }
}

fn hull_const(
    env: &Umgebung,
    index: &DeclIndex,
    name: &str,
    visited: &mut HashSet<Node>,
    stack: &mut Vec<Node>,
    out: &mut Hull,
    rein: &HashSet<String>,
) {
    let node = Node::Const(name.to_string());
    if stack.contains(&node) {
        out.cycle_through_const.push(node_span(index, &node));
        return;
    }
    if !visited.insert(node.clone()) {
        return;
    }
    stack.push(node);
    if let Some((const_module, decl)) = index.consts.get(name) {
        let params = HashSet::new();
        hull_expr(env, index, const_module, &decl.wert, &params, visited, stack, out, rein);
    }
    stack.pop();
}

fn hull_func(
    env: &Umgebung,
    index: &DeclIndex,
    name: &str,
    visited: &mut HashSet<Node>,
    stack: &mut Vec<Node>,
    out: &mut Hull,
    rein: &HashSet<String>,
) {
    let node = Node::Func(name.to_string());
    if stack.contains(&node) {
        if stack.iter().any(|k| matches!(k, Node::Const(_))) {
            out.cycle_through_const.push(node_span(index, &node));
        } else {
            out.cycle_fn_only = true;
        }
        return;
    }
    if !visited.insert(node.clone()) {
        return;
    }
    stack.push(node);
    if let Some((func_module, decl)) = index.functions.get(name) {
        if let Some(body) = const_body(decl) {
            let params: HashSet<String> = decl
                .parameter
                .iter()
                .map(|p| p.name.text.clone())
                .collect();
            hull_expr(env, index, func_module, body, &params, visited, stack, out, rein);
        }
    }
    stack.pop();
}

fn node_span(index: &DeclIndex, node: &Node) -> Span {
    match node {
        Node::Const(n) => index.consts.get(n).map(|(_, c)| c.name.span),
        Node::Func(n) => index.functions.get(n).map(|(_, f)| f.name.span),
    }
    .unwrap_or(Span { von: 0, bis: 0 })
}

/// Nodes the folder never handles: calls, carrier reads, layout queries,
/// quantified counts, entry/return values, reason values, function values,
/// indirect calls. Literals, bare const uses, parentheses, `!`/`-` and the
/// binary operators are native to it.
fn is_foreign(e: &Expr) -> bool {
    crate::alle_ausdruecke(e).iter().any(|x| match &x.art {
        ExprArt::Ruf(_)
        | ExprArt::LibraryCall(_)
        | ExprArt::Zaehle { .. }
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. }
        | ExprArt::FnWert(_) => true,
        ExprArt::Ort(o) => !o.suffixe.is_empty(),
        _ => false,
    })
}

/// A `~` anywhere inside: the emitter's shape (`C001`, `M137` over literals).
fn has_bitneg(e: &Expr) -> bool {
    crate::alle_ausdruecke(e)
        .iter()
        .any(|x| matches!(&x.art, ExprArt::Unaer(UnOp::BitNicht, _)))
}

/// A float literal anywhere inside: the fragment is integers.
fn has_float(e: &Expr) -> bool {
    crate::alle_ausdruecke(e)
        .iter()
        .any(|x| matches!(&x.art, ExprArt::Gleitkomma { .. }))
}

/// Division or remainder with a denominator folding to zero: `M102` owns it.
fn has_zero_divisor(env: &Umgebung, from: &str, e: &Expr) -> bool {
    crate::alle_ausdruecke(e).iter().any(|x| match &x.art {
        ExprArt::Binaer(BinOp::Geteilt, _, denom) | ExprArt::Binaer(BinOp::Rest, _, denom) => {
            env.konst_wert(from, denom) == Some(0)
        }
        _ => false,
    })
}

fn k190(span: Span, name: &str) -> Absage {
    Absage::fehler(
        "K190",
        span,
        format!(
            "`{name}` is not a compile-time constant of the evaluable fragment \
             (integer literals, other consts, arithmetic and bit operators, calls \
             of `pure` single-return `const fn`): table reads, layout queries, \
             indirect calls and block-bodied calls do not fold"
        ),
    )
    .mit_notiz("PLAN-BITS.md section 6: the checker evaluates the total, effect-free fragment")
}

/// Hold one scalar `const` against the fragment. Silent unless the initializer
/// is an integer shape the folder should have folded.
fn check_scalar(
    env: &Umgebung,
    index: &DeclIndex,
    name: &str,
    init_module: &str,
    init: &Expr,
    target_span: Span,
    absagen: &mut Absagen,
    rein: &HashSet<String>,
) {
    if has_float(init) || has_bitneg(init) {
        return;
    }
    let mut visited = HashSet::new();
    let mut stack = Vec::new();
    let mut hull = Hull::default();
    let params = HashSet::new();
    hull_expr(env, index, init_module, init, &params, &mut visited, &mut stack, &mut hull, rein);
    if !hull.cycle_through_const.is_empty() {
        for sp in hull.cycle_through_const {
            absagen.schiebe(
                Absage::fehler(
                    "K193",
                    sp,
                    "unbounded recursion in const evaluation: the reference cycle \
                     passes through a `const`, and a `const` carries no `decreases`",
                )
                .mit_notiz("a cycle of functions alone is K008/K009/H022 where it stands"),
            );
        }
        return;
    }
    if !hull.impure.is_empty() {
        for sp in hull.impure {
            absagen.schiebe(
                Absage::fehler(
                    "K192",
                    sp,
                    "a `const` calls a function that is not `pure` -- `pure` means it \
                     touches nothing, not even by reading",
                )
                .mit_notiz("the evaluable fragment calls only `effects { pure }` functions"),
            );
        }
        return;
    }
    if hull.cycle_fn_only {
        return;
    }
    if env.konst_wert(init_module, init).is_some() {
        return;
    }
    if !is_foreign(init) || has_zero_divisor(env, init_module, init) {
        return;
    }
    absagen.schiebe(k190(target_span, name));
}

/// Hold one const-table initializer against its declared array type.
fn check_table(
    env: &Umgebung,
    index: &DeclIndex,
    rein: &HashSet<String>,
    name: &str,
    init_module: &str,
    elements: &[Expr],
    element_type: &crate::typen::Typ,
    length: Option<u128>,
    target_span: Span,
    absagen: &mut Absagen,
) {
    let mut visited = HashSet::new();
    let mut stack = Vec::new();
    let mut hull = Hull::default();
    let params = HashSet::new();
    for e in elements {
        if has_float(e) || has_bitneg(e) {
            continue;
        }
        hull_expr(env, index, init_module, e, &params, &mut visited, &mut stack, &mut hull, rein);
    }
    if !hull.cycle_through_const.is_empty() {
        for sp in hull.cycle_through_const {
            absagen.schiebe(
                Absage::fehler(
                    "K193",
                    sp,
                    "unbounded recursion in const evaluation: the reference cycle \
                     passes through a `const`, and a `const` carries no `decreases`",
                )
                .mit_notiz("a cycle of functions alone is K008/K009/H022 where it stands"),
            );
        }
        return;
    }
    if !hull.impure.is_empty() {
        for sp in hull.impure {
            absagen.schiebe(
                Absage::fehler(
                    "K192",
                    sp,
                    "a const-table element calls a function that is not `pure` -- \
                     `pure` means it touches nothing, not even by reading",
                )
                .mit_notiz("the evaluable fragment calls only `effects { pure }` functions"),
            );
        }
        return;
    }
    if hull.cycle_fn_only {
        return;
    }
    if let Some(n) = length {
        if elements.len() as u128 != n {
            absagen.schiebe(
                Absage::fehler(
                    "K191",
                    target_span,
                    format!(
                        "const-table `{name}` declares [{n}] but the literal holds {} \
                         entries -- the literal is element-wise, nothing is filled in",
                        elements.len()
                    ),
                )
                .mit_notiz("the length is the declared count, not a separate annotation"),
            );
            return;
        }
    }
    let range = element_type.bereich();
    for e in elements {
        check_eintrag(env, name, init_module, e, element_type, &range, absagen);
    }
}

/// The array dimension a type declares, through named types and no further:
/// `[[u32; 2]; 2]` declares rows of two `u32`. A pointer TO an array is no
/// dimension -- stripping it would read the pointee's shape as the row's.
fn arraydimension(t: &crate::typen::Typ) -> Option<(&crate::typen::Typ, Option<u128>)> {
    match t {
        crate::typen::Typ::Feld { element, laenge } => Some((element, *laenge)),
        crate::typen::Typ::Benannt { unter, .. } => arraydimension(unter),
        _ => None,
    }
}

/// Lane 170 -- hold one ENTRY of a (possibly nested) const-table literal
/// against the element type one dimension declares.
///
/// A dimension whose element type is itself an array takes ROWS: the entry
/// must be an array literal (`N285` where a value stands, and where a row
/// stands at a scalar dimension), holding exactly the declared inner count
/// (`N286` -- ragged, short or long), each entry held recursively at
/// whatever depth the type ends. A scalar dimension takes VALUES, held
/// exactly the way the flat literal always was: outside the fragment
/// (`K190`), outside the range (`K194`). One fault keeps one refusal --
/// the shape rules own the nesting, the value rules own the leaves.
fn check_eintrag(
    env: &Umgebung,
    name: &str,
    init_module: &str,
    e: &Expr,
    element_type: &crate::typen::Typ,
    range: &Option<crate::typen::IntBereich>,
    absagen: &mut Absagen,
) {
    if let Some((inner, laenge)) = arraydimension(element_type) {
        let ExprArt::ArrayLit(zeile) = &e.art else {
            absagen.schiebe(
                Absage::fehler(
                    "N285",
                    e.span,
                    format!(
                        "const-table `{name}` declares an array at this dimension, but this \
                         entry is no row -- a nested literal holds one row per entry, \
                         nothing is filled in"
                    ),
                )
                .mit_notiz("the literal nests the way the type nests, row for row"),
            );
            return;
        };
        if let Some(n) = laenge {
            if zeile.len() as u128 != n {
                absagen.schiebe(
                    Absage::fehler(
                        "N286",
                        e.span,
                        format!(
                            "const-table `{name}` declares [{n}] at this dimension but this \
                             row holds {} entries -- every row holds the declared count, \
                             nothing is filled in",
                            zeile.len()
                        ),
                    )
                    .mit_notiz(
                        "a ragged row has no C shape: `uint32_t t[2][2]` is rectangular",
                    ),
                );
                return;
            }
        }
        let innen = inner.bereich();
        for z in zeile {
            check_eintrag(env, name, init_module, z, inner, &innen, absagen);
        }
        return;
    }
    if matches!(&e.art, ExprArt::ArrayLit(_)) {
        absagen.schiebe(
            Absage::fehler(
                "N285",
                e.span,
                format!(
                    "const-table `{name}` declares a single value at this dimension, but \
                     this entry is a row -- the literal nests deeper than the type"
                ),
            )
            .mit_notiz("the literal nests the way the type nests, row for row"),
        );
        return;
    }
    if has_float(e) || has_bitneg(e) {
        return;
    }
    let Some(value) = env.konst_wert(init_module, e) else {
        if is_foreign(e) && !has_zero_divisor(env, init_module, e) {
            absagen.schiebe(k190(e.span, name));
        }
        return;
    };
    if let Some(b) = &range {
        if value < b.min || value > b.max {
            absagen.schiebe(
                Absage::fehler(
                    "K194",
                    e.span,
                    format!(
                        "const-table element {value} lies outside the declared element \
                         range `{} .. {}`",
                        b.min, b.max
                    ),
                )
                .mit_notiz("each element is held against the element type, not the table"),
            );
        }
    }
}

/// The pass: every `const` in every module, scalars and tables -- including
/// the consts a `table` body carries, which the item walk never yields.
pub fn pass(tree: &Programm, absagen: &mut Absagen) {
    let env = Umgebung::sammle(tree);
    let index = DeclIndex::collect(tree);
    // **Lane 191:** the settled-empty derivations — `is_pure` counts them
    // like a written `effects { pure }` (see there).
    let rein = reine(tree);
    crate::fuer_jedes_item_im_modul(tree, &mut |item, module| {
        if let ItemArt::Konst(k) = &item.art {
            check_const(&env, &index, &rein, module, k, absagen);
        }
        if let ItemArt::Tabelle(t) = &item.art {
            for k in &t.konstanten {
                check_const(&env, &index, &rein, module, k, absagen);
            }
        }
    });
}

/// Hold one `const` declaration: tables element-wise, scalars whole.
fn check_const(
    env: &Umgebung,
    index: &DeclIndex,
    rein: &HashSet<String>,
    module: &str,
    k: &KonstDecl,
    absagen: &mut Absagen,
) {
    if let ExprArt::ArrayLit(elements) = &k.wert.art {
        let t = env.typ_von_ausdruck_decl(module, &k.typ);
        let (element, length) = match t.durchgreifen() {
            crate::typen::Typ::Feld { element, laenge } => ((**element).clone(), *laenge),
            _ => {
                absagen.schiebe(k190(k.name.span, &k.name.text));
                return;
            }
        };
        check_table(
            env,
            index,
            rein,
            &k.name.text,
            module,
            elements,
            &element,
            length,
            k.name.span,
            absagen,
        );
        return;
    }
    check_scalar(
        env,
        index,
        &k.name.text,
        module,
        &k.wert,
        k.name.span,
        absagen,
        rein,
    );
}

/// Print the evaluated values of a const table as a Lean certificate file:
/// the TRANSLATED const fn definition (lane 121: `konst_lean` renders the
/// body, so Lean checks the values against the SOURCE -- never a hand
/// equation), a `List Nat` literal, and the check as a `List.all`
/// predicate over `zipIdx` (encoding N of the certificate measurement),
/// closed by `decide`. `fn_def` is the full translated definition line;
/// `fn_name` the function the check applies.
pub fn certificate(name: &str, values: &[u64], fn_def: &str, fn_name: &str) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "-- Compile-time certificate printed by gabbro-check (lanes 111/121):"
    );
    let _ = writeln!(
        out,
        "-- the evaluated values of const-table `{name}` and their defining"
    );
    let _ = writeln!(
        out,
        "-- function, translated from the const fn source, as a `List.all`"
    );
    let _ = writeln!(out, "-- predicate (encoding N).");
    let _ = writeln!(out, "{fn_def}");
    let _ = writeln!(out, "def {name}Vals : List Nat :=");
    let werte: Vec<u128> = values.iter().map(|w| *w as u128).collect();
    let _ = writeln!(out, "  {}", crate::konst_lean::tabelle_lean(&werte));
    let _ = writeln!(
        out,
        "def {name}Ok : Bool := ({name}Vals.zipIdx).all (fun p => p.1 == {fn_name} p.2)"
    );
    let _ = writeln!(out, "theorem {name}_zert : {name}Ok = true := by decide");
    out
}

/// The certificate for a table computed by one const fn: translate the
/// body through `konst_lean`, then assemble. `None` where the body leaves
/// the printable fragment -- then there is no certificate, not a weaker
/// one.
pub fn certificate_of_const_fn(
    name: &str,
    values: &[u64],
    lean_fn: &str,
    param: &str,
    body: &Expr,
    funktionen: &HashMap<String, String>,
) -> Option<String> {
    let fn_def = crate::konst_lean::funktion_lean(lean_fn, param, body, funktionen)?;
    Some(certificate(name, values, &fn_def, lean_fn))
}
