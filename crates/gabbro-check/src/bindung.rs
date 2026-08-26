//! **THE BINDING SURFACE: what leaves a translation unit, and under which name.**
//!
//! Two rules stand here, and both answer one question from two sides: *what does the
//! boundary of a library carry?*
//!
//! | Code | Question |
//! |---|---|
//! | `N038` | does an EXPORTED declaration name something that is not exported? |
//! | `N039` | do two exported declarations bind under the SAME C name? |
//!
//! ## `N038` -- the export hull is closed
//!
//! Until 2026-08-25 `gabbro abi` decided the export set by **reachability**: it collected to
//! a fixpoint, because `table`, `lock`, `device` and `format` could not carry a `pub` at all.
//! A carrier therefore crossed the boundary as soon as some exported signature named it --
//! *without anything anywhere saying that it should go out.*
//!
//! > **D2 says "nothing is implicit", and an export set that falls out of the text is
//! > exactly that.** The library's author never wrote it down; he incurred it.
//!
//! Since the four carriers carry `pub`, the export set is written instead of computed -- and
//! therefore it can be **incomplete**. `N038` is the rule that names that: a `pub fn` whose
//! signature mentions a private table would give a `.gabi` pointing at something that does
//! not travel. *An interface that names something and does not explain it is none* -- the
//! same sentence `abi.rs` already used to justify its fixpoint, now as a refusal instead of
//! as a collection.
//!
//! **The difference from the fixpoint is the direction, and that is the whole thing.** The
//! fixpoint made the CONSEQUENCE honest; this rule refuses the CAUSE.
//!
//! ## `N039` -- the C name is the Gabbro name, so it can collide
//!
//! The product uses the ordinary C ABI and **does not mangle** (`abi.rs`, on the C side).
//! Two libraries that both carry a `pub fn lesen` therefore emit the symbol `lesen` twice --
//! and measured, that falls only at the LINKER:
//!
//! ```text
//! ld: multiple definition of `lesen'
//! ```
//!
//! > **A refusal that only the linker gives is no refusal of this compiler.** It names no
//! > Gabbro line, it does not know the module paths, and it arrives after the last pass.
//!
//! **There is still no mangling.** The generated C is meant to stay readable -- a reader of
//! the product should find `speicher_setze` and not a decorated form of it. The refusal is
//! the price of that, and it is deliberate: **refuse, never interpret** (design rule 3).
//! Whoever needs both names renames one; the compiler does not decide which of the two was
//! meant.
//!
//! ## How far a run reaches
//!
//! The rule holds over **one build**, and a build is more than one file:
//!
//! * within one tree -- unit **plus** the `--with` preamble, since that stands in front of
//!   the unit and is parsed with it: that is [`pass`];
//! * across the translation units of ONE run: that is [`Bindungsregister`], and the command
//!   carries it over its files.
//!
//! *What it does NOT see: two separate runs whose objects one `ld` links afterwards.* That
//! limit is real and stands in the pass's statement; it is the place where a manifest
//! (`manifest.rs`) takes over from a single invocation.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;

/// **Does this item bind outward, and under which name?**
///
/// Exhaustive over [`ItemArt`], with no `_` arm: a new item kind is a compile error here and
/// not a kind that quietly stops being checked. *Same construction as
/// [`crate::jeder_typausdruck_im_item`], and for the same reason.*
///
/// `None` does **not** mean "binds nothing" but *"carries no `pub`, so nothing goes out"* --
/// the constructs without a visibility word (`reason`, `state`, `accumulates`, …) drop out
/// here just as a private `fn` does.
pub fn ausgefuehrter_name(item: &Item) -> Option<&Ident> {
    match &item.art {
        // **A `spec fn` does NOT bind** -- it has no body in the product and no prototype;
        // `emit.rs` leaves at it immediately. A predicate helper claiming a symbol would be
        // a binding for a statement.
        ItemArt::Funktion(f) if matches!(f.klasse, Some(FnKlasse::Spec)) => None,
        ItemArt::Funktion(f) => f.oeffentlich.then_some(&f.name),
        ItemArt::Statisch(x) => x.oeffentlich.then_some(&x.name),
        ItemArt::Konst(k) => k.oeffentlich.then_some(&k.name),
        ItemArt::Typ(t) => t.oeffentlich.then_some(&t.name),
        ItemArt::Atomic(a) => a.oeffentlich.then_some(&a.name),
        ItemArt::Tabelle(t) => t.oeffentlich.then_some(&t.name),
        ItemArt::Lock(l) => l.oeffentlich.then_some(&l.name),
        ItemArt::Format(f) => f.oeffentlich.then_some(&f.name),
        ItemArt::Device(d) => d.oeffentlich.then_some(&d.name),
        // **A `module` and a `use` bind no symbol.** The module is a namespace the C does
        // not know; a `use` declares nothing, it fetches.
        ItemArt::Modul(_) | ItemArt::Use(_) => None,
        // The constructs without `pub` -- the grammar gives them none, so nothing of them
        // crosses the boundary either. **Written out and not swept up**, so that a `pub` on
        // one of them shows up here instead of vanishing quietly.
        ItemArt::Reason(_)
        | ItemArt::State(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Accumulates(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_) => None,
    }
}

/// **The names the EXPORTED form of an item mentions** -- that is, what of it stands in the
/// `.gabi`.
///
/// For a function that is its HEAD and not its body: what the body touches stays inside, and
/// `abi.rs` cuts it away on purpose. For everything else it is the whole declaration, since
/// that travels verbatim.
fn genannte_namen(item: &Item, aus: &mut Vec<(String, Span)>) {
    // The nominal names of a type expression -- a `path` and the table of an `index into T`.
    // Everything else is built in and explains itself.
    fn typ_namen(t: &TypExpr, aus: &mut Vec<(String, Span)>) {
        match t {
            TypExpr::Pfad(p) => {
                if let Some(i) = p.teile.last() {
                    aus.push((i.text.clone(), i.span));
                }
            }
            TypExpr::Index { tabelle, .. } => aus.push((tabelle.text.clone(), tabelle.span)),
            _ => {}
        }
    }
    fn ort_namen(o: &Ort, aus: &mut Vec<(String, Span)>) {
        aus.push((o.basis.text.clone(), o.basis.span));
    }
    fn expr_namen(e: &Expr, aus: &mut Vec<(String, Span)>) {
        for x in crate::alle_ausdruecke(e) {
            match &x.art {
                ExprArt::Ort(o) => ort_namen(o, aus),
                ExprArt::Ruf(r) => {
                    if let Some(p) = r.path() {
                        if let Some(i) = p.teile.last() {
                            aus.push((i.text.clone(), i.span));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    fn pred_namen(p: &Pred, span: Span, aus: &mut Vec<(String, Span)>) {
        let mut n = Vec::new();
        crate::gruppe::pred_namen_oeffentlich(p, &mut n);
        for x in n {
            aus.push((x, span));
        }
    }

    // The declared type expressions -- one walk that knows every item kind, and the single
    // reader of that question (W7).
    crate::jeder_typausdruck_im_item(item, &mut |t| typ_namen(t, aus));

    match &item.art {
        ItemArt::Funktion(f) => {
            if let Some(r) = &f.fehler {
                aus.push((r.text.clone(), r.span));
            }
            if let Some(p) = &f.verfeinert {
                if let Some(i) = p.teile.last() {
                    aus.push((i.text.clone(), i.span));
                }
            }
            for w in f.effects.iter().flat_map(|w| &w.liste) {
                match &w.art {
                    WirkungArt::Liest(o)
                    | WirkungArt::Schreibt(o)
                    | WirkungArt::Sperrt(o)
                    | WirkungArt::SperrtGeteilt(o)
                    | WirkungArt::Verbraucht(o)
                    | WirkungArt::Veroeffentlicht(o) => ort_namen(o, aus),
                    WirkungArt::Maskiert(i) | WirkungArt::Belegt(i) => {
                        aus.push((i.text.clone(), i.span))
                    }
                    WirkungArt::Divergiert | WirkungArt::Rein => {}
                }
            }
            for p in f.requires.iter().chain(&f.ensures) {
                pred_namen(p, f.name.span, aus);
            }
            for m in &f.maintains {
                aus.push((m.text.clone(), m.span));
            }
            if let Some(c) = &f.costs {
                expr_namen(c, aus);
            }
        }
        // **A table's `count` is its address space, and without it `index into T` has no
        // bound** -- it travels, so it has to be explainable.
        ItemArt::Tabelle(t) => {
            if let Some(k) = &t.kapazitaet {
                expr_namen(k, aus);
            }
            if let Some(h) = &t.hinterlegt {
                aus.push((h.text.clone(), h.span));
            }
            for i in &t.invarianten {
                pred_namen(&i.pred, t.name.span, aus);
            }
        }
        ItemArt::Lock(l) => {
            for o in &l.schuetzt {
                ort_namen(o, aus);
            }
            expr_namen(&l.rang, aus);
            for e in l.haltezeit.iter().chain(&l.geteilte_haltezeit) {
                expr_namen(e, aus);
            }
            if let Some(m) = &l.maskiert {
                aus.push((m.text.clone(), m.span));
            }
        }
        ItemArt::Konst(k) => expr_namen(&k.wert, aus),
        ItemArt::Statisch(s) => expr_namen(&s.wert, aus),
        ItemArt::Atomic(a) => {
            if let Some(o) = &a.beobachtet {
                aus.push((o.text.clone(), o.span));
            }
        }
        ItemArt::Device(d) => {
            for r in d.register.iter().chain(d.baenke.iter().flat_map(|b| &b.register)) {
                expr_namen(&r.versatz, aus);
            }
        }
        // These mention nothing beyond their type expressions, or they do not travel at all.
        // **Written out, no `_`** -- see [`ausgefuehrter_name`].
        ItemArt::Typ(_)
        | ItemArt::Format(_)
        | ItemArt::Modul(_)
        | ItemArt::Use(_)
        | ItemArt::Reason(_)
        | ItemArt::State(_)
        | ItemArt::Assume(_)
        | ItemArt::Axiom(_)
        | ItemArt::Check(_)
        | ItemArt::Rcu(_)
        | ItemArt::Gruppe(_)
        | ItemArt::Accumulates(_)
        | ItemArt::Walk(_)
        | ItemArt::Entry(_)
        | ItemArt::Entrust(_)
        | ItemArt::Boot(_) => {}
    }
}

/// **A register over the binding names of ONE BUILD** -- across more than one tree.
///
/// The command carries it over its files; [`pass`] keeps its own per tree. Both say `N039`,
/// and **both say it from this file**: a code belongs to exactly one file, or every poison
/// probe on it is ambiguous (`pruefe-kennungen.py`).
#[derive(Default)]
pub struct Bindungsregister {
    belegt: std::collections::BTreeMap<String, (String, String)>,
}

impl Bindungsregister {
    pub fn neu() -> Self {
        Self::default()
    }

    /// **Takes in the exported names of a tree and reports each collision AGAINST THE
    /// EARLIER TREES.**
    ///
    /// Two limits sit in it, and both are measured:
    ///
    /// * `ab` cuts the `--with` preamble away. It stands in EVERY tree of a run, and without
    ///   that boundary the register reported the library against itself.
    /// * **Within one tree it does NOT report.** That is [`pass`]'s job, and it runs over
    ///   every tree -- reporting from both gave the same collision twice, with the same
    ///   finger pointing. *A guard that counts double lets a number grow that nobody
    ///   recomputes.*
    pub fn nimm_auf(&mut self, herkunft: &str, baum: &Programm, ab: usize, absagen: &mut Absagen) {
        // **The first carrier per name wins** -- the FURTHER ones of the same tree have
        // already been reported by [`pass`], and a second finger on one line is not a second
        // measurement.
        let mut eigene: std::collections::BTreeMap<String, (String, Span)> = Default::default();
        for (name, voll, span) in ausgefuehrte_namen(baum) {
            if (span.von as usize) < ab {
                continue;
            }
            eigene.entry(name).or_insert((voll, span));
        }
        for (name, (voll, span)) in eigene {
            match self.belegt.get(&name) {
                // The same file twice on one command line is ONE translation unit, named
                // twice -- not a collision.
                Some((_, wo)) if wo == herkunft => {}
                Some((erster, wo)) => absagen.schiebe(absage(&name, span, erster, wo)),
                None => {
                    self.belegt.insert(name, (voll, herkunft.to_string()));
                }
            }
        }
    }
}

/// The one wording of `N039` -- one text, one place.
fn absage(name: &str, span: Span, erster: &str, wo: &str) -> Absage {
    Absage::fehler(
        "N039",
        span,
        format!("`{name}` binds twice in this build: `{erster}` in {wo} carries the same C name"),
    )
    .mit_notiz(
        "the C name IS the Gabbro name -- this emitter does not mangle, so the generated \
         source stays readable, and two exported items of one name become one symbol",
    )
    .mit_notiz("rename one of the two, or keep one of them out of the interface (drop its `pub`)")
}

/// **The pass over ONE tree** -- unit together with its `--with` preamble.
///
/// It runs behind the name pass, because it asks that pass's question one level up:
/// `N001` in `namen.rs` holds a name against its SCOPE, `N039` here against the BINDING
/// SURFACE -- and that one knows no modules.
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // -- N038: the hull of the export set -----------------------------------------------
    //
    // First the export set, then every exported name against it. What this unit does not
    // declare is none of its business -- **the same class as `N025` in `namen.rs`**, and for
    // the same reason. A fragment names things from outside the cut, and those must not
    // count as private.
    let mut erklaert: std::collections::HashMap<String, bool> = Default::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        // The name the item is declared under -- regardless of `pub`, since that is exactly
        // the question being asked.
        let Some(n) = item.art.name() else { return };
        // A `spec fn` does not bind but it certainly declares -- a `pub fn` naming a
        // `spec fn` in `requires` names nothing private. *It is a proof device and does not
        // travel into the C anyway.*
        if matches!(&item.art, ItemArt::Funktion(f) if matches!(f.klasse, Some(FnKlasse::Spec))) {
            return;
        }
        let offen = ausgefuehrter_name(item).is_some();
        // The same name twice in two modules: **the more open one wins**, or `N038` reports
        // at a place where the user meant the public one. That case itself is caught by
        // `N001` in `namen.rs`, or by `N039` below.
        erklaert
            .entry(n.text.clone())
            .and_modify(|x| *x |= offen)
            .or_insert(offen);
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        let Some(traeger) = ausgefuehrter_name(item) else {
            return;
        };
        let mut genannt = Vec::new();
        genannte_namen(item, &mut genannt);
        let mut gemeldet: std::collections::BTreeSet<String> = Default::default();
        for (n, span) in genannt {
            if n == traeger.text || erklaert.get(&n).copied().unwrap_or(true) {
                continue;
            }
            if !gemeldet.insert(n.clone()) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "N038",
                    span,
                    format!(
                        "`{}` is exported and names `{n}`, which is not -- the interface \
                         would point at something that does not travel",
                        traeger.text
                    ),
                )
                .mit_notiz(
                    "an interface that names something and does not explain it is none: \
                     `gabbro abi` writes only what carries `pub`",
                )
                .mit_notiz(format!("either write `pub` at `{n}`, or keep it out of the signature")),
            );
        }
    });

    // -- N039: one C name, one binding --------------------------------------------------
    //
    // **Within THIS tree**, that is, unit together with the `--with` preamble. Across the
    // trees of one run the command keeps a [`Bindungsregister`].
    let mut belegt: std::collections::BTreeMap<String, String> = Default::default();
    for (name, voll, span) in ausgefuehrte_namen(baum) {
        match belegt.get(&name) {
            Some(erster) => absagen.schiebe(absage(&name, span, erster, "this unit")),
            None => {
                belegt.insert(name, voll);
            }
        }
    }
}

/// **Every name that binds out of this tree** -- in source order, with its full path and the
/// place it stands at.
///
/// **One register for two readers** (W7): [`pass`] asks about duplicates WITHIN the tree,
/// [`Bindungsregister`] about ones BETWEEN the trees of a run. Two surveys of one question
/// would be two answers that can drift apart.
fn ausgefuehrte_namen(baum: &Programm) -> Vec<(String, String, Span)> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let Some(n) = ausgefuehrter_name(item) {
            aus.push((
                n.text.clone(),
                crate::umgebung::qualifiziere(modul, &n.text),
                n.span,
            ));
        }
    });
    aus
}
