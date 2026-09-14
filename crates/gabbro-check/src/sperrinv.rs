//! **Lock invariants on the lock declaration (lane 156).**
//!
//! `lock L protects { A, B } rank 0 invariant <pred>;` states what holds
//! whenever `L` is free: the sequential face of `SperrInv` in
//! `grammatik/Grammatik/SperreSem.lean`. The checker carries three decidable
//! thirds of `SperrInvOk` and records the rest:
//!
//! * **`N275`** -- the invariant reads a carrier the lock does not protect.
//!   This is the read half of `SperrInvOk`'s second conjunct, decided per
//!   declaration: `protects` names the carriers, the invariant may read only
//!   those (plus named constants, which are values, not state).
//! * **`N276`** -- the invariant is not a pure contract expression. `old`,
//!   `result`, calls (sugar calls like `count` included), `Held`, reason
//!   values, function values, quantifiers, reachability and array literals
//!   have no meaning over a memory snapshot, so they are refused where the
//!   invariant must be one.
//! * **`N277`** -- the invariant names something the unit declares nowhere
//!   (neither a carrier nor a constant). A name no pass can resolve would
//!   otherwise slip through: the body passes never walk this clause.
//!
//! What the checker does NOT decide is the USER's obligation, and that is by
//! shape, not by reticence: every `locks L { ... }` body must re-establish
//! the invariant at release (the `freiH` check, which fails as
//! `logik schleife`). Like `ensures`, that is recorded, not refused --
//! `pflichten::Art::Sperrinvariante` counts one duty per lock invariant, and
//! `gabbro lean-g` prints the `SperrInv` family for it.
//!
//! **`N278`/`N279` stay reserved** for the writer side (a function that writes
//! a protected carrier owing the guard at its own access -- the `hWatch`
//! half) and for the release shape (a `locks` body that cannot re-establish
//! by construction). Neither is refused here.
//!
//! A `protects` entry may name a carrier or one of its fields (`beispiele/10`
//! protects `{ belegt, rechte, objekt }` -- field names). The invariant reads
//! carriers (`Kappenraum.slots[i].rechte`), so each entry is resolved to its
//! carrier first: a carrier name to itself, a field name to its table.
//! Entries resolving to neither are another pass's question, not this one's.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// What the unit declares: carriers (tables, globals, states), table fields,
/// and named constants (values, readable in any pure predicate).
struct Bestand {
    traeger: BTreeSet<String>,
    feld_von: BTreeMap<String, String>,
    konstanten: BTreeSet<String>,
}

fn bestand(baum: &Programm) -> Bestand {
    let mut b = Bestand {
        traeger: BTreeSet::new(),
        feld_von: BTreeMap::new(),
        konstanten: BTreeSet::new(),
    };
    crate::fuer_jedes_item(baum, &mut |item| {
        match &item.art {
            ItemArt::Tabelle(t) => {
                b.traeger.insert(t.name.text.clone());
                if let Some(slot) = &t.slot {
                    for f in &slot.felder {
                        b.feld_von.insert(f.name.text.clone(), t.name.text.clone());
                    }
                }
            }
            ItemArt::Statisch(s) => {
                b.traeger.insert(s.name.text.clone());
            }
            ItemArt::Konst(k) => {
                b.konstanten.insert(k.name.text.clone());
            }
            _ => {}
        }
    });
    // A `state` is a carrier too (`gruppe.rs` counts it beside tables and
    // globals for the same question).
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::State(s) = &item.art {
            b.traeger.insert(s.name.text.clone());
        }
    });
    b
}

/// The carriers a `protects` list covers, resolved to carrier names.
fn schutzraum(lock: &LockDecl, b: &Bestand) -> BTreeSet<String> {
    let mut aus = BTreeSet::new();
    for o in &lock.schuetzt {
        let n = &o.basis.text;
        if b.traeger.contains(n) {
            aus.insert(n.clone());
        } else if let Some(t) = b.feld_von.get(n) {
            aus.insert(t.clone());
        }
        // Entries resolving to neither are another pass's question.
    }
    aus
}

/// One walk over the invariant: purity refusals plus the carrier reads of the
/// pure skeleton. Refused subtrees contribute no reads -- a call's arguments
/// are not invariant reads, they are part of the refused call.
struct Gang<'a> {
    sperre: &'a str,
    absagen: &'a mut Absagen,
    liest: Vec<Ort>,
}

fn ort_merken(g: &mut Gang<'_>, o: &Ort) {
    g.liest.push(o.clone());
    for s in &o.suffixe {
        if let OrtSuffix::Index(e) = s {
            ausdruck(g, e);
        }
    }
}

fn ausdruck(g: &mut Gang<'_>, e: &Expr) {
    match &e.art {
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch => {}
        ExprArt::Ort(o) => ort_merken(g, o),
        ExprArt::Klammer(x) => ausdruck(g, x),
        ExprArt::Unaer(_, x) => ausdruck(g, x),
        ExprArt::Binaer(_, a, b) => {
            ausdruck(g, a);
            ausdruck(g, b);
        }
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                ort_merken(g, o)
            }
            Eingebaut::Sizeof(TypOderOrt::Typ(_)) | Eingebaut::Lenof(TypOderOrt::Typ(_)) => {}
            Eingebaut::Aligned(a, c) => {
                ausdruck(g, a);
                ausdruck(g, c);
            }
        },
        ExprArt::Ruf(_) => unrein(
            g,
            e.span,
            "a call (conversions and `Some`/`None` included: every `Ruf` runs code)",
        ),
        ExprArt::LibraryCall(_) => unrein(g, e.span, "a library call"),
        ExprArt::Alt(_) => unrein(g, e.span, "`old(...)` (there is no entry world here)"),
        ExprArt::Ergebnis => unrein(g, e.span, "`result` (there is no answer here)"),
        ExprArt::FnWert(_) => unrein(g, e.span, "a function value"),
        ExprArt::Grund { .. } => unrein(g, e.span, "a reason value"),
        ExprArt::Zaehle { .. } => {
            unrein(g, e.span, "`count` (sugar for a call to the generated count function)")
        }
        ExprArt::ArrayLit(_) => unrein(g, e.span, "an array literal"),
    }
}

fn praedikat(g: &mut Gang<'_>, p: &Pred) {
    match &p.art {
        PredArt::Vergleich(e) => ausdruck(g, e),
        PredArt::Klammer(q) | PredArt::Nicht(q) => praedikat(g, q),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            praedikat(g, a);
            praedikat(g, b);
        }
        PredArt::Quantor(_) => unrein(g, p.span, "a quantifier"),
        PredArt::Element(_, _) => unrein(g, p.span, "a domain membership"),
        PredArt::Erreicht { .. } => unrein(g, p.span, "a reachability claim"),
        PredArt::Held { .. } => unrein(g, p.span, "`Held` (a derivation fact, not a value)"),
    }
}

fn unrein(g: &mut Gang<'_>, span: Span, was: &str) {
    g.absagen.schiebe(
        Absage::fehler(
            "N276",
            span,
            format!(
                "the invariant of lock `{}` is not pure -- {was}",
                g.sperre
            ),
        )
        .mit_notiz(
            "a lock invariant is a predicate over a memory snapshot (`SperrInv.inv`): \
             literals, named constants, carrier reads and the arithmetic, comparison \
             and boolean operators over them. Anything that runs code, names an \
             entry world, an answer, a witness or a domain does not denote there",
        ),
    );
}

/// The lock data lane 175 (`fusswache2.rs`) reuses: per lock (by short name) the
/// protected carriers -- a carrier name to itself, a field name to its table,
/// exactly the resolution the `N275` leg reads -- and whether the lock declares
/// an `invariant` clause (the surface form of `S.orte L` with `S.inv L`).
pub(crate) struct Sperrdaten {
    pub schutz: BTreeMap<String, BTreeSet<String>>,
    pub invariante: BTreeSet<String>,
}

pub(crate) fn sperrdaten(baum: &Programm) -> Sperrdaten {
    let b = bestand(baum);
    let mut aus = Sperrdaten {
        schutz: BTreeMap::new(),
        invariante: BTreeSet::new(),
    };
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            let mut s = BTreeSet::new();
            for o in &l.schuetzt {
                let n = o.basis.text.clone();
                if b.traeger.contains(&n) {
                    s.insert(n);
                } else if let Some(t) = b.feld_von.get(&n) {
                    s.insert(t.clone());
                }
            }
            let n = l.name.text.rsplit("::").next().unwrap_or(&l.name.text).to_string();
            aus.schutz.insert(n.clone(), s);
            if l.invariante.is_some() {
                aus.invariante.insert(n);
            }
        }
    });
    aus
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let b = bestand(baum);
    let mut sperren: Vec<LockDecl> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            sperren.push(l.clone());
        }
    });
    for l in &sperren {
        let Some(inv) = &l.invariante else { continue };
        let schutz = schutzraum(l, &b);
        let mut g = Gang { sperre: &l.name.text, absagen, liest: Vec::new() };
        praedikat(&mut g, inv);
        let liest = g.liest;
        let absagen = &mut g.absagen;
        for o in &liest {
            let n = &o.basis.text;
            if schutz.contains(n) || b.konstanten.contains(n) {
                continue;
            }
            if b.traeger.contains(n) {
                absagen.schiebe(
                    Absage::fehler(
                        "N275",
                        o.span,
                        format!(
                            "the invariant of lock `{}` reads carrier `{n}` which the lock does not protect",
                            l.name.text
                        ),
                    )
                    .mit_notiz(
                        "an invariant over carriers the lock does not guard is not a \
                         resource invariant (`SperrInvOk`): the acquiring thread's \
                         environment move may change exactly the protected carriers, \
                         so anything wider is stale at the first acquire",
                    ),
                );
            } else {
                absagen.schiebe(
                    Absage::fehler(
                        "N277",
                        o.span,
                        format!(
                            "the invariant of lock `{}` names `{n}`, which is neither a protected carrier nor a named constant",
                            l.name.text
                        ),
                    )
                    .mit_notiz(
                        "a lock invariant may read the lock's protected carriers and \
                         named constants -- nothing else. A lock declaration binds no \
                         parameters and no locals, so a name from a body would dangle \
                         here even where the unit declares it",
                    ),
                );
            }
        }
    }
}
