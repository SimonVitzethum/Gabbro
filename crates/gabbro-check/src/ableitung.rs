//! **«T1» -- the DERIVATION of the effects, and it draws on no declaration.**
//!
//! `aufrufgraph::huelle_der_gerufenen` computes a hull already -- but it takes from the
//! callee its **declared** `effects` (`Knoten.eigen`). While the declarations still stand
//! that is a usable approximation; **as a derivation it will not do**, and the reason is the
//! very thing at issue:
//!
//! > An over-declared callee bequeaths its padding to the caller's computed set. The caller
//! > then looks *identical* although it stands just as wide -- **the measurement covers up
//! > exactly the error it is meant to find.** And after the derivation the declarations it
//! > draws on are gone.
//!
//! So what stands here is the fixpoint over the **bodies**:
//!
//! ```text
//! derived[f] = deeds(body f)
//!            u  U over every call edge (g, args):  ersetze(derived[g], param g, args)
//!            u  U over every indirect call:        ersetze(contract, param, args)
//! ```
//!
//! ## Where the floor is, and it is not a gap
//!
//! An `extern fn` has no body, an `asm` hull is a sealed hole. For both **the declaration is
//! the source** -- and it stays the source after the derivation. *That is the trust surface
//! and not bookkeeping:* the 80 such entries in the corpus cannot go to zero, and whoever
//! counts them into the mark promises a saving no build can deliver. The edge is its own
//! kind of origin, distinct from an ordinary call hop, so that the difference stands in the
//! output instead of in a footnote.
//!
//! ## Why the fixpoint terminates -- and why the argument in §24 does NOT suffice
//!
//! `PLAN-HARDWARE.md` §24 says: *"effects form a finite lattice (union over a finite set of
//! places), so the fixpoint over the cycles converges anyway."*
//!
//! **The set of places is not finite.** `ersetze` carries a place across the call boundary
//! by replacing the parameter name with the argument expression -- and in a cycle it grows:
//!
//! ```text
//! impl fn geh(k : ptr<…> Knoten) effects { writes k.wert } { k.wert = 0; geh(k.kind); }
//!
//! round 1   writes k.wert
//! round 2   writes k.kind.wert
//! round 3   writes k.kind.kind.wert          …  an infinite ascending chain
//! ```
//!
//! *The lattice is finite as long as nobody creates new places; creating them is precisely
//! what the bridge across the call boundary does.* Hence a **widening**: a place deeper than
//! `TIEFE_MAX` is cut back to its prefix. That is coarse in the safe direction -- `deckt`
//! works over prefixes, `writes k` covers `writes k.kind.wert` -- and it makes the set of
//! places finite, so the fixpoint terminates.
//!
//! **Whether it ever fires is measured and stands in the output** (`verbreitert`). A
//! widening nobody counts is a silent imprecision -- the same class as a `_` arm that
//! quietly does the wrong thing.

use gabbro_syntax::ast::*;
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// **How deep a place expression may get before the widening cuts it.**
///
/// Four, and the number is measured, not chosen: the deepest place that stands literally in
/// the corpus is `writes v.slots[i].a` — base plus three steps. A cap at the measured
/// maximum would cut a legitimate place the first time somebody writes a fourth; a cap far
/// above it would let a recursion run a long time before the widening bites. *One step of
/// head-room, and the count in the output says whether it was ever needed.*
pub const TIEFE_MAX: usize = 4;

/// **The edge of the run, named** (R16). A fixpoint that stops silently is a lower bound
/// that looks like an answer.
pub const RUNDEN_MAX: usize = 64;

/// **Where one derived effect comes from.** One hop — the full path is walked by
/// [`Ableitung::pfad`].
#[derive(Debug, Clone, PartialEq)]
pub enum Weg {
    /// This body does it, at this place. **The end of every path.**
    Rumpf(Span),
    /// It came across a call to a callee that HAS a body, where it read `innen`.
    Ueber { gerufener: String, innen: String },
    /// The callee has **no body** — `extern`, `prim`, or a sealed `asm` hull. Its
    /// declaration is the source, and it stays the source after the derivation.
    Rand { gerufener: String, innen: String },
    /// An indirect call through a place: the contract at the pointer type.
    Zeiger { ort: String, innen: String },
    /// **A callee the COMPILER supplies, not the user:** a `device` transition, a generated
    /// `T::insert`, a device handle. Its effects come out of the declaration of the table or
    /// device, and they are neither a body nor bookkeeping.
    ///
    /// > It is its own hop and not a `Rand` because the two answer different questions.
    /// > *`Rand` says "here the checked world ends"; this says "here the compiler wrote the
    /// > line already".* Counting a generated op as trust surface would inflate the
    /// > un-removable half of the mark with entries nobody ever typed.
    Vertrag { traeger: String, innen: String },
    /// The place was cut to its prefix by the widening — see `TIEFE_MAX`.
    Verbreitert { von: String },
}

/// What the derivation knows about one function.
#[derive(Debug, Clone, Default)]
pub struct Abgeleitet {
    pub wirkungen: BTreeSet<String>,
    /// One origin per effect. **The FIRST one found wins** — a set has no second entry, and
    /// two paths to the same effect do not make it two effects.
    pub herkunft: BTreeMap<String, Weg>,
    /// **A lower bound from here on, and it says why** (R16). An unknown callee, an
    /// argument that is not a place, an indirect call without a contract.
    pub unvollstaendig: Option<String>,
}

#[derive(Debug, Default)]
pub struct Ableitung {
    pub je: BTreeMap<String, Abgeleitet>,
    /// How many rounds the fixpoint needed. **`1` would mean the graph is a DAG in the
    /// order we happened to walk it** — the number belongs in the output, not in a claim.
    pub runden: usize,
    /// How often the widening cut a place. *Measured, not assumed.*
    pub verbreitert: usize,
    /// Set when `RUNDEN_MAX` was hit: everything below is a lower bound.
    pub abgebrochen: bool,
}

impl Ableitung {
    /// **The origin path of one effect, from the caller down to the body that does it.**
    ///
    /// *This is an output and not a second analysis* — every hop was already recorded while
    /// the fixpoint ran. The path stops at a `Rumpf` (the deed), at a `Rand` (the trust
    /// surface), or when it has walked more hops than there are functions, which cannot
    /// happen and is caught anyway.
    pub fn pfad(&self, funktion: &str, wirkung: &str) -> Vec<(String, String, Weg)> {
        let mut aus = Vec::new();
        let mut hier = funktion.to_string();
        let mut was = wirkung.to_string();
        for _ in 0..=self.je.len() {
            let Some(a) = self.je.get(&hier) else { return aus };
            let Some(w) = a.herkunft.get(&was) else { return aus };
            aus.push((hier.clone(), was.clone(), w.clone()));
            match w {
                Weg::Rumpf(_)
                | Weg::Rand { .. }
                | Weg::Zeiger { .. }
                | Weg::Vertrag { .. } => return aus,
                Weg::Verbreitert { von } => was = von.clone(),
                Weg::Ueber { gerufener, innen } => {
                    hier = gerufener.clone();
                    was = innen.clone();
                }
            }
        }
        aus
    }
}


/// **Cut a place to `TIEFE_MAX` steps.** Returns `None` when nothing had to be cut.
///
/// The prefix is taken at a step boundary (`.` or `[`), never inside a name — `a.bcd` must
/// not become `a.b`. *A prefix that is not a place covers nothing and would silently drop
/// the effect instead of widening it.*
fn verbreitere(w: &str) -> Option<String> {
    let (kopf, ort) = w.rsplit_once(' ')?;
    let mut grenzen: Vec<usize> = Vec::new();
    for (i, c) in ort.char_indices() {
        if c == '.' || c == '[' {
            grenzen.push(i);
        }
    }
    // `TIEFE_MAX` steps are KEPT; the cut sits at the boundary that would open the next one.
    if grenzen.len() <= TIEFE_MAX {
        return None;
    }
    Some(format!("{kopf} {}", &ort[..grenzen[TIEFE_MAX]]))
}

/// **The widening, reachable from a probe.**
///
/// It fires nowhere in today's corpus (`widening fired 0x`), and a piece of code that
/// nothing reaches is a piece of code nobody has measured. *A guard nobody can trip is a
/// guard nobody can trust* — so the probe trips it directly, and the corpus number stays a
/// statement about the corpus instead of about the code's existence.
pub fn verbreitere_fuer_probe(w: &str) -> Option<String> {
    verbreitere(w)
}

/// **Derive the effects of every function in a unit.** `weit` as in
/// `wirkungen::rumpfwirkungen_mit`: with it, reads through parameters count too — and an
/// elaborator that WRITES the line has to write those, because the caller wants to see what
/// happens to his pointer.
pub fn leite_ab(baum: &Programm, weit: bool) -> Ableitung {
    let g = crate::aufrufgraph::erhebe(baum);
    let (konstanten, weltnamen) = crate::wirkungen::welt_und_konstanten(baum);

    // **What each body does by itself** — and for a function without one, what it declares.
    let mut eigen: BTreeMap<String, BTreeMap<String, Weg>> = Default::default();
    let mut ohne_rumpf: BTreeSet<String> = Default::default();
    // Graph nodes that are no `fn` item at all -- see the loop below.
    let mut vertraglich: BTreeSet<String> = Default::default();
    let mut stumm: BTreeMap<String, String> = Default::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let key = crate::umgebung::qualifiziere(modul, &f.name.text);
        let mut m: BTreeMap<String, Weg> = Default::default();
        match &f.rumpf {
            FnRumpf::Block(b) => {
                for (w, sp) in
                    crate::wirkungen::rumpfwirkungen_mit_ort(f, b, &konstanten, &weltnamen, weit)
                {
                    m.insert(w, Weg::Rumpf(sp));
                }
            }
            // **No body — the declaration IS the source, and it stays one.** A `spec fn`
            // with a `= pred` body computes nothing at runtime; an `asm` hull is a sealed
            // hole; an `extern fn` is another unit's promise. All three are the edge of the
            // checked world.
            _ => {
                ohne_rumpf.insert(key.clone());
                match &f.effects {
                    Some(w) => {
                        for e in &w.liste {
                            m.insert(e.art.text(), Weg::Rumpf(e.span));
                        }
                    }
                    None => {
                        stumm.insert(key.clone(), format!("`{key}` declares no `effects`"));
                    }
                }
            }
        }
        eigen.insert(key, m);
    });

    // **The graph carries nodes that are no `fn` item, and forgetting them is a hole that
    // looks like a finding.**
    //
    // A `device` transition, a device handle (`Vtd(basis)` is a constructor, not a call) and
    // a generated table operation (`T::insert`) all stand in `Graph::knoten` with their
    // effects — `aufrufgraph.rs` says of the first two that missing them was *"a gap in the GRAPH, not in
    // the program"*, and of the third that it was the **third instance of the same fix at the
    // same place.**
    //
    // *Measured: without this loop the derivation reported 18 functions as a lower bound with
    // "unknown to the graph" -- against 3 for the hull over the declarations.* The fourth
    // instance of the same class, and it was caught by holding the two bases against each
    // other.
    for (key, k) in &g.knoten {
        if eigen.contains_key(key) {
            continue;
        }
        ohne_rumpf.insert(key.clone());
        vertraglich.insert(key.clone());
        let m: BTreeMap<String, Weg> = k
            .eigen
            .iter()
            .map(|w| {
                (
                    w.clone(),
                    Weg::Vertrag { traeger: key.clone(), innen: w.clone() },
                )
            })
            .collect();
        if m.is_empty() && !k.hat_effects {
            stumm.insert(key.clone(), format!("`{key}` declares no `effects`"));
        }
        eigen.insert(key.clone(), m);
    }

    let mut je: BTreeMap<String, Abgeleitet> = Default::default();
    for (k, m) in &eigen {
        je.insert(
            k.clone(),
            Abgeleitet {
                wirkungen: m.keys().cloned().collect(),
                herkunft: m.clone(),
                unvollstaendig: stumm.get(k).cloned(),
            },
        );
    }

    let mut verbreitert = 0usize;
    let mut runden = 0usize;
    let mut abgebrochen = false;
    loop {
        runden += 1;
        if runden > RUNDEN_MAX {
            abgebrochen = true;
            for a in je.values_mut() {
                if a.unvollstaendig.is_none() {
                    a.unvollstaendig = Some(format!(
                        "the fixpoint did not settle within {RUNDEN_MAX} rounds"
                    ));
                }
            }
            break;
        }
        let mut geaendert = false;
        // The keys are walked in a fixed order so that two runs over the same tree give the
        // same origins -- a path that depends on `BTreeMap` iteration order is not a finding.
        let namen: Vec<String> = je.keys().cloned().collect();
        for name in &namen {
            let Some(k) = g.knoten.get(name) else { continue };
            // A function without a body inherits nothing from its callees: it HAS none.
            if ohne_rumpf.contains(name) {
                continue;
            }
            let mut zuwachs: Vec<(String, Weg)> = Vec::new();
            let mut offen: Option<String> = None;
            for (ziel, args) in &k.rufe {
                let ziel_par: Vec<Option<String>> = g
                    .knoten
                    .get(ziel)
                    .map(|z| z.parameter.iter().cloned().map(Some).collect())
                    .unwrap_or_default();
                let Some(unten) = je.get(ziel) else {
                    if offen.is_none() {
                        offen = Some(format!("`{ziel}` is unknown to the graph"));
                    }
                    continue;
                };
                if offen.is_none() {
                    offen.clone_from(&unten.unvollstaendig);
                }
                let am_rand = ohne_rumpf.contains(ziel);
                let am_vertrag = vertraglich.contains(ziel);
                for w in &unten.wirkungen {
                    let (neu, unklar) = crate::aufrufgraph::ersetze(w, &ziel_par, args);
                    if unklar && offen.is_none() {
                        offen = Some(format!(
                            "an argument of the call to `{ziel}` is not a place, so `{w}` \
                             cannot be carried across"
                        ));
                    }
                    let her = if am_vertrag {
                        Weg::Vertrag { traeger: ziel.clone(), innen: w.clone() }
                    } else if am_rand {
                        Weg::Rand { gerufener: ziel.clone(), innen: w.clone() }
                    } else {
                        Weg::Ueber { gerufener: ziel.clone(), innen: w.clone() }
                    };
                    zuwachs.push((neu, her));
                }
            }
            // Edges without argument knowledge (`transition`): no substitution, no bridge.
            for ziel in k.ruft.iter().filter(|z| !k.rufe.iter().any(|(t, _)| &t == z)) {
                let Some(unten) = je.get(ziel) else {
                    if offen.is_none() {
                        offen = Some(format!("`{ziel}` is unknown to the graph"));
                    }
                    continue;
                };
                if offen.is_none() {
                    offen.clone_from(&unten.unvollstaendig);
                }
                let am_rand = ohne_rumpf.contains(ziel);
                let am_vertrag = vertraglich.contains(ziel);
                for w in &unten.wirkungen {
                    let her = if am_vertrag {
                        Weg::Vertrag { traeger: ziel.clone(), innen: w.clone() }
                    } else if am_rand {
                        Weg::Rand { gerufener: ziel.clone(), innen: w.clone() }
                    } else {
                        Weg::Ueber { gerufener: ziel.clone(), innen: w.clone() }
                    };
                    zuwachs.push((w.clone(), her));
                }
            }
            // **The indirect calls.** There is nothing to descend into -- a place carries no
            // key. The contract at the pointer type is the source, and that makes it a
            // `Rand` for the same reason an `extern fn` is one.
            for i in &k.indirect {
                if !i.has_contract {
                    if offen.is_none() {
                        offen = Some(format!(
                            "the callee at `{}` is not statically known, and its type \
                             declares no `effects`",
                            i.place
                        ));
                    }
                    continue;
                }
                for w in &i.effects {
                    let (neu, unklar) = crate::aufrufgraph::ersetze(w, &i.parameters, &i.arguments);
                    if unklar && offen.is_none() {
                        offen = Some(format!(
                            "an argument of the indirect call at `{}` is not a place, so \
                             `{w}` cannot be carried across",
                            i.place
                        ));
                    }
                    zuwachs.push((neu, Weg::Zeiger { ort: i.place.clone(), innen: w.clone() }));
                }
            }
            let a = je.get_mut(name).expect("key came from `je`");
            for (w, her) in zuwachs {
                // **The widening, and it is counted.**
                let (w, her) = match verbreitere(&w) {
                    Some(kurz) if kurz != w => {
                        verbreitert += 1;
                        (kurz, Weg::Verbreitert { von: w })
                    }
                    _ => (w, her),
                };
                if a.wirkungen.insert(w.clone()) {
                    geaendert = true;
                    a.herkunft.insert(w, her);
                }
            }
            if let Some(o) = offen {
                if a.unvollstaendig.is_none() {
                    a.unvollstaendig = Some(o);
                    geaendert = true;
                }
            }
        }
        if !geaendert {
            break;
        }
    }

    Ableitung { je, runden, verbreitert, abgebrochen }
}

/// **The set an elaborator would WRITE for one function.**
///
/// `pure` when nothing is touched — and that is not a special case but what the empty set
/// says. *A function whose derived set is empty and that carries `effects { pure }` today
/// is the one entry the derivation reproduces exactly.*
pub fn zeile(a: &Abgeleitet) -> String {
    let mit_ort: Vec<&String> = a
        .wirkungen
        .iter()
        .filter(|w| *w != "pure" && *w != "diverges")
        .collect();
    if mit_ort.is_empty() {
        return "effects { pure }".to_string();
    }
    format!(
        "effects {{ {} }}",
        mit_ort.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
    )
}

/// One line of prose per hop, for `gabbro effects --ursprung`.
pub fn weg_text(w: &Weg) -> String {
    match w {
        Weg::Rumpf(_) => "the body does it here".to_string(),
        Weg::Ueber { gerufener, innen } => {
            format!("across the call to `{gerufener}`, where it reads `{innen}`")
        }
        Weg::Vertrag { traeger, innen } => format!(
            "from the contract the compiler itself supplies for `{traeger}` (`{innen}`) \
             -- a device transition, a generated table op or a device handle"
        ),
        Weg::Rand { gerufener, innen } => format!(
            "at the edge: `{gerufener}` has no body, its declaration says `{innen}` \
             -- TRUST SURFACE"
        ),
        Weg::Zeiger { ort, innen } => format!(
            "across the indirect call at `{ort}`, from the contract at the pointer type \
             (`{innen}`)"
        ),
        Weg::Verbreitert { von } => {
            format!("WIDENED from `{von}` -- deeper than {TIEFE_MAX} steps")
        }
    }
}
