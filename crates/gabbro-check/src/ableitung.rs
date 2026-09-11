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
use gabbro_syntax::diag::{Absage, Absagen};
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

/// **The refused drop: a call/pair edge the derivation cannot resolve (`H021`).**
///
/// Assigned 2026-09-11, verified free (zero hits for `H021` across `crates/`,
/// `beispiele/`, `instrumente/`, `messung/`, `TODO.md`, `DONE.md`, `README.md`).
/// The derivation answers an unresolvable edge with a lower bound (`unvollstaendig`)
/// where `E009` stands beside it as a hint -- and a hint is not a refusal. `H021` is
/// the refusal: a body calling a target with nothing to derive from, or an indirect
/// call whose (place, contract) pair stands outside every checked hull, falls here,
/// once per (caller, target), at the caller's name.
///
/// > **Not wired into `pruefe` yet** -- central assembly (`lib.rs`, `saetze.rs`) is
/// > frozen for this lane. `pass` below is the refusal, ready to wire; `messung/
/// > ABLEITUNG-WEG.md` carries the investigation, the probes, and the wiring note.
pub const H021: &str = "H021";

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

/// **The no-body bookkeeping `leite_ab` and `fehlende_kanten` share.**
///
/// One reader, not two: the sets below answer *"what stands at the edge of the checked
/// world"* for the fixpoint (which walks around the edge) and for the refusal (which
/// names it). Two readers for one classification is the `W7` class this tree is written
/// against -- so the walk stands here, once.
struct Kantenbuch {
    /// Functions without a body: `extern`, `prim`, a sealed `asm` hull, a `spec fn`
    /// with a `= pred` body -- plus every graph node that is no `fn` item at all.
    ohne_rumpf: BTreeSet<String>,
    /// The graph-only subset of `ohne_rumpf`: device transitions, device handles,
    /// generated table ops, conversion words. Compiler-supplied, not user-written.
    vertraglich: BTreeSet<String>,
    /// The silent subset: no body AND no declared `effects` anywhere. Nothing to
    /// derive from -- the edge is dropped, and only a lower bound is recorded.
    stumm: BTreeMap<String, String>,
    /// Every `fn` item's name span, by key -- where a refusal about one of its edges
    /// stands (the graph carries no call-site spans; same granularity as `E009`).
    spannen: BTreeMap<String, Span>,
    /// The declared source of every graph-only node, by key -- its `eigen` set as
    /// `Weg::Vertrag` origins. Built here so the fixpoint does not walk the graph
    /// nodes a second time for the same entries.
    vertrag_eigen: BTreeMap<String, BTreeMap<String, Weg>>,
}

fn erhebe_kantenbuch(baum: &Programm, g: &crate::aufrufgraph::Graph) -> Kantenbuch {
    let mut buch = Kantenbuch {
        ohne_rumpf: Default::default(),
        vertraglich: Default::default(),
        stumm: Default::default(),
        spannen: Default::default(),
        vertrag_eigen: Default::default(),
    };
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let key = crate::umgebung::qualifiziere(modul, &f.name.text);
        buch.spannen.insert(key.clone(), f.name.span);
        // **No body — the declaration IS the source, and it stays one.** A `spec fn`
        // with a `= pred` body computes nothing at runtime; an `asm` hull is a sealed
        // hole; an `extern fn` is another unit's promise. All three are the edge of the
        // checked world.
        if !matches!(f.rumpf, FnRumpf::Block(_)) {
            buch.ohne_rumpf.insert(key.clone());
            if f.effects.is_none() {
                buch.stumm.insert(key.clone(), format!("`{key}` declares no `effects`"));
            }
        }
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
        if buch.spannen.contains_key(key) {
            continue;
        }
        buch.ohne_rumpf.insert(key.clone());
        buch.vertraglich.insert(key.clone());
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
            buch.stumm.insert(key.clone(), format!("`{key}` declares no `effects`"));
        }
        buch.vertrag_eigen.insert(key.clone(), m);
    }
    buch
}

/// **Derive the effects of every function in a unit.** `weit` as in
/// `wirkungen::rumpfwirkungen_mit`: with it, reads through parameters count too — and an
/// elaborator that WRITES the line has to write those, because the caller wants to see what
/// happens to his pointer.
pub fn leite_ab(baum: &Programm, weit: bool) -> Ableitung {
    let g = crate::aufrufgraph::erhebe(baum);
    let (konstanten, weltnamen) = crate::wirkungen::welt_und_konstanten(baum);
    let buch = erhebe_kantenbuch(baum, &g);

    // **What each body does by itself** — and for a function without one, what it declares.
    let mut eigen: BTreeMap<String, BTreeMap<String, Weg>> = Default::default();
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
            // **No body — the declaration IS the source, and it stays one**; see
            // `erhebe_kantenbuch` for why these three are the edge of the checked world.
            _ => {
                if let Some(w) = &f.effects {
                    for e in &w.liste {
                        m.insert(e.art.text(), Weg::Rumpf(e.span));
                    }
                }
            }
        }
        eigen.insert(key, m);
    });
    eigen.extend(buch.vertrag_eigen.iter().map(|(k, m)| (k.clone(), m.clone())));

    let ohne_rumpf = &buch.ohne_rumpf;
    let vertraglich = &buch.vertraglich;
    let stumm = &buch.stumm;

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

// =======================================================================================
// «H021» -- THE REFUSED DROP
// =======================================================================================

/// **Why a dropped edge falls.** Three shapes, one code -- and the fourth shape that
/// deliberately does not:
/// * `Unbekannt`: the target resolves to no key at all -- not an `fn` item, not a graph
///   node. The fixpoint drops the edge with *"`ziel` is unknown to the graph"*.
/// * `Stumm`: the target stands at the edge but declares nothing -- no body anywhere
///   and no `effects` clause to derive from. The fixpoint drops the edge with
///   *"`ziel` declares no `effects`"*. An `extern`/`prim`/`spec`/`asm` WITH declared
///   effects is the trust surface (`Weg::Rand`) and stays silent -- *this one declares
///   nothing, so there is no surface, only a hole.*
/// * `OhneVertrag`: an indirect call through a place whose type carries no `effects`
///   contract. The (place, contract) pair stands outside every checked hull -- there
///   is no callee key to descend into and no promise to fold in.
/// * NOT here: an argument that is not a place (`unklar` in `ersetze`). That shape is
///   `E009`'s legitimate third state -- a bridge that cannot be built is not a target
///   that does not exist, and refusing it as `H021` would re-run lane 103 (`H019`,
///   withdrawn at integration: it fired on member/predicate shapes that were never
///   frame-bound). *A refusal that cannot tell those apart is a wider net, not a
///   stronger rule.*
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kantengrund {
    Unbekannt,
    Stumm,
    OhneVertrag,
}

/// **One dropped edge, named at both ends.**
#[derive(Debug, Clone)]
pub struct FehlendeKante {
    /// The caller -- a function WITH a body. A function without one has no edges.
    pub funktion: String,
    /// The unreachable end: the callee key, or the place of an indirect call.
    pub ziel: String,
    pub grund: Kantengrund,
    /// The caller's name span -- the graph carries no call-site spans, so this is the
    /// same granularity `E009` stands at.
    pub span: Span,
}

/// **Every dropped edge of a unit, one entry per (caller, target, reason).**
///
/// This walks the same edges the fixpoint walks (`rufe` with arguments, `ruft` without,
/// `indirect` through places) and keeps exactly the ones the fixpoint drops without a
/// resolvable end: unknown targets, silent (`stumm`) targets, contract-less indirect
/// calls. Everything with a source -- bodies (`Ueber`), declarations at the edge
/// (`Rand`), compiler-supplied entries (`Vertrag`), pointer contracts (`Zeiger`) --
/// stays silent, as does the imprecise bridge (non-place arguments).
pub fn fehlende_kanten(baum: &Programm) -> Vec<FehlendeKante> {
    let g = crate::aufrufgraph::erhebe(baum);
    let buch = erhebe_kantenbuch(baum, &g);
    let bekannt: BTreeSet<String> =
        buch.spannen.keys().cloned().chain(g.knoten.keys().cloned()).collect();
    let mut aus = Vec::new();
    let mut gesehen: BTreeSet<(String, String, Kantengrund)> = Default::default();
    // The keys are walked in a fixed order so that two runs over the same tree give the
    // same refusals in the same order -- same reason as in the fixpoint below.
    let mut namen: Vec<String> = bekannt.iter().cloned().collect();
    namen.sort();
    for name in &namen {
        // A function without a body inherits nothing because it HAS no edges -- and a
        // graph-only node neither: both are the edge, never the caller.
        if buch.ohne_rumpf.contains(name) {
            continue;
        }
        let Some(k) = g.knoten.get(name) else { continue };
        let Some(span) = buch.spannen.get(name) else { continue };
        let mut lege = |ziel: &str, grund: Kantengrund| {
            if gesehen.insert((name.clone(), ziel.to_string(), grund)) {
                aus.push(FehlendeKante {
                    funktion: name.clone(),
                    ziel: ziel.to_string(),
                    grund,
                    span: *span,
                });
            }
        };
        for (ziel, _) in &k.rufe {
            if !bekannt.contains(ziel) {
                lege(ziel, Kantengrund::Unbekannt);
            } else if buch.stumm.contains_key(ziel) {
                lege(ziel, Kantengrund::Stumm);
            }
        }
        // Edges without argument knowledge (`transition`): same resolution question,
        // asked without the bridge.
        for ziel in k.ruft.iter().filter(|z| !k.rufe.iter().any(|(t, _)| &t == z)) {
            if !bekannt.contains(ziel) {
                lege(ziel, Kantengrund::Unbekannt);
            } else if buch.stumm.contains_key(ziel) {
                lege(ziel, Kantengrund::Stumm);
            }
        }
        // **The indirect calls.** With a contract the pointer type is the source
        // (`Zeiger`) and the edge resolves; without one the (place, contract) pair
        // stands outside every checked hull.
        for i in &k.indirect {
            if !i.has_contract {
                lege(&i.place, Kantengrund::OhneVertrag);
            }
        }
    }
    aus
}

/// **The refusal over one unit: every dropped edge falls once, at the caller.**
///
/// One refusal per (caller, target, reason), never per site -- the edge was dropped
/// once, so it falls once (same decision as `H014`/`H016`/`H017`).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    for kante in fehlende_kanten(baum) {
        let (text, erster, zweiter) = match kante.grund {
            Kantengrund::Unbekannt => (
                format!(
                    "`{}` calls `{}`, and `{}` is unknown to the graph -- the edge \
                     carries nothing across",
                    kante.funktion, kante.ziel, kante.ziel
                ),
                "the derivation drops the edge and records a lower bound instead -- \
                 and a lower bound is not an answer"
                    .to_string(),
                "compare `E009`: a hint where the target is merely imprecise -- here \
                 there is no target at all"
                    .to_string(),
            ),
            Kantengrund::Stumm => (
                format!(
                    "`{}` calls `{}`, and `{}` has no body and declares no `effects` \
                     -- there is nothing to derive from",
                    kante.funktion, kante.ziel, kante.ziel
                ),
                "an `extern`/`prim`/`spec`/`asm` WITH declared `effects` is the edge of \
                 the checked world and stays silent -- this one declares nothing, so \
                 there is no trust surface, only a hole"
                    .to_string(),
                "today the caller is only marked incomplete (`unvollstaendig`), and an \
                 `E009` hint is all that names it"
                    .to_string(),
            ),
            Kantengrund::OhneVertrag => (
                format!(
                    "`{}` calls through `{}`, and no `effects` contract stands at the \
                     pointer type -- the pair stands outside every checked hull",
                    kante.funktion, kante.ziel
                ),
                "the contract at the `fn(...)` type is the source where the callee has \
                 no name (see `beispiele/49`); without it there is neither a key to \
                 descend into nor a promise to fold in"
                    .to_string(),
                "today the caller is only marked incomplete (`unvollstaendig`), and an \
                 `E009` hint is all that names it"
                    .to_string(),
            ),
        };
        absagen.schiebe(
            Absage::fehler(H021, kante.span, text).mit_notiz(erster).mit_notiz(zweiter),
        );
    }
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

#[cfg(test)]
mod tests {
    //! **The refusal proves first that it can tell its shapes apart.**
    //!
    //! The twin rule from `tests/ableitung.rs` (R14) holds here too, in both halves:
    //! (a) every must-fall shape below would pass SILENTLY at `Fehler` level without
    //! `H021` -- an `E009` hint at most -- and (b) every silence below is load-bearing:
    //! each twin removes exactly one property of the falling shape, so a refusal that
    //! stopped refusing would turn the twin red instead of green. *A probe that cannot
    //! turn red measures nothing.*
    //!
    //! These run against `leite_ab`/`fehlende_kanten`/`pass` directly -- the refusal is
    //! not wired into `pruefe` (central assembly frozen for this lane), so the suite
    //! level cannot carry them yet. `messung/ABLEITUNG-WEG.md` says where the wire goes.

    use super::*;

    fn kanten(q: &str) -> Vec<FehlendeKante> {
        fehlende_kanten(&gabbro_syntax::lies("probe.gab", q).0)
    }

    fn fehler(q: &str) -> Vec<String> {
        let (baum, _) = gabbro_syntax::lies("probe.gab", q);
        let mut absagen = Absagen::neu("probe.gab");
        pass(&baum, &mut absagen);
        absagen.absagen.iter().map(|a| a.code.to_string()).collect()
    }

    /// **Must fall: a body calling a target with no body and no `effects`.**
    ///
    /// `stumm` declares nothing, so the derivation drops the edge into a lower bound
    /// (`unvollstaendig`) and no `Fehler` names the call. `H021` names it -- once, at
    /// the caller, with the reason.
    #[test]
    fn stummes_ziel_faellt_einmal_am_rufer() {
        let q = "module t {
static mut W : u32 = 0;
extern fn stumm() costs <= 2 ops;
impl fn rufer() effects { pure } costs <= 8 ops { stumm(); }
}";
        let ks = kanten(q);
        assert_eq!(ks.len(), 1, "{ks:?}");
        assert_eq!(ks[0].funktion, "t::rufer");
        assert_eq!(ks[0].ziel, "t::stumm");
        assert_eq!(ks[0].grund, Kantengrund::Stumm);
        // The refusal and the bookkeeping agree: the caller IS the lower bound the
        // fixpoint records -- the rule refuses the edge the derivation drops.
        let ab = leite_ab(&gabbro_syntax::lies("probe.gab", q).0, true);
        assert!(ab.je["t::rufer"].unvollstaendig.is_some(), "{:?}", ab.je["t::rufer"]);
        assert_eq!(fehler(q), [H021], "falls once, with H021");
    }

    /// **Must pass: the same edge with a declared line is the trust surface.**
    ///
    /// `rand` has no body but declares `effects` -- `Weg::Rand`, silent by design.
    /// This twin removes exactly the falling property (the missing declaration), so a
    /// refusal that fired here would refuse the edge of the checked world itself.
    #[test]
    fn rand_mit_deklaration_bleibt_still() {
        let q = "module t {
static mut W : u32 = 0;
extern fn rand() effects { writes W } costs <= 2 ops;
impl fn rufer() effects { writes W } costs <= 8 ops { rand(); }
}";
        assert!(kanten(q).is_empty(), "{:?}", kanten(q));
        assert!(fehler(q).is_empty(), "the trust surface never draws H021");
        // And the path says `Rand`, not `Ueber` -- the hop the twin is about.
        let ab = leite_ab(&gabbro_syntax::lies("probe.gab", q).0, true);
        let p = ab.pfad("t::rufer", "writes W");
        assert!(matches!(&p[0].2, Weg::Rand { .. }), "{p:?}");
    }

    /// **Must pass: an ordinary body-to-body call resolves.**
    ///
    /// The second twin: nothing missing anywhere, derivation and refusal agree on
    /// silence.
    #[test]
    fn rumpf_zu_rumpf_bleibt_still() {
        let q = "module t {
static mut W : u32 = 0;
impl fn tief() effects { writes W } costs <= 2 ops { W = 1; }
impl fn oben() effects { writes W } costs <= 8 ops { tief(); }
}";
        assert!(kanten(q).is_empty(), "{:?}", kanten(q));
        assert!(fehler(q).is_empty(), "{:?}", fehler(q));
    }

    /// **Boundary: the compiler's own words are no hole.**
    ///
    /// The eight integer conversions stand in the graph with declared `pure`
    /// (`vertraglich`, never `stumm`) -- a call to `u64(x)` resolves. A refusal that
    /// fired here would fall on every cast in the corpus.
    #[test]
    fn umwandlungswort_bleibt_still() {
        let q = "module t {
impl fn wandle(a : u32 in 0 .. 100) -> u64 effects { pure } costs <= 4 ops { return u64(a); }
}";
        assert!(kanten(q).is_empty(), "{:?}", kanten(q));
        assert!(fehler(q).is_empty(), "{:?}", fehler(q));
    }

    /// **Boundary: a target no pass can name is still a dropped edge.**
    ///
    /// Nothing declares `nichts` -- the edge is unknown to the graph. At suite level
    /// the name pass refuses first, so no gift probe can carry this shape; it stands
    /// here so the refusal's answer is on record: unknown is unknown, whoever speaks
    /// first.
    #[test]
    fn unbekanntes_ziel_faellt_als_unbekannt() {
        let q = "module t {
impl fn rufer() effects { pure } costs <= 8 ops { nichts(); }
}";
        let ks = kanten(q);
        assert_eq!(ks.len(), 1, "{ks:?}");
        assert_eq!(ks[0].grund, Kantengrund::Unbekannt);
        assert_eq!(fehler(q), [H021], "{:?}", fehler(q));
    }

    /// **Must fall: an indirect call with no contract at the pointer type.**
    ///
    /// The (place, contract) pair stands outside every checked hull -- no key to
    /// descend into, no promise to fold in. `E009` stays a hint; `H021` refuses.
    #[test]
    fn vertragsloser_zeiger_faellt() {
        let q = "module t {
type T = { f : fn(u8), };
impl fn rufe(t : ptr<normal, r> T) effects { pure } costs <= 8 ops { t->f(1); }
}";
        let ks = kanten(q);
        assert_eq!(ks.len(), 1, "{ks:?}");
        assert_eq!(ks[0].grund, Kantengrund::OhneVertrag);
        assert_eq!(fehler(q), [H021], "{:?}", fehler(q));
    }

    /// **Boundary: the imprecise bridge is `E009`'s, not `H021`'s.**
    ///
    /// `tief` touches its parameter (`writes p.slots` derives param-rooted) and the
    /// caller hands a computed value (`nimm()`, no place) -- `ersetze` cannot build
    /// the bridge (`unklar`). That is a target that EXISTS but cannot be carried
    /// across, not a target that does not exist; refusing it here would re-run lane
    /// 103 (`H019`, withdrawn: member/predicate shapes were never frame-bound). The
    /// rule stays out -- deliberately, and pinned. The `unvollstaendig` assertion is
    /// what keeps this pin from going vacuous: without it, silence could mean the
    /// bridge was never needed.
    #[test]
    fn unklare_bruecke_bleibt_still() {
        let q = "module t {
table K count 64 { slot { wert : u32 in 0 .. 100, } }
extern fn nimm() -> ptr<normal, rw> K effects { pure } costs <= 2 ops;
impl fn tief(p : ptr<normal, rw> K) effects { writes p.slots } costs <= 2 ops { p.slots[0].wert = 0; }
impl fn oben() effects { writes K.slots } costs <= 8 ops { tief(nimm()); }
}";
        let ab = leite_ab(&gabbro_syntax::lies("probe.gab", q).0, true);
        assert!(
            ab.je["t::oben"].unvollstaendig.is_some(),
            "the bridge must actually be needed, or this pin is vacuous: {:?}",
            ab.je["t::oben"]
        );
        assert!(kanten(q).is_empty(), "{:?}", kanten(q));
        assert!(fehler(q).is_empty(), "{:?}", fehler(q));
    }
}
