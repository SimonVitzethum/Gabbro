//! **Declared concurrency -- pairwise non-interference from transitive hulls.**
//!
//! The language names no second body by itself: threads are table rows, entries
//! dispatch into ordinary `fn`s, and which BODIES may run at the same time was
//! therefore unnameable (`messung/NEBENLAEUFIGKEIT-ENTWURF.md` §1). A `concurrent
//! { f, g };` declaration names them, and this pass checks AUTOMATICALLY, per
//! unordered pair, from the already computed transitive hulls
//! (`Graph::huelle`, `Huelle.wirkungen`):
//!
//! * `writes(hull f) ∩ writes(hull g) = ∅` -- shared READS may overlap freely;
//! * shared writes overlap only if some lock `L` stands in BOTH hulls' `locks`
//!   effects (HB comes from `gibt L → nimmt L`; exclusion itself stays W3);
//! * `publishes` payload places are exempt (HB via pairing, `V001`–`V007` already
//!   checked); `atomic` globals are exempt (machine orders, A10);
//! * same-TABLE writes from two declared-concurrent bodies fall unless lock-shared
//!   (interim rule over open question 4: row-level disjointness needs index
//!   analysis this checker lacks -- one corpus table, three bodies, all
//!   lock-shared, so the interim stands).
//!
//! Closed world: two context roots (`entry`/`boot` dispatch) whose hulls overlap
//! in writes and share no `concurrent` set fall (`W002`) -- non-declared pairs
//! are NOT concurrent, so nothing is fail-open. Fail-closed: a declared member
//! whose hull is incomplete, or that resolves to nothing, refuses (`W003`).
//! A `start { f, g };` root that resolves to nothing refuses the same way
//! (`W003`, lane 253) -- the statement names declared roots, never fresh paths.
//!
//! ## What this pass does NOT do
//!
//! * Scheduler fairness/starvation (D8): a set says "may run together", never
//!   "each gets a turn".
//! * Dynamic thread creation: refused by absence -- the corpus needs no spawn.
//! * Held-set analysis (open question 1): a common `locks L` in both hulls counts
//!   as lock-shared even where neither body holds `L` across the access. The
//!   exemption is pair-level, not site-level.
//! * `per cpu` cells are NOT desugared: `writes cpu_zelle` from two bodies falls
//!   unless lock-shared, although the shape is disjoint by core (open question 3,
//!   checker-lane half: desugar to disjoint write sets).
//! * `entrust` roots are SKIPPED, not cleared: the guest's writes are unknown
//!   (open question 2, proof-architecture lane).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// The write places, lock names and published places of a hull.
#[derive(Default)]
struct Bild {
    schreibt: BTreeSet<String>,
    sperren: BTreeSet<String>,
    veroeffentlicht: BTreeSet<String>,
}

/// The write string to its carrier table, where statically known.
///
/// The basis of a `writes` place is either a declared table (`writes Faden.slots`)
/// or a function parameter of table type (`writes f.slots` with
/// `f : ptr<normal, rw> Faeden`). Anything else -- a local, an unknown name -- has
/// no carrier this pass can name, and the exact-string comparison stays the only
/// line for it.
///
/// Identity is the SHORT name: `beispiel::m::Faeden` and `Faeden` are one table.
/// Two different modules declaring the same short table name in ONE unit would
/// read as one carrier here -- the residual risk, and it stands in the sentence
/// instead of in a `_` arm.
fn traeger_von(
    schreibt: &str,
    param: &BTreeMap<String, String>,
    tabellen: &BTreeSet<String>,
) -> Option<String> {
    let basis = schreibt.split(['.', '[']).next().unwrap_or(schreibt);
    if tabellen.contains(basis) {
        return Some(basis.to_string());
    }
    param.get(basis).cloned()
}

/// The table a type expression names, through pointers.
fn tabelle_im_typ(t: &TypExpr) -> Option<String> {
    match t {
        TypExpr::Pfad(p) => p.teile.last().map(|i| i.text.clone()),
        TypExpr::Zeiger(z) => tabelle_im_typ(&z.ziel),
        _ => None,
    }
}

fn bild(h: &crate::aufrufgraph::Huelle) -> Bild {
    let mut b = Bild::default();
    for w in &h.wirkungen {
        if let Some(o) = w.strip_prefix("writes ") {
            b.schreibt.insert(o.to_string());
        } else if let Some(o) = w
            .strip_prefix("locks shared ")
            .or_else(|| w.strip_prefix("locks "))
        {
            // The last segment: `locks a::b::L` and `lock L` are the same lock.
            b.sperren
                .insert(o.rsplit("::").next().unwrap_or(o).to_string());
        } else if let Some(o) = w.strip_prefix("publishes ") {
            b.veroeffentlicht.insert(o.to_string());
        }
    }
    b
}

/// The overlap that survives the exemptions: exact write places and carriers.
fn ueberlappung(
    bf: &Bild,
    bg: &Bild,
    atomar: &BTreeSet<String>,
    param_f: &BTreeMap<String, String>,
    param_g: &BTreeMap<String, String>,
    tabellen: &BTreeSet<String>,
) -> (Vec<String>, Vec<String>) {
    // Pair-level: a lock in BOTH hulls carries every shared write (HB from
    // `gibt L → nimmt L`; the held-set half is open question 1).
    if !bf.sperren.is_disjoint(&bg.sperren) {
        return (Vec::new(), Vec::new());
    }
    let mut orte = Vec::new();
    for o in bf.schreibt.intersection(&bg.schreibt) {
        // `publishes` payload pairs are exempt (HB via pairing, already checked).
        if bf.veroeffentlicht.contains(o) || bg.veroeffentlicht.contains(o) {
            continue;
        }
        // `atomic` globals are exempt (machine orders, A10).
        let basis = o.split(['.', '[']).next().unwrap_or(o);
        let traeger = traeger_von(o, param_f, tabellen);
        if atomar.contains(basis)
            || traeger
                .as_ref()
                .is_some_and(|t| atomar.contains(t.as_str()))
        {
            continue;
        }
        orte.push(o.clone());
    }
    // Table-level (interim rule over open question 4): different rows of one
    // table share the carrier name but not the place. Exact overlaps already
    // reported above are not repeated here.
    let mut tf = BTreeSet::new();
    for o in &bf.schreibt {
        if let Some(t) = traeger_von(o, param_f, tabellen) {
            tf.insert(t);
        }
    }
    let mut tg = BTreeSet::new();
    for o in &bg.schreibt {
        if let Some(t) = traeger_von(o, param_g, tabellen) {
            tg.insert(t);
        }
    }
    let mut tab = Vec::new();
    for t in tf.intersection(&tg) {
        // An exact overlap on this table is already named place by place.
        let genau = orte.iter().any(|o| traeger_von(o, param_f, tabellen).as_ref() == Some(t));
        if !genau {
            tab.push(t.clone());
        }
    }
    (orte, tab)
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);

    // Declared tables, atomic globals, per-function parameter tables.
    let mut tabellen = BTreeSet::new();
    let mut atomar = BTreeSet::new();
    let mut param: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Tabelle(t) => {
            tabellen.insert(t.name.text.clone());
        }
        ItemArt::Atomic(a) => {
            atomar.insert(a.name.text.clone());
        }
        ItemArt::Funktion(f) => {
            let schluessel = crate::umgebung::qualifiziere(modul, &f.name.text);
            let mut p = BTreeMap::new();
            for q in &f.parameter {
                if let Some(t) = tabelle_im_typ(&q.typ) {
                    let kurz = t.rsplit("::").next().unwrap_or(&t).to_string();
                    if tabellen.contains(&kurz) || u.nennt_tabelle(modul, &kurz).is_some() {
                        p.insert(q.name.text.clone(), kurz);
                    }
                }
            }
            param.insert(schluessel, p);
        }
        _ => {}
    });

    // The declared sets, resolved to graph keys. One walk: members need their
    // module, and the refusal needs the declaration span.
    struct Menge {
        glieder: Vec<(String, Span)>,
        span: Span,
    }
    let mut mengen = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            let mut glieder = Vec::new();
            for pfad in &c.koerper {
                let span = pfad
                    .teile
                    .last()
                    .map(|i| i.span)
                    .unwrap_or(item.span);
                match g.aufloesen(&u, modul, &pfad.text()) {
                    Some(k) => glieder.push((k, span)),
                    None => absagen.schiebe(
                        Absage::fehler(
                            "W003",
                            span,
                            format!(
                                "`concurrent` names `{}`, which resolves to no body -- \
                                 without the hull the pair cannot be checked, and an \
                                 unchecked pair is not a declared one",
                                pfad.text()
                            ),
                        )
                        .mit_notiz(
                            "fail-closed: an unresolvable member refuses, it never \
                             passes silently",
                        ),
                    ),
                }
            }
            mengen.push(Menge {
                glieder,
                span: item.span,
            });
        }
    });

    // **Lane 253: every `start` root resolves, fail-closed (`W003`).**
    //
    // A `start { f, g };` names already-declared roots and never a fresh
    // path -- like the `concurrent` members above, an unresolvable root
    // refuses instead of passing silently. What this walk does NOT owe
    // yet: membership in a `concurrent` set, the nullary shape, and the
    // join/effects accounting -- handoff to the next lane, not built here.
    {
        fn collect_starts<'a>(b: &'a Block, aus: &mut Vec<&'a StartStmt>) {
            for s in &b.anweisungen {
                if let StmtArt::Start(st) = &s.art {
                    aus.push(st);
                }
                for k in crate::unterbloecke(s) {
                    collect_starts(k, aus);
                }
            }
        }
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            if let ItemArt::Funktion(f) = &item.art {
                if let FnRumpf::Block(b) = &f.rumpf {
                    let mut starts = Vec::new();
                    collect_starts(b, &mut starts);
                    for st in starts {
                        for pfad in &st.roots {
                            let span = pfad.teile.last().map(|i| i.span).unwrap_or(item.span);
                            if g.aufloesen(&u, modul, &pfad.text()).is_none() {
                                absagen.schiebe(
                                    Absage::fehler(
                                        "W003",
                                        span,
                                        format!(
                                            "`start` names `{}`, which resolves to no body -- \
                                             without the body there is nothing to start, and an \
                                             unstarted name is not a started one",
                                            pfad.text()
                                        ),
                                    )
                                    .mit_notiz(
                                        "fail-closed: an unresolvable root refuses, it never \
                                         passes silently",
                                    ),
                                );
                            }
                        }
                    }
                }
            }
        });
    }

    // Declared pairs, with fail-closed on incomplete hulls.
    let mut deklariert: BTreeSet<(String, String)> = BTreeSet::new();
    for m in &mengen {
        for i in 0..m.glieder.len() {
            for j in (i + 1)..m.glieder.len() {
                let (fa, _) = &m.glieder[i];
                let (fb, _) = &m.glieder[j];
                if fa == fb {
                    continue;
                }
                let paar = if fa < fb {
                    (fa.clone(), fb.clone())
                } else {
                    (fb.clone(), fa.clone())
                };
                if !deklariert.insert(paar.clone()) {
                    continue;
                }
                let ha = g.huelle(&paar.0);
                let hb = g.huelle(&paar.1);
                if ha.unvollstaendig.is_some() || hb.unvollstaendig.is_some() {
                    let grund = ha
                        .unvollstaendig
                        .as_ref()
                        .or(hb.unvollstaendig.as_ref())
                        .cloned()
                        .unwrap_or_default();
                    absagen.schiebe(
                        Absage::fehler(
                            "W003",
                            m.span,
                            format!(
                                "`concurrent` cannot be checked for this pair: {grund} -- \
                                 an incomplete hull is a lower bound, and a lower bound \
                                 that looks disjoint is the shape of a missed race"
                            ),
                        )
                        .mit_notiz(
                            "fail-closed: an incomplete hull refuses, it never passes",
                        ),
                    );
                    continue;
                }
                let ba = bild(&ha);
                let bb = bild(&hb);
                let leere: BTreeMap<String, String> = BTreeMap::new();
                let pa = param.get(&paar.0).unwrap_or(&leere);
                let pb = param.get(&paar.1).unwrap_or(&leere);
                let (orte, tab) = ueberlappung(&ba, &bb, &atomar, pa, pb, &tabellen);
                for o in orte {
                    absagen.schiebe(
                        Absage::fehler(
                            "W001",
                            m.span,
                            format!(
                                "declared-concurrent bodies write `{o}` both -- \
                                 `writes(hull f) ∩ writes(hull g)` must be empty"
                            ),
                        )
                        .mit_notiz(
                            "shared READS may overlap freely; shared WRITES need a lock \
                             in BOTH hulls, a `publishes` pairing, or an `atomic` carrier",
                        ),
                    );
                }
                for t in tab {
                    absagen.schiebe(
                        Absage::fehler(
                            "W001",
                            m.span,
                            format!(
                                "declared-concurrent bodies write table `{t}` both, at \
                                 different places -- row-level disjointness needs index \
                                 analysis this checker lacks, so same-table writes fall \
                                 unless lock-shared"
                            ),
                        )
                        .mit_notiz(
                            "interim rule over open question 4 \
                             (`messung/NEBENLAEUFIGKEIT-ENTWURF.md` §6.4)",
                        ),
                    );
                }
            }
        }
    }

    // Closed world: context roots whose hulls overlap without a shared set.
    let mut wurzeln: Vec<(String, Span)> = Vec::new();
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) {
            wurzeln.push((voll, k.span));
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Boot(b) = &item.art {
            if let Some(voll) = g.aufloesen(&u, modul, &b.dispatch.text()) {
                wurzeln.push((voll, item.span));
            }
        }
    });
    for i in 0..wurzeln.len() {
        for j in (i + 1)..wurzeln.len() {
            let (fa, sa) = &wurzeln[i];
            let (fb, _) = &wurzeln[j];
            if fa == fb {
                continue;
            }
            let paar = if fa < fb {
                (fa.clone(), fb.clone())
            } else {
                (fb.clone(), fa.clone())
            };
            // Declared pairs were already checked above, fail-closed included.
            if deklariert.contains(&paar) {
                continue;
            }
            let ha = g.huelle(&paar.0);
            let hb = g.huelle(&paar.1);
            // Asymmetry, named: on visible overlap the lower bound suffices to
            // refuse (presence, not absence); where nothing is visible the pair
            // stays silent -- the fail-closed half belongs to declared sets.
            let ba = bild(&ha);
            let bb = bild(&hb);
            let leere: BTreeMap<String, String> = BTreeMap::new();
            let pa = param.get(&paar.0).unwrap_or(&leere);
            let pb = param.get(&paar.1).unwrap_or(&leere);
            let (orte, tab) = ueberlappung(&ba, &bb, &atomar, pa, pb, &tabellen);
            for o in orte.into_iter().chain(tab) {
                absagen.schiebe(
                    Absage::fehler(
                        "W002",
                        *sa,
                        format!(
                            "context roots write `{o}` both and share no `concurrent` \
                             set -- non-declared pairs are NOT concurrent, so declare \
                             the pair or separate the writes"
                        ),
                    )
                    .mit_notiz(
                        "closed world: what stands in no `concurrent` set never runs \
                         concurrently -- an overlapping pair outside every set is the \
                         interference no declaration covers",
                    ),
                );
            }
        }
    }
}
