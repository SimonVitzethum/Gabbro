//! **Start exclusivity -- TRANSFER of `StartExklusiv` into the checker.**
//!
//! The goal theorem over the repaired call machine G (`ziel_ort_geraet`,
//! `ZielOrtGeraet.lean`) takes `hex : StartExklusiv init` as a premise:
//! no two threads start in functions holding a common lock by signature
//! (`RufMaschineG.lean`, `startSpur`: a thread starts the way a callee is
//! entered -- with `requires Held(L)` met). The audit (`AuditZiel.lean`,
//! probe B) shows what it means in practice: for the usual constant thread
//! assignment it collapses to "a thread ENTRY function holds no lock by
//! signature", because nobody holds a lock for a thread before it starts --
//! and two threads running the same lock-holding routine never satisfy it
//! (counter-lemma `audit_same_lock_start_excluded`).
//!
//! What the checker knows about thread starts: there is no `spawn` syntax --
//! threads are table rows, entries dispatch into ordinary `fn`s (lane 120).
//! The starts are the `concurrent { … }` members (bodies that may run
//! together) and the `entry`/`boot` dispatch roots (the closed-world thread
//! entries, same pool `nebeneinander.rs` reads). The signature-held locks of
//! a start function are its `requires Held(L)` witnesses, read flat over the
//! predicate tree (`aufrufgraph::held_aus_pred`).
//!
//! The rule (`N240`): the start functions of distinct thread starts have
//! disjoint signature-held lock sets. A lock both starts require -- unless
//! both sides require it `shared` -- falls once per function pair and lock,
//! naming both starts, both functions and the lock.
//!
//! ## What this pass does NOT do
//!
//! * `shared` + `shared` is allowed: a shared lock exists to be co-held, and
//!   `H005` already tells the strengths apart. `exclusive` against anything
//!   falls -- an exclusive holder excludes every other holder, and G's
//!   `exklusivG` (two threads never hold one lock) is exactly that.
//! * Unresolvable starts are skipped, not cleared: a `concurrent` member that
//!   resolves to nothing is already refused (`W003`), a dangling `dispatch`
//!   likewise (`N018`). A second refusal here would pin the same defect twice.
//! * `entrust` roots are skipped: the guest's contract is unknown (same open
//!   question `nebeneinander.rs` books for writes).
//! * Lock identity is the SHORT name (`a::b::L` and `L` are one lock), the
//!   same convention the pair check in `nebeneinander.rs` uses.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{BTreeMap, BTreeSet};

/// Short lock name: `requires Held(a::b::L)` and `requires Held(L)` name one lock.
fn kurz(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// One thread start the checker can see: its function (graph key), where it
/// was declared, and what to call it in the refusal.
struct Start {
    funktion: String,
    span: gabbro_syntax::span::Span,
    quelle: String,
}

/// The signature-held locks of every function: `(short lock, shared?)` per
/// `requires Held(L)` / `requires Held(L, shared)`, flat over the tree.
fn gehalten(baum: &Programm) -> BTreeMap<String, Vec<(String, bool)>> {
    let mut aus: BTreeMap<String, Vec<(String, bool)>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            let mut v = Vec::new();
            for p in &f.requires {
                let mut h = Vec::new();
                crate::aufrufgraph::held_aus_pred(p, &mut h);
                for (sperre, geteilt) in h {
                    v.push((kurz(&sperre).to_string(), geteilt));
                }
            }
            aus.insert(crate::umgebung::qualifiziere(modul, &f.name.text), v);
        }
    });
    aus
}

/// Every thread start: `concurrent` members first, then `entry` roots, then
/// `boot` dispatch -- one pool, because one boot assignment starts them all.
fn startet(baum: &Programm, g: &crate::aufrufgraph::Graph) -> Vec<Start> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            for pfad in &c.koerper {
                let span = pfad
                    .teile
                    .last()
                    .map(|i| i.span)
                    .unwrap_or(item.span);
                if let Some(k) = g.aufloesen(&u, modul, &pfad.text()) {
                    aus.push(Start {
                        funktion: k,
                        span,
                        quelle: format!("concurrent member `{}`", pfad.text()),
                    });
                }
            }
        }
    });
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) {
            aus.push(Start {
                funktion: voll,
                span: k.span,
                quelle: format!("entry `{}`", k.name),
            });
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Boot(b) = &item.art {
            if let Some(voll) = g.aufloesen(&u, modul, &b.dispatch.text()) {
                aus.push(Start {
                    funktion: voll,
                    span: item.span,
                    quelle: format!("boot `{}`", b.name.text),
                });
            }
        }
    });
    aus
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let gehalten = gehalten(baum);
    let startet = startet(baum, &g);
    let leer: Vec<(String, bool)> = Vec::new();
    // One refusal per (function pair, lock): the same pair is reachable as
    // entries and as a declared set, and must not fall twice.
    let mut gefallen: BTreeSet<(String, String, String)> = BTreeSet::new();
    for i in 0..startet.len() {
        for j in (i + 1)..startet.len() {
            let (fa, fb) = (&startet[i].funktion, &startet[j].funktion);
            let ha = gehalten.get(fa).unwrap_or(&leer);
            let hb = gehalten.get(fb).unwrap_or(&leer);
            for (la, ta) in ha {
                for (lb, tb) in hb {
                    if la != lb || (*ta && *tb) {
                        continue;
                    }
                    let paar = if fa <= fb {
                        (fa.clone(), fb.clone(), la.clone())
                    } else {
                        (fb.clone(), fa.clone(), la.clone())
                    };
                    if !gefallen.insert(paar) {
                        continue;
                    }
                    absagen.schiebe(
                        Absage::fehler(
                            "N240",
                            startet[j].span,
                            format!(
                                "thread starts {} and {} share a signature-held lock: \
                                 `{}` requires Held({la}) and `{}` requires Held({la}) -- \
                                 two threads never start holding one lock",
                                startet[i].quelle, startet[j].quelle, fa, fb
                            ),
                        )
                        .mit_notiz(
                            "the model premise is `StartExklusiv` (`RufMaschineG.lean`): \
                             no two threads start in functions holding a common lock by \
                             signature, consumed by `exklusivG` on the way to \
                             `ziel_ort_geraet`",
                        )
                        .mit_notiz(
                            "in the usual shape a thread ENTRY function holds no lock by \
                             signature -- take the lock inside (`locks L { … }`) instead \
                             of requiring it, or give the two starts disjoint locks",
                        ),
                    );
                }
            }
        }
    }
}
