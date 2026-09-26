//! **The hosted thread start `start { f, g };` as a checker rule** (fix lane F4,
//! review G12 F2/F3, 2026-09-22).
//!
//! Lane 253 parsed the statement and resolved its names (`W003`), and nothing else: the
//! checker accepted it, and only the emitter (`C001`) and the exporter (`LG004`) stopped a
//! program that used it. This pass holds the statement's SHAPE; the other halves stand
//! where their data lives:
//!
//! | code | rule | where |
//! |---|---|---|
//! | `N458` | every root is an `impl fn` with a body, no parameters, no result and no signature-held lock | here |
//! | `N459` | no root twice in one statement (`start { h, h }`) | here |
//! | `N460` | no root the runtime starts already: a `concurrent` member, an `entry` root, a `boot` dispatch | here |
//! | `N461` | no `start` while the starter holds something: inside `locks`, `observes`, `breaking`, or under `requires Held` | here |
//! | `N462` | every started root is pool-safe: each carrier its graph touches that anyone writes is guarded, atomic or per-core | `fusswache2.rs` (`startfaeden`) |
//! | -- | the roots are edges of the call graph: effects, locks and incompleteness reach the starter (`E008`, `E009`) | `aufrufgraph.rs` |
//! | -- | the statement costs the sum of the roots' declared costs plus two primitives per root | `kosten.rs` |
//!
//! **The ownership rule (review G12 F3).** Boot starts every `concurrent` member
//! (`lean_g::check_starts`, the generated driver), so a member that a `start` names
//! would run twice -- once from the declaration, once from the statement. A thread is
//! therefore started by EXACTLY ONE of the two: a `concurrent` member (and an
//! `entry`/`boot` root) by the runtime, a `start` root by the statement, never both
//! (`N460`). The started roots are no `concurrent` members, so the declared-pair race
//! component (`N300`/`N301`, `W001`) never pairs them; what makes them race-free instead
//! is `N462`, the fail-safe shape `N457` gives a `child` path: a started root runs beside
//! the other roots of its statement, beside every declared start and beside other
//! instances of itself (a `start` in a loop, in two starters, in a pool routine), and it
//! may touch a carrier somebody writes only under a lock, atomically or per core.
//!
//! **Why no held lock at the statement (`N461`).** The starter joins the roots before it
//! proceeds. A root that takes a lock the starter holds waits for the starter, which
//! waits for the root: a deadlock no lock order sees, because the two acquisitions stand
//! in two threads. The rule is conservative -- ANY held lock refuses, not only a lock
//! some root takes -- and it mirrors `N456` for the `child` path. `observes` and
//! `breaking` fall with it: an RCU read section held across a join blocks every writer's
//! grace period behind the roots, and an invariant the starter's `breaking` suspends is
//! not the roots' to rely on.
//!
//! ## What this pass does NOT do
//!
//! * No lowering: `C001` stays the emitter's answer. Nothing here makes a `start`
//!   program reach C.
//! * The model is elsewhere (Opus agent A, 2026-09-26, OFFEN O22): the exporter carries
//!   the roots as `gE.gestartet` (`lean_g::check_gestartet`), the goal theorem runs over
//!   the thread machine (`FadenMaschine.lean`: `start` spawns, `join` ends the wait), and
//!   the Lean checker Bool judges each root as a pool routine -- `N458`'s lock half is
//!   `wurzelnB`, `N462` is `einzelnPoolB`, `N461` the side condition of the `start` step.
//! * No liveness: a root that never returns keeps its starter waiting forever. That is
//!   a progress question (`FortschrittG` has no statement-level start either), not a
//!   safety one.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// One `start` statement with the holding context it stands in.
struct Fund {
    starter: String,
    modul: String,
    st: StartStmt,
    kontext: Option<String>,
}

/// Every `start` of a body with its innermost holding context (`N461`).
///
/// The walk is `clone::kontextpfade`'s: a `locks`, `observes` or `breaking` block sets the
/// context for everything below it; every other statement passes it through
/// `crate::unterbloecke`, which is exhaustive over `StmtArt`. A `child` region starts with
/// an EMPTY context -- `N456` already refuses a child inside a holding context, so the
/// child holds nothing of the parent.
fn sammle(
    starter: &str,
    modul: &str,
    b: &Block,
    kontext: Option<&str>,
    aus: &mut Vec<Fund>,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Start(st) => aus.push(Fund {
                starter: starter.to_string(),
                modul: modul.to_string(),
                st: st.clone(),
                kontext: kontext.map(str::to_string),
            }),
            StmtArt::Child(region) => sammle(starter, modul, region, None, aus),
            StmtArt::Sperrt(l) => {
                let k = format!("`locks {}`", l.sperre.text());
                sammle(starter, modul, &l.rumpf, Some(&k), aus);
            }
            StmtArt::Observiert(o) => {
                let k = format!("`observes {}`", o.domaene.text);
                sammle(starter, modul, &o.rumpf, Some(&k), aus);
            }
            StmtArt::Bricht(x) => {
                let namen: Vec<String> = x.invarianten.iter().map(|i| i.text.clone()).collect();
                let k = format!("`breaking {}`", namen.join(", "));
                sammle(starter, modul, &x.rumpf, Some(&k), aus);
            }
            _ => {
                for k in crate::unterbloecke(s) {
                    sammle(starter, modul, k, kontext, aus);
                }
            }
        }
    }
}

/// Every `start` statement of the unit, in source order -- for the passes that read the
/// started roots (`fusswache2::startfaeden`). `(starter module, root path, root span)`.
pub fn wurzeln(baum: &Programm) -> Vec<(String, String, Span)> {
    let mut funde = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                sammle(&f.name.text, modul, b, None, &mut funde);
            }
        }
    });
    let mut aus = Vec::new();
    for fd in funde {
        for w in &fd.st.roots {
            let span = w.teile.last().map(|i| i.span).unwrap_or(fd.st.span);
            aus.push((fd.modul.clone(), w.text(), span));
        }
    }
    aus
}

fn melde(code: &'static str, span: Span, text: String, notiz: &str, absagen: &mut Absagen) {
    absagen.schiebe(Absage::fehler(code, span, text).mit_notiz(notiz));
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // The statements first: a unit without one owes nothing here.
    let mut funde: Vec<Fund> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                // A signature-held lock is held at every statement of the body.
                let mut sig: Vec<String> = Vec::new();
                for p in &f.requires {
                    let mut h = Vec::new();
                    crate::aufrufgraph::held_aus_pred(p, &mut h);
                    for (n, _) in h {
                        if !sig.contains(&n) {
                            sig.push(n);
                        }
                    }
                }
                let start = if sig.is_empty() {
                    None
                } else {
                    Some(format!("`requires Held({})` of `{}`", sig.join(", "), f.name.text))
                };
                sammle(&f.name.text, modul, b, start.as_deref(), &mut funde);
            }
        }
    });
    if funde.is_empty() {
        return;
    }
    let mut funktionen: BTreeMap<String, FnDecl> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            funktionen.insert(crate::umgebung::qualifiziere(modul, &f.name.text), f.clone());
        }
    });
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);

    // The roots the runtime starts: `concurrent` members, `entry` roots, `boot` dispatch.
    let mut laufzeit: BTreeMap<String, String> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Concurrent(c) => {
            for pfad in &c.koerper {
                if let Some(k) = g.aufloesen(&u, modul, &pfad.text()) {
                    laufzeit
                        .entry(k)
                        .or_insert_with(|| format!("a `concurrent` member (`{}`)", pfad.text()));
                }
            }
        }
        ItemArt::Boot(b) => {
            if let Some(k) = g.aufloesen(&u, modul, &b.dispatch.text()) {
                laufzeit
                    .entry(k)
                    .or_insert_with(|| format!("the `boot` dispatch of `{}`", b.name.text));
            }
        }
        _ => {}
    });
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) {
            laufzeit
                .entry(voll)
                .or_insert_with(|| format!("the root of `entry {}`", k.name));
        }
    }

    for fd in &funde {
        // **`N461` -- the one issuance site: a start under a holding context.**
        if let Some(k) = &fd.kontext {
            melde(
                "N461",
                fd.st.span,
                format!(
                    "`{}` starts threads inside {k} -- the starter waits for its roots \
                     while it holds this, and a root that needs it waits for the starter",
                    fd.starter
                ),
                "the starter joins every root before it proceeds, so whatever it holds \
                 across the `start` is held against the roots: a lock one of them takes \
                 is a deadlock no lock order sees (the two acquisitions stand in two \
                 threads) -- start the roots outside every `locks`/`observes`/`breaking` \
                 block and in a function that holds no lock by signature",
                absagen,
            );
        }
        let mut gesehen: BTreeSet<String> = BTreeSet::new();
        for w in &fd.st.roots {
            let span = w.teile.last().map(|i| i.span).unwrap_or(fd.st.span);
            let pfad = w.text();
            // Unresolvable: `W003` (nebeneinander.rs) owns it.
            let Some(k) = g.aufloesen(&u, &fd.modul, &pfad) else {
                continue;
            };
            // **`N459` -- the one issuance site: a root twice in one statement.**
            if !gesehen.insert(k.clone()) {
                melde(
                    "N459",
                    span,
                    format!(
                        "`start` names `{pfad}` twice -- one statement starts each root once"
                    ),
                    "a root named twice would be two threads running one routine, and \
                     the statement has no pool form: the symmetric pool is the \
                     `concurrent` declaration's (`PoolSicher`, open item O18) -- name \
                     each root once",
                    absagen,
                );
                continue;
            }
            // **`N460` -- the one issuance site: a root the runtime starts already.**
            if let Some(wer) = laufzeit.get(&k) {
                melde(
                    "N460",
                    span,
                    format!(
                        "`start` names `{pfad}`, which is {wer} -- the runtime starts it \
                         already, and the statement would run it a second time"
                    ),
                    "a thread has exactly one owner: the runtime starts every \
                     `concurrent` member, `entry` root and `boot` dispatch at boot, the \
                     statement starts its own roots -- drop the root from the \
                     declaration, or drop it from the statement",
                    absagen,
                );
            }
            // **`N458` -- the one issuance site: a root that is not a thread root.**
            let grund = match funktionen.get(&k) {
                None => Some("it is no function of this unit".to_string()),
                Some(f) => {
                    let mut gruende: Vec<String> = Vec::new();
                    if !matches!(f.klasse, None | Some(FnKlasse::Impl))
                        || !matches!(f.rumpf, FnRumpf::Block(_))
                    {
                        gruende.push("it has no checked body (an `impl fn` with a block)".into());
                    }
                    if !f.parameter.is_empty() {
                        gruende.push(format!("it takes {} parameter(s)", f.parameter.len()));
                    }
                    if f.ergebnis.is_some() {
                        gruende.push("it declares a result".into());
                    }
                    let mut h = Vec::new();
                    for p in &f.requires {
                        crate::aufrufgraph::held_aus_pred(p, &mut h);
                    }
                    if !h.is_empty() {
                        let namen: Vec<String> = h.into_iter().map(|(n, _)| n).collect();
                        gruende.push(format!("it requires `Held({})`", namen.join(", ")));
                    }
                    if gruende.is_empty() {
                        None
                    } else {
                        Some(gruende.join(", and "))
                    }
                }
            };
            if let Some(grund) = grund {
                melde(
                    "N458",
                    span,
                    format!("`start` names `{pfad}`, which is no thread root: {grund}"),
                    "a started root is an `impl fn` with a body, no parameters, no result \
                     and no signature-held lock -- the thread passes it nothing, the join \
                     receives nothing, and nobody holds a lock for a thread before it \
                     starts",
                    absagen,
                );
            }
        }
    }
}
