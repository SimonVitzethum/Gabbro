//! **The flagship's decidable footprint premise as a checker rule (lane 175).**
//!
//! The goal theorem is now `ziel_ort_mehrfaden` (`grammatik/Grammatik/ZielOrtMehrfaden.lean`,
//! SATZKARTE §16.1), and its footprint premise is no longer the old `fussOrtGB` --
//! `E245`-`E249` in `wirkungen.rs` compute that older, stricter check and stay hints.
//! Today the premise is `FussS P S (lokK P K)`:
//!
//! * per started thread the reachable call graph (`K t`, closed under calls --
//!   `AbgK`, computed by `reachB`; `FadenMerkmal.lean`: `AbgK`/`abgB` closure,
//!   `reachB`),
//! * thread-local carriers from each thread's graph (`GetrenntK`, `lokK`, `fussMehrB`):
//!   a carrier is thread-local if no thread reaches it in a footprint while a
//!   DIFFERENT thread may write it,
//! * lock invariants (`SperreFuss.lean`: `fussSperreB`): a non-local footprint carrier
//!   is admitted when a lock held AT THE ACCESS guards it or that lock's invariant
//!   protects it,
//! * lock floors consistent with ranks (`StufenOk`/`StufenM`, `Verklemmung.lean`).
//!
//! Five codes, one per leg:
//!
//! * `N290` -- a contract carrier (`requires`/`ensures`) that is written somewhere,
//!   guarded by no signature lock, protected by no lock invariant, and not thread-local.
//! * `N291` -- a body READ at a site where no held lock (signature or enclosing `locks`
//!   block) guards it, with the same two exemptions. A read inside `locks L { … }`
//!   over a carrier `L` protects is guarded AT THE ACCESS and stays silent -- the shape
//!   probe C of the 2026-09-13 verdict refused under the old check.
//! * `N292` -- a direct callee's contract carrier outside the same admission, at the
//!   call site, naming the callee.
//! * `N293` -- an indirect call whose candidate pool reads outside the caller footprint
//!   with the same admission (the `fussMehrB` leg over the E249 candidate pool).
//! * `N294` -- a lock floor violated against a SIGNATURE-held lock: a `locks L` take or
//!   a call whose hull takes a lock ranking at or below a lock the function holds by
//!   signature. `H006`/`H012` never see signature-held outers (their chain starts empty),
//!   so this leg fires exactly where they stay silent; same-lock pairs are exempt there
//!   as here (the real same-lock take is `H003`'s).
//!
//! Surface mapping, each with its Lean ground:
//!
//! * Started threads are the `concurrent` members plus the `entry`/`boot` dispatch roots
//!   -- the same pool `startexklusiv.rs` reads. With no declared start the unit is
//!   single-threaded (`ziel_ort_einfaden`): one thread whose graph is every function,
//!   hence every carrier is thread-local and the legs stay silent.
//! * Call graphs are reached over `aufrufgraph.rs` (`rufe` keys, already resolved); a
//!   function with indirect calls unions the E249 candidate pool (address-taken functions,
//!   else every function of the unit) -- the surface form of `AbgK` over indirect calls
//!   by signature. The fixpoint is closed by construction over direct edges.
//! * "May write" is DECLARED write permission (`writes`, plus `publishes` and `allocs`
//!   resolved to carriers), exactly what SATZKARTE §16.6 says `GetrenntK` judges -- not
//!   the writes a body performs. "Written by none" reuses the old writer set direction
//!   (declared or performed -- a body write without a declared effect is `E005`'s).
//! * Guards reuse lane 156's lock data (`sperrinv::sperrdaten`: `lock L protects`
//!   resolved to carriers, the `N275` resolution, which the old E245-E249 walk
//!   never did). Lock identity is by short name on both sides.
//! * Invariant protection is `lock L protects { c }` WITH an `invariant` clause --
//!   `S.orte L` on the surface. Holding AT THE ACCESS is `geteilt.rs`'s question (`H007`,
//!   an error); this rule asks the footprint question and stays silent where `H007`
//!   speaks, so a protected carrier read bare draws one refusal, not two.
//! * Device-rooted reads carry no footprint (the E245-E249 boundary); `syscall`/`axiom`
//!   contracts, `maintains` and `= pred ;` bodies are not read (same boundary).
//! * The surface declares no lock floors (`Signatur.boden` defaults to `none`, so
//!   `StufenM` holds by `stufenM_of_ok` over `stufenOk_ohne`); `N294` is the rank half that
//!   remains: the floor of a function is the maximum rank of the locks it holds by
//!   signature, and every take and every callee take ranks strictly above it.
//!
//! Severity is an ERROR: measured over `beispiele/*.gab` the new rule admits every file
//! the old hints flagged on single-threaded drivers (thread-locality) and on lock-held
//! reads (guard at the access), and refuses nothing -- the corpus stays green, and every
//! refusal names a real concurrent defect (see the lane report for the table).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// **ERROR -- see the module head.** The corpus stays green under the new rule, so every
/// refusal is a real concurrent defect and refuses instead of flagging.
const ALS_FEHLER: bool = true;

fn melde(code: &'static str, span: Span, text: String, notizen: &[&str], absagen: &mut Absagen) {
    let mut a = if ALS_FEHLER {
        Absage::fehler(code, span, text)
    } else {
        Absage::hinweis(code, span, text)
    };
    for n in notizen {
        a = a.mit_notiz((*n).to_string());
    }
    absagen.schiebe(a);
}

/// Short name: `a::b::L` and `L` are one lock, the convention `startexklusiv.rs` and
/// `nebeneinander.rs` use.
fn kurz(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// The root of a place: everything before the first `.`, `[` or `-`.
fn wurzel(ort: &str) -> &str {
    crate::wirkungen::carrier_root(ort)
}

/// What the unit declares: carriers, devices, constants.
struct Bestand {
    traeger: BTreeSet<String>,
    geraete: BTreeSet<String>,
    konstanten: BTreeSet<String>,
}

fn bestand(baum: &Programm) -> Bestand {
    let mut b = Bestand {
        traeger: BTreeSet::new(),
        geraete: BTreeSet::new(),
        konstanten: BTreeSet::new(),
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Tabelle(t) => {
            b.traeger.insert(t.name.text.clone());
        }
        ItemArt::Statisch(s) => {
            b.traeger.insert(s.name.text.clone());
        }
        ItemArt::State(s) => {
            b.traeger.insert(s.name.text.clone());
        }
        ItemArt::Device(d) => {
            b.geraete.insert(d.name.text.clone());
        }
        ItemArt::Konst(k) => {
            b.konstanten.insert(k.name.text.clone());
        }
        _ => {}
    });
    b
}

/// A lock: its protected carriers (resolved), its rank, whether it declares an invariant.
struct Sperre {
    schutz: BTreeSet<String>,
    rang: Option<i128>,
    invariante: bool,
}

fn sperren(baum: &Programm, u: &crate::umgebung::Umgebung) -> BTreeMap<String, Sperre> {
    // The protected sets and the invariant presence come from lane 156
    // (`sperrinv.rs`: the `N275` resolution); only the ranks are read here.
    let daten = crate::sperrinv::sperrdaten(baum);
    let mut aus: BTreeMap<String, Sperre> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Lock(l) = &item.art {
            let n = kurz(&l.name.text).to_string();
            aus.insert(
                n.clone(),
                Sperre {
                    schutz: daten.schutz.get(&n).cloned().unwrap_or_default(),
                    rang: u.konst_wert(modul, &l.rang),
                    invariante: daten.invariante.contains(&n),
                },
            );
        }
    });
    aus
}

/// The table a type expression names, through pointers -- the `nebeneinander.rs`
/// resolution, read point for point: a declared table name, or a parameter of table
/// type whose writes land on that table.
fn tabelle_im_typ(t: &TypExpr, tabellen: &BTreeSet<String>) -> Option<String> {
    match t {
        TypExpr::Pfad(p) => p
            .teile
            .last()
            .map(|i| i.text.clone())
            .filter(|n| tabellen.contains(n)),
        TypExpr::Zeiger(z) => tabelle_im_typ(&z.ziel, tabellen),
        _ => None,
    }
}

/// A declared write target resolved to its carrier, if it names one: a carrier root
/// directly, or a parameter whose type names a table.
fn schreibtraeger(
    ort: &str,
    param: &BTreeMap<String, String>,
    tabellen: &BTreeSet<String>,
) -> Option<String> {
    let grund = wurzel(ort).to_string();
    if tabellen.contains(&grund) {
        return Some(grund);
    }
    param.get(&grund).cloned()
}

/// One thread start the checker can see -- the `startexklusiv.rs` pool: `concurrent`
/// members, `entry` roots, `boot` dispatch.
struct Start {
    funktion: String,
    #[allow(dead_code)]
    quelle: String,
}

fn startet(
    baum: &Programm,
    g: &crate::aufrufgraph::Graph,
    u: &crate::umgebung::Umgebung,
) -> Vec<Start> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            for pfad in &c.koerper {
                if let Some(k) = g.aufloesen(u, modul, &pfad.text()) {
                    aus.push(Start {
                        funktion: k,
                        quelle: format!("concurrent member `{}`", pfad.text()),
                    });
                }
            }
        }
    });
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = g.aufloesen(u, &k.modul, &k.wurzel) {
            aus.push(Start {
                funktion: voll,
                quelle: format!("entry `{}`", k.name),
            });
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Boot(b) = &item.art {
            if let Some(voll) = g.aufloesen(u, modul, &b.dispatch.text()) {
                aus.push(Start {
                    funktion: voll,
                    quelle: format!("boot `{}`", b.name.text),
                });
            }
        }
    });
    aus
}

/// The reachable call graph of one started thread: the fixpoint over resolved direct
/// edges, union the indirect-call candidate pool wherever a member calls through a
/// place -- the surface form of `reachB` with `AbgK` over indirect calls by signature.
fn erreichbar(
    start: &str,
    g: &crate::aufrufgraph::Graph,
    kandidaten: &[String],
) -> BTreeSet<String> {
    let mut gesehen = BTreeSet::new();
    let mut stapel = vec![start.to_string()];
    while let Some(s) = stapel.pop() {
        if !gesehen.insert(s.clone()) {
            continue;
        }
        if let Some(k) = g.knoten.get(&s) {
            for (ziel, _) in &k.rufe {
                stapel.push(ziel.clone());
            }
            for alt in k.ruft.iter().filter(|a| !k.rufe.iter().any(|(z, _)| z == *a)) {
                stapel.push(alt.clone());
            }
            if !k.indirect.is_empty() {
                stapel.extend(kandidaten.iter().cloned());
            }
        }
    }
    gesehen
}

/// The E249 candidate pool: the functions behind a pointer where the unit takes
/// addresses, else every function of the unit -- the same pool `wirkungen.rs` reads,
/// because the same unsound-narrowing argument applies.
fn kandidatenpool(
    baum: &Programm,
    funktionen: &BTreeMap<String, FnDecl>,
) -> Vec<String> {
    let mut kurz: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for k in funktionen.keys() {
        let n = k.rsplit("::").next().unwrap_or(k).to_string();
        kurz.entry(n).or_default().push(k.clone());
    }
    let mut genommen = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let bloecke: Vec<&Block> = match &item.art {
            ItemArt::Funktion(f) => match &f.rumpf {
                FnRumpf::Block(b) => vec![b],
                _ => vec![],
            },
            ItemArt::Check(c) => vec![&c.can_fail],
            _ => vec![],
        };
        for b in bloecke {
            let mut stapel = vec![b];
            while let Some(bb) = stapel.pop() {
                for s in &bb.anweisungen {
                    for e in crate::eigene_ausdruecke(s) {
                        for x in crate::alle_ausdruecke(e) {
                            if let ExprArt::FnWert(p) = &x.art {
                                if let Some(letztes) = p.teile.last() {
                                    genommen.insert(letztes.text.clone());
                                }
                            }
                        }
                    }
                    for k in crate::unterbloecke(s) {
                        stapel.push(k);
                    }
                }
            }
        }
    });
    if genommen.is_empty() {
        return funktionen.keys().cloned().collect();
    }
    let mut pool = BTreeSet::new();
    for name in &genommen {
        if let Some(schluessel) = kurz.get(name) {
            pool.extend(schluessel.iter().cloned());
        }
    }
    pool.into_iter().collect()
}

/// Read Orten of one expression, indices included -- the `geteilt.rs` coverage at one
/// site: every `Ort` in the tree plus every index under it, plus traverse/`count`
/// domains, which are reads of their carriers.
fn orte_aus_expr(e: &Expr, aus: &mut Vec<Ort>) {
    match &e.art {
        ExprArt::Ort(o) => {
            aus.push((*o).clone());
            for s in &o.suffixe {
                if let OrtSuffix::Index(ix) = s {
                    orte_aus_expr(ix, aus);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => orte_aus_expr(x, aus),
        ExprArt::Binaer(_, a, b) => {
            orte_aus_expr(a, aus);
            orte_aus_expr(b, aus);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                orte_aus_expr(a, aus);
            }
        }
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                orte_aus_expr(a, aus);
            }
        }
        ExprArt::Eingebaut(g) => match &**g {
            Eingebaut::Aligned(a, b) => {
                orte_aus_expr(a, aus);
                orte_aus_expr(b, aus);
            }
            Eingebaut::Sizeof(x) | Eingebaut::Lenof(x) => {
                if let TypOderOrt::Ort(o) = x {
                    for s in &o.suffixe {
                        if let OrtSuffix::Index(ix) = s {
                            orte_aus_expr(ix, aus);
                        }
                    }
                }
            }
        },
        ExprArt::Zaehle { domaene, rumpf, .. } => {
            domaene_ort(domaene, aus);
            for e in crate::ausdruecke_im_praedikat(rumpf) {
                orte_aus_expr(e, aus);
            }
        }
        _ => {}
    }
}

fn domaene_ort(d: &Domaene, aus: &mut Vec<Ort>) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o)
        | Domaene::KetteIn { ort: o, .. } => {
            aus.push(o.clone());
            for s in &o.suffixe {
                if let OrtSuffix::Index(ix) = s {
                    let mut idx = Vec::new();
                    orte_aus_expr(ix, &mut idx);
                    aus.extend(idx);
                }
            }
        }
        Domaene::FelderVon(_) | Domaene::Threads => {}
    }
}

/// One body-read site: the carrier roots read at this statement level with the span
/// of the read. Index reads count beside the place itself.
fn stand_liest(s: &Stmt, aus: &mut Vec<Ort>) {
    match &s.art {
        StmtArt::Zuweisung(z) => {
            for suf in &z.ziel.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    orte_aus_expr(ix, aus);
                }
            }
            orte_aus_expr(&z.wert, aus);
        }
        StmtArt::Publish(p) => {
            for suf in &p.ziel.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    orte_aus_expr(ix, aus);
                }
            }
            orte_aus_expr(&p.wert, aus);
        }
        StmtArt::Let(l) => orte_aus_expr(&l.wert, aus),
        StmtArt::Alloc(a) => orte_aus_expr(&a.wert, aus),
        StmtArt::Return(Some(x)) => orte_aus_expr(x, aus),
        StmtArt::Ruf(r) => {
            for a in &r.argumente {
                orte_aus_expr(a, aus);
            }
        }
        StmtArt::LibraryCall(r) => {
            for a in &r.args {
                orte_aus_expr(a, aus);
            }
        }
        StmtArt::AwaitLoad(a) => aus.push(a.quelle.clone()),
        StmtArt::Exchange(e) => aus.push(e.ort.clone()),
        StmtArt::Narrow(x) => aus.push(x.ort.clone()),
        StmtArt::Wenn(w) => {
            for (bed, _) in &w.zweige {
                orte_aus_expr(bed, aus);
            }
        }
        StmtArt::Match(m) => orte_aus_expr(&m.gegenstand, aus),
        StmtArt::Schleife(sch) => {
            if let Schleife::Traverse(x) = sch.as_ref() {
                domaene_ort(&x.domaene, aus);
            }
        }
        _ => {}
    }
}

/// The per-site body walk for `N291` and the `N294` take leg: every read site with the
/// locks held there (signature-held plus the enclosing `locks` stack), and every
/// `locks` take with the same held set at the take.
struct Begehung {
    liest: Vec<(String, Span, Vec<String>)>,
    nimmt: Vec<(String, Span, Vec<String>)>,
}

fn begehe(b: &Block, gehalten: &[String], aus: &mut Begehung) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                aus.nimmt.push((l.sperre.text(), l.sperre.span, gehalten.to_vec()));
                let mut innen = gehalten.to_vec();
                innen.push(l.sperre.text());
                begehe(&l.rumpf, &innen, aus);
            }
            _ => {
                let mut orte = Vec::new();
                stand_liest(s, &mut orte);
                for o in &orte {
                    aus.liest.push((o.text(), o.span, gehalten.to_vec()));
                }
                for k in crate::unterbloecke(s) {
                    begehe(k, gehalten, aus);
                }
            }
        }
    }
}

/// The direct callee takes of a hull: every `locks X` / `locks shared X` effect the
/// transitive hull carries -- the same over-approximation `H012` reads ("this call
/// takes X").
fn huelle_nimmt(h: &crate::aufrufgraph::Huelle) -> Vec<String> {
    let mut aus = Vec::new();
    for w in &h.wirkungen {
        if let Some(o) = w
            .strip_prefix("locks shared ")
            .or_else(|| w.strip_prefix("locks "))
        {
            let n = kurz(o).to_string();
            if !aus.contains(&n) {
                aus.push(n);
            }
        }
    }
    aus
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let b = bestand(baum);
    let sperrkarte = sperren(baum, &u);
    let weltnamen: Vec<String> = {
        let mut w: Vec<String> = b.traeger.iter().cloned().collect();
        crate::fuer_jedes_item(baum, &mut |item| match &item.art {
            ItemArt::Atomic(x) => w.push(x.name.text.clone()),
            ItemArt::Tabelle(x) => w.push(x.name.text.clone()),
            ItemArt::Device(x) => w.push(x.name.text.clone()),
            _ => {},
        });
        w
    };
    let konstanten: Vec<String> = b.konstanten.iter().cloned().collect();

    // Functions by graph key.
    let mut funktionen: BTreeMap<String, FnDecl> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            let k = crate::umgebung::qualifiziere(modul, &f.name.text);
            funktionen.insert(k.clone(), f.clone());
        }
    });

    // Declared writes per function, resolved to carriers -- the `TraegerSchreibt`
    // relation `GetrenntK` judges.
    let mut schreibt: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (k, f) in &funktionen {
        let mut param: BTreeMap<String, String> = BTreeMap::new();
        for p in &f.parameter {
            if let Some(t) = tabelle_im_typ(&p.typ, &b.traeger) {
                param.insert(p.name.text.clone(), t);
            }
        }
        let mut s = BTreeSet::new();
        if let Some(w) = &f.effects {
            for e in &w.liste {
                match &e.art {
                    WirkungArt::Schreibt(o) | WirkungArt::Veroeffentlicht(o) => {
                        if let Some(t) = schreibtraeger(&o.text(), &param, &b.traeger) {
                            s.insert(t);
                        }
                    }
                    WirkungArt::Belegt(i) => {
                        if b.traeger.contains(&i.text) {
                            s.insert(i.text.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        schreibt.insert(k.clone(), s);
    }

    // Written by ANY function, declared or performed -- the `freiB` disjunct, the same
    // direction as the old writer set.
    let mut schreiber: BTreeSet<String> = BTreeSet::new();
    for s in schreibt.values() {
        schreiber.extend(s.iter().cloned());
    }
    for f in funktionen.values() {
        if let FnRumpf::Block(bb) = &f.rumpf {
            let mut stapel = vec![bb];
            while let Some(cur) = stapel.pop() {
                for s in &cur.anweisungen {
                    match &s.art {
                        StmtArt::Zuweisung(z) => {
                            let grund = wurzel(&z.ziel.text()).to_string();
                            if b.traeger.contains(&grund) {
                                schreiber.insert(grund);
                            }
                        }
                        StmtArt::Publish(p) => {
                            let grund = wurzel(&p.ziel.text()).to_string();
                            if b.traeger.contains(&grund) {
                                schreiber.insert(grund);
                            }
                        }
                        StmtArt::Exchange(e) => {
                            let grund = wurzel(&e.ort.text()).to_string();
                            if b.traeger.contains(&grund) {
                                schreiber.insert(grund);
                            }
                        }
                        StmtArt::Alloc(a) => {
                            schreiber.insert(a.tisch.text.clone());
                        }
                        StmtArt::ResetArena(t) => {
                            schreiber.insert(t.text.clone());
                        }
                        _ => {}
                    }
                    for kk in crate::unterbloecke(s) {
                        stapel.push(kk);
                    }
                }
            }
        }
    }

    // Threads and their call graphs.
    let pool = kandidatenpool(baum, &funktionen);
    let mut faeden: Vec<BTreeSet<String>> = Vec::new();
    let starts = startet(baum, &g, &u);
    if starts.is_empty() {
        // No declared start: the single driver thread runs everything
        // (`ziel_ort_einfaden` -- one active thread needs no footprint check).
        faeden.push(funktionen.keys().cloned().collect());
    } else {
        for s in &starts {
            faeden.push(erreichbar(&s.funktion, &g, &pool));
        }
    }

    // Contract roots per function, memoised.
    let mut vertragskarte: BTreeMap<String, Vec<(String, Span)>> = BTreeMap::new();
    for (k, f) in &funktionen {
        let geraete = &b.geraete;
        let mut orte = crate::wirkungen::clause_roots(&f.requires, f, &konstanten, &weltnamen, geraete);
        orte.extend(crate::wirkungen::clause_roots(&f.ensures, f, &konstanten, &weltnamen, geraete));
        let mut eng: Vec<(String, Span)> = Vec::new();
        for (w, sp) in orte {
            if eng.iter().any(|(v, _)| v == &w) {
                continue;
            }
            eng.push((w, sp));
        }
        vertragskarte.insert(k.clone(), eng);
    }

    // Footprint per function: own contracts, body reads, direct callee contracts.
    let mut fuss: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut rufer_karte: BTreeMap<String, Vec<(String, String, Span)>> = BTreeMap::new();
    for (k, f) in &funktionen {
        let mut rufpfade: Vec<(String, Span)> = Vec::new();
        if let FnRumpf::Block(bb) = &f.rumpf {
            crate::wirkungen::calls_with_spans(bb, &mut rufpfade);
            // `let x = f() else (e)` is a call site too -- the shared walker reads
            // neither the call nor a place source there (the `H007` handshake documents
            // the same gap), but the callee contract joins the caller footprint all
            // the same (`H012`'s `rufprobe` reads this site as well).
            let mut stapel = vec![bb];
            while let Some(cur) = stapel.pop() {
                for s in &cur.anweisungen {
                    if let StmtArt::LetSonst(x) = &s.art {
                        if let Some(r) = x.als_ruf() {
                            if let Some(p) = r.path() {
                                rufpfade.push((p.text(), r.span));
                            }
                        }
                    }
                    for kk in crate::unterbloecke(s) {
                        stapel.push(kk);
                    }
                }
            }
        }
        let mut gerufene: Vec<(String, String, Span)> = Vec::new();
        for (pfad, span) in &rufpfade {
            if let Some(schluessel) = g.aufloesen(&u, k, pfad) {
                if funktionen.contains_key(&schluessel) {
                    let n = pfad.rsplit("::").next().unwrap_or(pfad).to_string();
                    gerufene.push((schluessel, n, *span));
                }
            }
        }
        rufer_karte.insert(k.clone(), gerufene.clone());
        let mut fset = BTreeSet::new();
        if let Some(orte) = vertragskarte.get(k) {
            for (w, _) in orte {
                fset.insert(w.clone());
            }
        }
        if let FnRumpf::Block(bb) = &f.rumpf {
            for (w, _) in crate::wirkungen::body_roots(f, bb, &konstanten, &weltnamen, &b.geraete) {
                fset.insert(w);
            }
        }
        for (schluessel, _, _) in &gerufene {
            if let Some(orte) = vertragskarte.get(schluessel) {
                for (w, _) in orte {
                    fset.insert(w.clone());
                }
            }
        }
        fuss.insert(k.clone(), fset);
    }

    // Thread-locality: reachers and writers per carrier over the thread graphs.
    let mut erreicht_von: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut geschrieben_von: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (t, graph) in faeden.iter().enumerate() {
        for fname in graph {
            if let Some(fset) = fuss.get(fname) {
                for c in fset {
                    erreicht_von.entry(c.clone()).or_default().insert(t);
                }
            }
            if let Some(s) = schreibt.get(fname) {
                for c in s {
                    geschrieben_von.entry(c.clone()).or_default().insert(t);
                }
            }
        }
    }
    // A carrier is thread-local (`GetrenntK`): no thread reaches it in a footprint
    // while a DIFFERENT thread may write it.
    let lokal = |c: &str| -> bool {
        let reach = erreicht_von.get(c);
        let write = geschrieben_von.get(c);
        match (reach, write) {
            (Some(r), Some(w)) => !r.iter().any(|t| w.iter().any(|v| v != t)),
            _ => true,
        }
    };

    // Signature-held locks per function (short names), and the guard question.
    let mut gehalten: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (k, f) in &funktionen {
        let mut h = Vec::new();
        for p in &f.requires {
            let mut v = Vec::new();
            crate::aufrufgraph::held_aus_pred(p, &mut v);
            for (name, _) in v {
                let n = kurz(&name).to_string();
                if sperrkarte.contains_key(&n) && !h.contains(&n) {
                    h.push(n);
                }
            }
        }
        gehalten.insert(k.clone(), h);
    }
    let bewacht = |c: &str, sperre: &str| -> bool {
        sperrkarte.get(sperre).is_some_and(|s| s.schutz.contains(c))
    };
    let signatur_bewacht = |k: &str, c: &str| -> bool {
        gehalten.get(k).is_some_and(|h| h.iter().any(|l| bewacht(c, l)))
    };
    let invariant_geschuetzt = |c: &str| -> bool {
        sperrkarte.values().any(|s| s.invariante && s.schutz.contains(c))
    };
    // Admitted without a thread question: written by none, signature-guarded, or
    // protected by a lock invariant.
    let ohne_faden_ok = |k: &str, c: &str| -> bool {
        !schreiber.contains(c) || signatur_bewacht(k, c) || invariant_geschuetzt(c)
    };

    for (k, f) in &funktionen {
        let rufer = f.name.text.clone();
        let mut gemeldet: Vec<(&str, String)> = Vec::new();
        let mut refuse = |code: &'static str,
                           wort: String,
                           traeger: &str,
                           span: Span,
                           extra: Option<String>,
                           absagen: &mut Absagen| {
            if ohne_faden_ok(k, traeger) || lokal(traeger) {
                return;
            }
            let merker = (code, traeger.to_string());
            if gemeldet.contains(&merker) {
                return;
            }
            gemeldet.push((code, traeger.to_string()));
            let mut text = format!(
                "`{traeger}` is read by the {wort} of `{rufer}` but no signature lock \
                 guarding it is held, no lock invariant protects it, and it is not \
                 thread-local -- another started thread writes it"
            );
            if let Some(z) = extra {
                text.push_str(&z);
            }
            melde(
                code,
                span,
                text,
                &[
                    "the flagship footprint (`FussS`): every footprint carrier wants a \
                     `requires Held(L)` guard over a `lock L protects` line, a lock \
                     invariant over it, or thread-locality (no other started thread \
                     writes it)",
                    "carriers no function writes need nothing; a read inside `locks L` \
                     over a carrier `L` protects is guarded at the access (`H007` holds \
                     the hold itself)",
                ],
                absagen,
            );
        };
        // N290 -- the contract leg.
        let geraete = &b.geraete;
        for (w, sp) in crate::wirkungen::clause_roots(&f.requires, f, &konstanten, &weltnamen, geraete) {
            refuse("N290", "`requires`".to_string(), &w, sp, None, absagen);
        }
        for (w, sp) in crate::wirkungen::clause_roots(&f.ensures, f, &konstanten, &weltnamen, geraete) {
            refuse("N290", "`ensures`".to_string(), &w, sp, None, absagen);
        }
        // N291 -- the body leg, per site with the locks held there.
        if let FnRumpf::Block(bb) = &f.rumpf {
            let sig = gehalten.get(k).cloned().unwrap_or_default();
            let mut gang = Begehung { liest: Vec::new(), nimmt: Vec::new() };
            begehe(bb, &sig, &mut gang);
            for (text, span, held) in &gang.liest {
                let c = wurzel(text).to_string();
                if f.parameter.iter().any(|p| p.name.text == c) {
                    continue;
                }
                if konstanten.iter().any(|kk| kk == &c) {
                    continue;
                }
                if !b.traeger.contains(&c) || b.geraete.contains(&c) {
                    continue;
                }
                if held.iter().any(|l| bewacht(&c, kurz(l))) {
                    continue;
                }
                refuse("N291", "body".to_string(), &c, *span, None, absagen);
            }
            // N294 -- the floor leg, direct takes against signature-held outers.
            let raenge: Vec<(String, i128)> = sig
                .iter()
                .filter_map(|l| sperrkarte.get(l).and_then(|s| s.rang).map(|r| (l.clone(), r)))
                .collect();
            let boden_kennbar = sig.iter().all(|l| {
                sperrkarte.get(l).is_none_or(|s| s.rang.is_some())
            });
            if boden_kennbar {
                if let Some(boden) = raenge.iter().map(|(_, r)| *r).max() {
                    let mut boden_gemeldet: BTreeSet<String> = BTreeSet::new();
                    for (name, span, _) in &gang.nimmt {
                        let n = kurz(name).to_string();
                        if sig.iter().any(|l| l == &n) {
                            continue;
                        }
                        let rang = sperrkarte.get(&n).and_then(|s| s.rang);
                        if rang.is_none_or(|r| r > boden) {
                            continue;
                        }
                        if !boden_gemeldet.insert(n.clone()) {
                            continue;
                        }
                        let hh: Vec<String> = sig
                            .iter()
                            .filter(|l| {
                                sperrkarte
                                    .get(*l)
                                    .and_then(|s| s.rang)
                                    .is_some_and(|r| r >= rang.unwrap_or(i128::MIN))
                            })
                            .cloned()
                            .collect();
                        melde(
                            "N294",
                            *span,
                            format!(
                                "`{n}` is taken here while `{rufer}` holds {} by signature \
                                 -- a lock floor the ranks do not honour",
                                hh.join(", ")
                            ),
                            &[
                                "the floor of a function is the maximum rank of the locks it \
                                 holds by signature: every take ranks strictly above it \
                                 (`StufenM`, the residue form of `StufenOk`)",
                                "takes under enclosing `locks` blocks are `H006`'s, takes \
                                 through calls `H012`'s -- this leg fires only against \
                                 signature-held outers, where both stay silent",
                            ],
                            absagen,
                        );
                    }
                    // N294 through calls: the callee hull takes against the same floor.
                    if let Some(gerufene) = rufer_karte.get(k) {
                        for (schluessel, cname, span) in gerufene {
                            for genommen in huelle_nimmt(&g.huelle(schluessel)) {
                                if sig.iter().any(|l| l == &genommen) {
                                    continue;
                                }
                                let rang = sperrkarte.get(&genommen).and_then(|s| s.rang);
                                if rang.is_none_or(|r| r > boden) {
                                    continue;
                                }
                                let merker = format!("{cname}:{genommen}");
                                if !boden_gemeldet.insert(merker) {
                                    continue;
                                }
                                melde(
                                    "N294",
                                    *span,
                                    format!(
                                        "this call takes `{genommen}` through `{cname}` while \
                                         `{rufer}` holds a higher-or-equal lock by signature \
                                         -- a lock floor the ranks do not honour"
                                    ),
                                    &[
                                        "floors rise towards the head across calls \
                                         (`RangKette`, `RufPasst.hx/hb`): a callee take ranks \
                                         strictly above every lock the caller holds",
                                        "same-lock pairs are exempt here as under \
                                         `H006`/`H012`; the real same-lock take is `H003`'s",
                                    ],
                                    absagen,
                                );
                            }
                        }
                    }
                }
            }
        }
        // N292 -- the direct-callee leg.
        if let Some(gerufene) = rufer_karte.get(k) {
            for (schluessel, cname, span) in gerufene {
                if let Some(orte) = vertragskarte.get(schluessel) {
                    for (w, _) in orte {
                        refuse(
                            "N292",
                            "contract of the callee".to_string(),
                            w,
                            *span,
                            Some(format!(" (read by `{cname}`)")),
                            absagen,
                        );
                    }
                }
            }
        }
        // N293 -- the indirect-call leg over the candidate pool.
        if let Some(knoten) = g.knoten.get(k) {
            if !knoten.indirect.is_empty() {
                let span = knoten.indirect[0].span;
                let fset = fuss.get(k).cloned().unwrap_or_default();
                for kand in &pool {
                    let cname = kand.rsplit("::").next().unwrap_or(kand).to_string();
                    if let Some(orte) = vertragskarte.get(kand) {
                        for (w, _) in orte {
                            if fset.contains(w) {
                                continue;
                            }
                            if ohne_faden_ok(k, w) || lokal(w) {
                                continue;
                            }
                            let merker = ("N293", format!("{cname}:{w}"));
                            if gemeldet.contains(&merker) {
                                continue;
                            }
                            gemeldet.push(("N293", format!("{cname}:{w}")));
                            melde(
                                "N293",
                                span,
                                format!(
                                    "the indirect call in `{rufer}` may reach `{cname}`, \
                                     whose contract reads `{w}` outside the caller \
                                     footprint -- and `{w}` is shared, guarded by no \
                                     signature lock and by no lock invariant"
                                ),
                                &[
                                    "an indirect call is admitted only if every function \
                                     behind the pointer keeps its footprint inside the \
                                     caller footprint, under a guard, an invariant, or \
                                     thread-locality",
                                ],
                                absagen,
                            );
                        }
                    }
                }
            }
        }
    }
}
