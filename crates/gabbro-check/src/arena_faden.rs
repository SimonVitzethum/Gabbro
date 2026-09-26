//! **Arenas under concurrency (lane 264, OFFEN O20).**
//!
//! The arena flow (`arena.rs`) tracks generations and the commit ceiling along
//! one thread of control; the emitted counters are plain `uint32_t` words
//! (`emit.rs`, `laufzeit/arena_dyn.h`). Two rules close the three O20 rows
//! from the checker side:
//!
//! * `N521` -- a `reset` of `A` in a routine that may run concurrently with a
//!   use of `A` (another `concurrent` member, an `entry`/`boot` dispatch
//!   target) is refused: the reset consumes every generation program-wide,
//!   and no generation analysis tracks the holder across threads.
//! * `N522` -- counter touches (`alloc`, `grow`) of one arena from two
//!   concurrently running routines without a guarding lock held at every
//!   access are refused: the plain words are sound only under mutual
//!   exclusion, and no atomic lowering is built.
//!
//! `child` regions are `N457`'s thread and `start` roots `N462`'s; this pass
//! judges neither (no double verdicts). The commit-ceiling count of repeated
//! entries (pools, `start` statements, unbounded re-entry) is `arena.rs`'s.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

fn kurz(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// **Usable arena bounds.** Mirrors `arena.rs::bodenwert`: `N210` owns the
/// unusable declaration, and no thread question piles onto it.
fn brauchbar(sig: &crate::umgebung::ArenaSig) -> bool {
    matches!((sig.lo, sig.hi), (Some(lo), Some(hi)) if 0 <= lo && lo <= hi && hi >= 1 && hi <= u32::MAX as i128)
}

/// One arena touch site: the arena (qualified), the span, and the `locks`
/// stack (short names) enclosing it. A `locks shared` take guards reads,
/// never counter writes -- the flag travels with the name.
#[derive(Clone)]
struct Genommen {
    sperre: String,
    geteilt: bool,
}

#[derive(Clone)]
struct Stelle {
    arena: String,
    span: Span,
    stapel: Vec<Genommen>,
}

/// The direct touches of one function body: presence only, no flow. `child`
/// regions are skipped (that thread is `N457`'s); `start` roots are not
/// followed (that thread is `N462`'s) -- the closure below is calls-only.
#[derive(Default)]
struct Direkt {
    modul: String,
    /// `reset A` sites.
    resets: Vec<Stelle>,
    /// `alloc A` / `grow A` sites (the emitted counter writes).
    zaehler: Vec<Stelle>,
    /// Every arena this body may use: resets, counter writes, `A[i]`
    /// reads, and `index into A` parameters (a handed-in index may be
    /// read behind the boundary).
    gebraucht: BTreeSet<String>,
    /// Resolved direct call targets (calls-only: no `start` edges).
    ruft: HashSet<String>,
    /// A call through a place: the callee is unknown.
    indirekt: bool,
    /// `requires Held(L)` locks of this function (short names; the flag is
    /// the `shared` side, which guards no counter write).
    gehalten_sig: Vec<(String, bool)>,
    /// `effects { locks L }` locks of this function (short names). A
    /// `locks shared` line guards reads, never a counter write, so it is
    /// not filed here.
    eff_sperren: Vec<String>,
}

struct Sammler<'a> {
    u: &'a crate::umgebung::Umgebung,
    graph: &'a crate::aufrufgraph::Graph,
}

impl<'a> Sammler<'a> {
    /// Resolve a written path the way the call graph does; `None` is a
    /// constructor, an intrinsic or a name M1 refuses -- nothing of this
    /// unit runs there.
    fn loese(&self, modul: &str, p: &Pfad) -> Option<String> {
        let name =
            crate::aufrufgraph::zucker_umschreiben(&p.text()).unwrap_or_else(|| p.text());
        self.graph.aufloesen(self.u, modul, &name)
    }

    fn ruf_sammeln(&self, r: &Ruf, modul: &str, d: &mut Direkt) {
        match &r.ziel {
            CallTarget::Path(p) => {
                if let Some(k) = self.loese(modul, p) {
                    d.ruft.insert(k);
                }
            }
            CallTarget::Place(_) => d.indirekt = true,
        }
    }

    /// Every call inside an expression, innermost first (order is
    /// irrelevant here: presence only).
    fn rufe_in_expr(&self, e: &Expr, modul: &str, d: &mut Direkt) {
        for x in crate::alle_ausdruecke(e) {
            if let ExprArt::Ruf(r) = &x.art {
                self.ruf_sammeln(r, modul, d);
            }
        }
    }

    fn rufe_in_pred(&self, p: &Pred, modul: &str, d: &mut Direkt) {
        for e in crate::ausdruecke_im_praedikat(p) {
            self.rufe_in_expr(e, modul, d);
        }
    }

    /// One place: an `A[i]` read over an unshadowed arena is a use.
    /// Index expressions are read inside out (`A[B[j]]` uses both).
    fn ort_gebrauch(&self, o: &Ort, d: &mut Direkt, lokal: &HashSet<String>) {
        for sx in &o.suffixe {
            if let OrtSuffix::Index(ix) = sx {
                for inner in crate::alle_orte(ix) {
                    self.ort_gebrauch(inner, d, lokal);
                }
            }
        }
        if lokal.contains(&o.basis.text) {
            return;
        }
        let Some(q) = self.u.nennt_arena(&d.modul, &o.basis.text) else {
            return;
        };
        if self.u.arenen.get(&q).is_none_or(|s| !brauchbar(s)) {
            return;
        }
        if let [OrtSuffix::Index(_)] = o.suffixe.as_slice() {
            d.gebraucht.insert(q);
        }
    }

    /// Every `A[i]` read inside an expression.
    fn orte_in_expr(&self, e: &Expr, d: &mut Direkt, lokal: &HashSet<String>) {
        for o in crate::alle_orte(e) {
            self.ort_gebrauch(o, d, lokal);
        }
    }

    /// `alloc`/`grow`/`reset` name their arena through an `Ident`: a local
    /// of the same spelling shadows the declaration (M1 reads the local
    /// meaning), and this pass stays silent about it -- like `arena.rs`.
    fn tisch(&self, t: &Ident, d: &mut Direkt, lokal: &HashSet<String>) -> Option<String> {
        if lokal.contains(&t.text) {
            return None;
        }
        let q = self.u.nennt_arena(&d.modul, &t.text)?;
        if self.u.arenen.get(&q).is_none_or(|s| !brauchbar(s)) {
            return None;
        }
        Some(q)
    }

    fn block(&self, b: &Block, d: &mut Direkt, lokal: &mut HashSet<String>, sperren: &mut Vec<Genommen>, durch_kind: bool) {
        // Block scope like M1 and `arena.rs`: a `let` inside dies with it.
        // Touches are presence-only, so one walk suffices (no loop
        // fixpoint: a second pass would find the same sites).
        let gesichert = lokal.clone();
        for s in &b.anweisungen {
            self.anweisung(s, d, lokal, sperren, durch_kind);
        }
        *lokal = gesichert;
    }

    #[allow(clippy::too_many_arguments)]
    fn anweisung(&self, s: &Stmt, d: &mut Direkt, lokal: &mut HashSet<String>, sperren: &mut Vec<Genommen>, durch_kind: bool) {
        let modul = d.modul.clone();
        match &s.art {
            StmtArt::Alloc(a) => {
                self.rufe_in_expr(&a.wert, &modul, d);
                self.orte_in_expr(&a.wert, d, lokal);
                if let Some(q) = self.tisch(&a.tisch, d, lokal) {
                    d.zaehler.push(Stelle { arena: q.clone(), span: s.span, stapel: sperren.clone() });
                    d.gebraucht.insert(q);
                }
                lokal.insert(a.name.text.clone());
            }
            StmtArt::ResetArena(tisch) => {
                if let Some(q) = self.tisch(tisch, d, lokal) {
                    d.resets.push(Stelle { arena: q.clone(), span: tisch.span, stapel: sperren.clone() });
                    d.gebraucht.insert(q);
                }
            }
            StmtArt::Grow(g) => {
                self.rufe_in_expr(&g.mehr, &modul, d);
                self.orte_in_expr(&g.mehr, d, lokal);
                if let Some(q) = self.tisch(&g.tisch, d, lokal) {
                    d.zaehler.push(Stelle { arena: q.clone(), span: s.span, stapel: sperren.clone() });
                    d.gebraucht.insert(q);
                }
                self.block(&g.sonst, d, lokal, sperren, durch_kind);
            }
            StmtArt::Let(l) => {
                self.rufe_in_expr(&l.wert, &modul, d);
                self.orte_in_expr(&l.wert, d, lokal);
                lokal.insert(l.name.text.clone());
            }
            StmtArt::LetSonst(l) => {
                match &l.quelle {
                    LetQuelle::Ruf(r) => {
                        for arg in &r.argumente {
                            self.rufe_in_expr(arg, &modul, d);
                            self.orte_in_expr(arg, d, lokal);
                        }
                        self.ruf_sammeln(r, &modul, d);
                    }
                    LetQuelle::Ort(o) => self.ort_gebrauch(o, d, lokal),
                }
                lokal.insert(l.name.text.clone());
                lokal.insert(l.fehlername.text.clone());
                self.block(&l.sonst, d, lokal, sperren, durch_kind);
            }
            StmtArt::Zuweisung(z) => {
                self.ort_gebrauch(&z.ziel, d, lokal);
                self.rufe_in_expr(&z.wert, &modul, d);
                self.orte_in_expr(&z.wert, d, lokal);
            }
            StmtArt::Wenn(w) => {
                for (bed, _) in &w.zweige {
                    self.rufe_in_expr(bed, &modul, d);
                    self.orte_in_expr(bed, d, lokal);
                }
                for (_, rumpf) in &w.zweige {
                    self.block(rumpf, d, lokal, sperren, durch_kind);
                }
                if let Some(sonst) = &w.sonst {
                    self.block(sonst, d, lokal, sperren, durch_kind);
                }
            }
            StmtArt::Match(m) => {
                self.rufe_in_expr(&m.gegenstand, &modul, d);
                self.orte_in_expr(&m.gegenstand, d, lokal);
                for z in &m.zweige {
                    if let Some(binder) = &z.binder {
                        lokal.insert(binder.text.clone());
                    }
                    self.block(&z.rumpf, d, lokal, sperren, durch_kind);
                }
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => {
                    if let Some(g) = &t.gegenstand {
                        self.rufe_in_expr(g, &modul, d);
                        self.orte_in_expr(g, d, lokal);
                    }
                    self.domaene_gebrauch(&t.domaene, d, lokal);
                    if let Some(inv) = &t.invariante {
                        self.rufe_in_pred(inv, &modul, d);
                        for e in crate::ausdruecke_im_praedikat(inv) {
                            self.orte_in_expr(e, d, lokal);
                        }
                    }
                    let gesichert = lokal.clone();
                    lokal.insert(t.variable.text.clone());
                    self.block(&t.rumpf, d, lokal, sperren, durch_kind);
                    *lokal = gesichert;
                }
                Schleife::Retry(r) => {
                    self.rufe_in_expr(&r.schranke, &modul, d);
                    self.orte_in_expr(&r.schranke, d, lokal);
                    if let Some(bis) = &r.bis {
                        self.rufe_in_pred(bis, &modul, d);
                    }
                    if let Some(inv) = &r.invariante {
                        self.rufe_in_pred(inv, &modul, d);
                        for e in crate::ausdruecke_im_praedikat(inv) {
                            self.orte_in_expr(e, d, lokal);
                        }
                    }
                    self.block(&r.rumpf, d, lokal, sperren, durch_kind);
                }
                Schleife::Forever(f) => {
                    self.rufe_in_expr(&f.je_durchgang, &modul, d);
                    self.orte_in_expr(&f.je_durchgang, d, lokal);
                    if let Some(inv) = &f.invariante {
                        self.rufe_in_pred(inv, &modul, d);
                        for e in crate::ausdruecke_im_praedikat(inv) {
                            self.orte_in_expr(e, d, lokal);
                        }
                    }
                    self.block(&f.rumpf, d, lokal, sperren, durch_kind);
                }
            },
            StmtArt::Bricht(x) => self.block(&x.rumpf, d, lokal, sperren, durch_kind),
            StmtArt::Narrow(n) => {
                self.ort_gebrauch(&n.ort, d, lokal);
                self.block(&n.sonst, d, lokal, sperren, durch_kind);
            }
            StmtArt::Sperrt(x) => {
                self.ort_gebrauch(&x.sperre, d, lokal);
                sperren.push(Genommen {
                    sperre: kurz(&x.sperre.basis.text).to_string(),
                    geteilt: x.geteilt,
                });
                self.block(&x.rumpf, d, lokal, sperren, durch_kind);
                sperren.pop();
            }
            StmtArt::Observiert(x) => self.block(&x.rumpf, d, lokal, sperren, durch_kind),
            StmtArt::Leave(_) | StmtArt::Next(_) => {}
            StmtArt::Publish(p) => {
                self.ort_gebrauch(&p.ziel, d, lokal);
                self.rufe_in_expr(&p.wert, &modul, d);
                self.orte_in_expr(&p.wert, d, lokal);
            }
            StmtArt::AwaitLoad(a) => {
                self.ort_gebrauch(&a.quelle, d, lokal);
                for o in &a.erwartet {
                    self.ort_gebrauch(o, d, lokal);
                }
                lokal.insert(a.name.text.clone());
            }
            StmtArt::Exchange(e) => {
                self.ort_gebrauch(&e.ort, d, lokal);
                match &e.form {
                    XForm::Update { rumpf, .. } => self.block(rumpf, d, lokal, sperren, durch_kind),
                    XForm::Vergleich { wert, .. } => {
                        self.rufe_in_expr(wert, &modul, d);
                        self.orte_in_expr(wert, d, lokal);
                    }
                }
                lokal.insert(e.name.text.clone());
            }
            StmtArt::Return(Some(x)) => {
                self.rufe_in_expr(x, &modul, d);
                self.orte_in_expr(x, d, lokal);
            }
            StmtArt::Return(None) => {}
            StmtArt::Ruf(r) => {
                for arg in &r.argumente {
                    self.rufe_in_expr(arg, &modul, d);
                    self.orte_in_expr(arg, d, lokal);
                }
                self.ruf_sammeln(r, &modul, d);
            }
            StmtArt::LibraryCall(r) => {
                for arg in &r.args {
                    self.rufe_in_expr(arg, &modul, d);
                    self.orte_in_expr(arg, d, lokal);
                }
            }
            // The child path is its own thread (`N457` in `fusswache2.rs`):
            // neither its touches nor its calls belong to this body -- unless
            // this walk IS the region's own (`durch_kind`), where a nested
            // region is part of its outer one.
            StmtArt::Child(x) => {
                if durch_kind {
                    self.block(x, d, lokal, sperren, durch_kind);
                }
            }
            // A started root is its own thread (`N462` in `fusswache2.rs`):
            // its touches are judged there, and no edge is filed here, so
            // the closure below stays calls-only.
            StmtArt::Start(_) => {}
        }
    }

    /// The places a `traverse` domain names: a domain over `T.slots[A[i]]`
    /// reads the arena behind the index.
    fn domaene_gebrauch(&self, dom: &Domaene, d: &mut Direkt, lokal: &HashSet<String>) {
        match dom {
            Domaene::SlotsVon(o)
            | Domaene::NachfahrenVon(o)
            | Domaene::VorfahrenVon(o)
            | Domaene::Schlange(o)
            | Domaene::ElementeVon(o)
            | Domaene::AbbildungenVon(o)
            | Domaene::KetteIn { ort: o, .. } => self.ort_gebrauch(o, d, lokal),
            Domaene::FelderVon(_) | Domaene::Threads => {}
        }
    }
}

/// A thread the runtime may run beside others. `child` regions are threads
/// here (their reads are `N457`'s only where unguarded); `start` roots are
/// threads too (`N462` judges their writes, not a guarded holder's stale
/// read). Regions address their `Direkt` through a synthetic key (`#kind`
/// never stands in a qualified name).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Faden {
    Funktion(String),
    Region(String, usize),
}

impl Faden {
    fn schluessel(&self) -> String {
        match self {
            Faden::Funktion(k) => k.clone(),
            Faden::Region(k, n) => format!("{k}#kind{n}"),
        }
    }

    fn anzeige(&self) -> String {
        match self {
            Faden::Funktion(k) => format!("`{}`", kurz(k)),
            Faden::Region(k, _) => format!("the `child` path of `{}`", kurz(k)),
        }
    }
}

/// Collect every function body plus every outermost `child` region (a nested
/// region is part of its outer one). Returns the map and the region order.
fn direkt_sammeln(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
    graph: &crate::aufrufgraph::Graph,
) -> (HashMap<String, Direkt>, Vec<(Faden, Span)>) {
    let sammler = Sammler { u, graph };
    let mut map: HashMap<String, Direkt> = HashMap::new();
    let mut regionen: Vec<(Faden, Span)> = Vec::new();
    let mut naechste: usize = 0;
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let key = crate::umgebung::qualifiziere(modul, &f.name.text);
        let mut d = Direkt { modul: modul.to_string(), ..Default::default() };
        for p in &f.requires {
            let mut v = Vec::new();
            crate::aufrufgraph::held_aus_pred(p, &mut v);
            for (name, geteilt) in v {
                let k = (kurz(&name).to_string(), geteilt);
                if !d.gehalten_sig.contains(&k) {
                    d.gehalten_sig.push(k);
                }
            }
        }
        if let Some(w) = &f.effects {
            for e in &w.liste {
                match &e.art {
                    WirkungArt::Sperrt(o) => {
                        let k = kurz(&o.basis.text).to_string();
                        if !d.eff_sperren.contains(&k) {
                            d.eff_sperren.push(k);
                        }
                    }
                    // `locks shared` guards reads, never a counter write.
                    _ => {}
                }
            }
        }
        let mut lokal: HashSet<String> = HashSet::new();
        for p in &f.parameter {
            lokal.insert(p.name.text.clone());
            if let TypExpr::Index { tabelle, .. } = &p.typ {
                if let Some(q) = u.nennt_arena(modul, &tabelle.text) {
                    if u.arenen.get(&q).is_none_or(|s| !brauchbar(s)) {
                        continue;
                    }
                    d.gebraucht.insert(q);
                }
            }
        }
        if let FnRumpf::Block(b) = &f.rumpf {
            let mut sperren = Vec::new();
            sammler.block(b, &mut d, &mut lokal, &mut sperren, false);
            #[allow(clippy::too_many_arguments)]
            fn regionen_in(
                b: &Block,
                fkey: &str,
                modul: &str,
                f: &FnDecl,
                sammler: &Sammler,
                map: &mut HashMap<String, Direkt>,
                regionen: &mut Vec<(Faden, Span)>,
                naechste: &mut usize,
            ) {
                for s in &b.anweisungen {
                    if let StmtArt::Child(region) = &s.art {
                        let faden = Faden::Region(fkey.to_string(), *naechste);
                        *naechste += 1;
                        let mut d = Direkt { modul: modul.to_string(), ..Default::default() };
                        let mut lokal: HashSet<String> = f
                            .parameter
                            .iter()
                            .map(|p| p.name.text.clone())
                            .collect();
                        let mut sperren = Vec::new();
                        sammler.block(region, &mut d, &mut lokal, &mut sperren, true);
                        let span = region.span;
                        map.insert(faden.schluessel(), d);
                        regionen.push((faden, span));
                        continue;
                    }
                    for k in crate::unterbloecke(s) {
                        regionen_in(k, fkey, modul, f, sammler, map, regionen, naechste);
                    }
                }
            }
            regionen_in(b, &key, modul, f, &sammler, &mut map, &mut regionen, &mut naechste);
        }
        map.insert(key, d);
    });
    (map, regionen)
}

/// Calls-only closure over the direct sets: `start` edges are not filed, so
/// started roots never join a starter's graph, and `child` regions never
/// joined any body. An indirect call may be any routine: the whole pool.
fn schliesse(
    start: &str,
    direkt: &HashMap<String, Direkt>,
    pool: &[String],
) -> BTreeSet<String> {
    let mut gesehen = BTreeSet::new();
    let mut stapel = vec![start.to_string()];
    while let Some(s) = stapel.pop() {
        if !gesehen.insert(s.clone()) {
            continue;
        }
        if let Some(d) = direkt.get(&s) {
            for z in &d.ruft {
                stapel.push(z.clone());
            }
            if d.indirekt {
                for k in pool {
                    stapel.push(k.clone());
                }
            }
        }
    }
    gesehen
}

/// Everything one thread may touch, closed over calls.
#[derive(Default)]
struct Beruehrt {
    resets: BTreeMap<String, Vec<Span>>,
    zaehler: Vec<(String, Stelle)>,
    gebraucht: BTreeSet<String>,
}

fn beruehrt(
    faden: &Faden,
    direkt: &HashMap<String, Direkt>,
    pool: &[String],
) -> Beruehrt {
    let mut aus = Beruehrt::default();
    for k in schliesse(&faden.schluessel(), direkt, pool) {
        let Some(d) = direkt.get(&k) else {
            continue;
        };
        for r in &d.resets {
            aus.resets.entry(r.arena.clone()).or_default().push(r.span);
        }
        for z in &d.zaehler {
            aus.zaehler.push((k.clone(), z.clone()));
        }
        aus.gebraucht.extend(d.gebraucht.iter().cloned());
    }
    aus
}

/// The guard question for one counter site, counted the way `H007`
/// (`geteilt.rs`) counts holding: an enclosing `locks` block, an
/// `effects { locks … }` line, or a `requires Held(…)`. A `shared` take
/// guards reads, never a counter write.
fn nimmt(d: &Direkt, stapel: &[Genommen], sperre: &str) -> bool {
    stapel
        .iter()
        .any(|g| g.sperre == sperre && !g.geteilt)
        || d.gehalten_sig
            .iter()
            .any(|(l, geteilt)| l == sperre && !geteilt)
        || d.eff_sperren.iter().any(|l| l == sperre)
}

/// **The one issuance site of `N521`.**
fn melde_n521(
    absagen: &mut Absagen,
    span: Span,
    arena: &str,
    r: &Faden,
    s: &Faden,
    selbst: bool,
) {
    let (wer, wessen) = if selbst {
        (
            format!("{} runs beside its own second instance", r.anzeige()),
            "its own",
        )
    } else {
        (
            format!("{} may run concurrently with {}", r.anzeige(), s.anzeige()),
            "the other thread's",
        )
    };
    absagen.schiebe(
        Absage::fehler(
            "N521",
            span,
            format!(
                "`reset {arena}` in {}: the reset consumes every generation of \
                 `{arena}` program-wide, and an index {wessen} use across it \
                 names another lifetime of the same slots",
                wer
            ),
        )
        .mit_notiz(
            "a lock does not admit this shape: mutual exclusion serializes the \
             counter but cannot revive a consumed generation -- allocate again \
             after the reset where the holder can see it, or give each thread \
             its own arena",
        ),
    );
}

/// **The one issuance site of `N522`.**
fn melde_n522(absagen: &mut Absagen, span: Span, arena: &str, r: &Faden, s: &Faden) {
    absagen.schiebe(
        Absage::fehler(
            "N522",
            span,
            format!(
                "{} and {} both allocate or commit slots of `{arena}` with no \
                 lock guarding every access: the emitted `used`/`committed` \
                 are plain words, and two cursors race",
                r.anzeige(),
                s.anzeige()
            ),
        )
        .mit_notiz(
            "guard every `alloc`/`grow` of this arena in both routines with \
             one lock protecting it (taken inside the routine, not shared), \
             or give each routine its own arena -- the plain words are sound \
             only under mutual exclusion",
        ),
    );
}

fn kleinste(spannen: &[Span]) -> Span {
    let mut sortiert = spannen.to_vec();
    sortiert.sort_by_key(|s| (s.von, s.bis));
    sortiert.into_iter().next().unwrap()
}

/// **Arenas under concurrency: `N521` (reset beside a use) and `N522`
/// (counter touches without a guarding lock).**
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    if u.arenen.is_empty() {
        return;
    }
    let graph = crate::aufrufgraph::erhebe_mit(baum, &u);
    let (direkt, regionen) = direkt_sammeln(baum, &u, &graph);

    // The threads: `concurrent` members (named twice means two instances),
    // `entry` targets (beside everything and beside themselves), the `boot`
    // dispatch (once), and `start` roots (beside the siblings, the starter
    // excluded -- `N462` judges the starter side). Unresolvable names are
    // `W003`'s, never silent threads here.
    struct FadenZeile {
        faden: Faden,
        selbst: bool,
    }
    let mut zeilen: Vec<FadenZeile> = Vec::new();
    let mut anzahl: HashMap<String, usize> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            for pfad in &c.koerper {
                let name =
                    crate::aufrufgraph::zucker_umschreiben(&pfad.text()).unwrap_or_else(|| pfad.text());
                if let Some(k) = graph.aufloesen(&u, modul, &name) {
                    *anzahl.entry(k.clone()).or_insert(0) += 1;
                }
            }
        }
    });
    for (k, n) in &anzahl {
        zeilen.push(FadenZeile { faden: Faden::Funktion(k.clone()), selbst: *n >= 2 });
    }
    for k in crate::kontexte::erhebe(baum) {
        if let Some(voll) = graph.aufloesen(&u, &k.modul, &k.wurzel) {
            zeilen.push(FadenZeile { faden: Faden::Funktion(voll), selbst: true });
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Boot(b) = &item.art {
            if let Some(voll) = graph.aufloesen(&u, modul, &b.dispatch.text()) {
                zeilen.push(FadenZeile { faden: Faden::Funktion(voll), selbst: false });
            }
        }
    });
    let mut gestartet: HashMap<String, usize> = HashMap::new();
    for (modul, pfad, _) in crate::fadenstart::wurzeln(baum) {
        if let Some(voll) = graph.aufloesen(&u, &modul, &pfad) {
            *gestartet.entry(voll).or_insert(0) += 1;
        }
    }
    for (k, n) in &gestartet {
        zeilen.push(FadenZeile { faden: Faden::Funktion(k.clone()), selbst: *n >= 2 });
    }
    for (faden, _) in &regionen {
        zeilen.push(FadenZeile { faden: faden.clone(), selbst: true });
    }
    // One entry per thread; a routine named from two sides keeps the
    // widest self-pair.
    zeilen.sort_by(|a, b| a.faden.cmp(&b.faden));
    let mut faeden: Vec<FadenZeile> = Vec::new();
    for z in zeilen {
        if let Some(letzte) = faeden.last_mut() {
            if letzte.faden == z.faden {
                letzte.selbst = letzte.selbst || z.selbst;
                continue;
            }
        }
        faeden.push(z);
    }
    if faeden.len() < 2 && faeden.iter().all(|z| !z.selbst) {
        return;
    }

    let pool: Vec<String> = direkt.keys().cloned().collect();
    // **The arena protects map, read directly.** `sperrinv::sperrdaten`
    // resolves no arena `protects` (its carriers are tables, globals and
    // states), so the `N457`/`N462` guard disjunct is vacuous for arenas --
    // a measured fact, not a second rule. This pass reads `lock L protects
    // { A }` itself (module-resolved to qualified arenas) and verifies the
    // holding site by site (`nimmt`), which is what admits guarded sharing
    // here without weakening either rule.
    let mut arena_schutz: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Lock(l) = &item.art {
            let schluessel = kurz(&l.name.text).to_string();
            for o in &l.schuetzt {
                if o.suffixe.is_empty() {
                    if let Some(q) = u.nennt_arena(modul, &o.basis.text) {
                        arena_schutz.entry(schluessel.clone()).or_default().insert(q);
                    }
                }
            }
        }
    });
    let beruehrt: Vec<Beruehrt> =
        faeden.iter().map(|z| beruehrt(&z.faden, &direkt, &pool)).collect();

    for i in 0..faeden.len() {
        for j in i..faeden.len() {
            if i == j && !faeden[i].selbst {
                continue;
            }
            let r = &faeden[i].faden;
            let s = &faeden[j].faden;
            let selbst = i == j;
            let br = &beruehrt[i];
            let bs = &beruehrt[j];
            // `N521`: a reset on either side beside a use on the other.
            let mut kandidaten = BTreeSet::new();
            kandidaten.extend(br.resets.keys().cloned());
            kandidaten.extend(bs.resets.keys().cloned());
            let mut n521_gefeuert: BTreeSet<String> = BTreeSet::new();
            for a in &kandidaten {
                let r_setzt = br.resets.get(a).is_some_and(|v| !v.is_empty());
                let s_setzt = bs.resets.get(a).is_some_and(|v| !v.is_empty());
                if (r_setzt && bs.gebraucht.contains(a))
                    || (s_setzt && br.gebraucht.contains(a))
                {
                    let mut stellen = Vec::new();
                    if r_setzt && bs.gebraucht.contains(a) {
                        stellen.extend(br.resets.get(a).cloned().unwrap_or_default());
                    }
                    if s_setzt && br.gebraucht.contains(a) {
                        stellen.extend(bs.resets.get(a).cloned().unwrap_or_default());
                    }
                    melde_n521(absagen, kleinste(&stellen), kurz(a), r, s, selbst);
                    n521_gefeuert.insert(a.clone());
                }
            }
            // `N522`: counter touches on both sides without one guarding
            // lock held at every access. Where `N521` fired the pair is
            // already refused; a second code would only re-name it. `child`
            // regions stay out (`N457` reads the region's names
            // syntactically, guarded or not); `start` roots stay IN:
            // `N462` resolves no arena `writes` (its carriers are tables),
            // so a sharing start root is this rule's alone.
            let kind_beteiligt = !matches!(faeden[i].faden, Faden::Funktion(_))
                || !matches!(faeden[j].faden, Faden::Funktion(_));
            let mut r_z: BTreeSet<String> = BTreeSet::new();
            for (_, st) in &br.zaehler {
                r_z.insert(st.arena.clone());
            }
            let mut s_z: BTreeSet<String> = BTreeSet::new();
            for (_, st) in &bs.zaehler {
                s_z.insert(st.arena.clone());
            }
            for a in r_z.intersection(&s_z) {
                if kind_beteiligt {
                    continue;
                }
                if n521_gefeuert.contains(a) {
                    continue;
                }
                let stellen: Vec<(String, Stelle)> = br
                    .zaehler
                    .iter()
                    .chain(bs.zaehler.iter())
                    .filter(|(_, st)| st.arena == *a)
                    .map(|(k, st)| (k.clone(), st.clone()))
                    .collect();
                let traeger = kurz(a);
                let ausgenommen = arena_schutz.iter().any(|(sperre, orts)| {
                    if !orts.contains(a) {
                        return false;
                    }
                    stellen.iter().all(|(k, st)| {
                        direkt.get(k).is_some_and(|d| nimmt(d, &st.stapel, sperre))
                    })
                });
                if !ausgenommen {
                    let mut spannen: Vec<Span> = stellen.iter().map(|(_, st)| st.span).collect();
                    spannen.sort_by_key(|s| (s.von, s.bis));
                    // The first unguarded site is the actionable one; where
                    // every site is guarded by SOME lock but no single one
                    // guards them all, the first site still shows the gap.
                    melde_n522(absagen, kleinste(&spannen), traeger, r, s);
                }
            }
        }
    }
}
