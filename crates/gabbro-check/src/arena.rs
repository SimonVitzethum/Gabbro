//! **`arena` -- the monotone region with two bounds** («E4»,
//! `PLAN-ERWEITUNG.md` §3, checker half).
//!
//! The Lean model (`grammatik/Grammatik/Arena.lean`, lane E4 model half)
//! proves the mathematics: allocation within the reservation never fails
//! (`alloc_innerhalb_reserve`), indices are contiguous (`keine_fragmentierung`),
//! a reset empties the arena (`reset_used`), and no index survives a reset
//! by typing. What stands HERE is the checker's half: the declaration
//! against its own shape, and the per-function flow -- which generation is
//! current, how many allocations stand since the last reset, and whether
//! the owed `else` stands beside them.
//!
//! The four rules, each with its probe:
//!
//! | code | rule | probe |
//! |---|---|---|
//! | `N210` | both bounds are constants with `0 <= lo <= hi`, and `hi` fits the emitted counter | gift 885 |
//! | `N211` | no use of an index outside its generation | gift 886 |
//! | `N212` | the `else` is owed exactly when the static count since the last reset may exceed the reservation | gift 887 |
//! | `N213` | `alloc` and `reset` name a declared arena | gift 888 |
//!
//! Two questions belong to existing rules and are NOT re-issued here: the
//! shape of an arena place and whether the index belongs to the arena
//! (`N214`, `m1.rs`, at the one place that types every `Ort`), and the
//! unknown bare name (`M119`, `m1.rs`).
//!
//! ## Counting
//!
//! The count runs per function body, like `costs`: a reset sets it to zero,
//! an `alloc` adds one, a branch joins with the maximum, and a loop whose
//! body allocates saturates -- the bound of a `traverse` domain is a question
//! for `domaene.rs`, and a pass that guesses it here would be the second
//! reader of that promise. An `alloc` with the count already at or above
//! `lo` owes its `else`; below `lo` none is owed because none can run
//! (`alloc_innerhalb_reserve`).
//!
//! ## Generations
//!
//! Each arena carries a generation counter, starting at zero; a reset takes
//! a fresh one. An index bound by `alloc` remembers its generation, and a
//! use in another generation falls (`N211`). A branch that resets on one
//! side only takes a fresh generation at the join: an older index MAY be
//! stale on the joined path, and `N211` is the refusal, not a guess.
//!
//! ## What is NOT here
//!
//! The count is per function: two functions allocating into one arena share
//! the runtime counter, and no static count sees the other. Like `costs`
//! (whose recursion carries an assumption instead of a computation), this
//! pass counts what one body does. A reservation shared across functions
//! needs the whole-program discipline, and that is future work, not a
//! silent promise.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

/// **The saturated count: "more than any reservation".**
///
/// A loop whose body allocates may run any number of times, so after it the
/// count is not a number but the knowledge that no reservation covers it.
/// Every later `alloc` then owes its `else` -- sound in the only direction a
/// static count can be: it never claims room that is not there.
const UNENDLICH: u64 = u64::MAX;

/// Flow state for one function body: the current generation and the static
/// allocation count of every arena, plus which local names are live indices
/// of which generation.
#[derive(Debug, Clone, Default)]
struct Stand {
    generation: HashMap<String, u64>,
    zaehlung: HashMap<String, u64>,
    /// Local name -> (arena, generation). Only `alloc` binds these.
    gebunden: HashMap<String, (String, u64)>,
    /// Local name whose index value is no longer tracked (reassigned,
    /// compound-updated): a use falls (`N211`), because the generation the
    /// name carries is unknown.
    unsicher: HashSet<String>,
    /// Every local name in scope -- arena names shadowed by these are not
    /// arena uses at all, and this pass stays silent about them (M1 reads
    /// the local meaning).
    lokal: HashSet<String>,
}

impl Stand {
    fn generation(&self, arena: &str) -> u64 {
        self.generation.get(arena).copied().unwrap_or(0)
    }

    fn zaehlung(&self, arena: &str) -> u64 {
        self.zaehlung.get(arena).copied().unwrap_or(0)
    }

    /// A fresh generation for `arena`: the reset consumes the old one.
    fn reset(&mut self, arena: &str, frisch: &mut u64) {
        *frisch = frisch.saturating_add(1);
        self.generation.insert(arena.to_string(), *frisch);
        self.zaehlung.insert(arena.to_string(), 0);
    }

    /// Join two branch states: the count is the maximum, and a generation
    /// that differs between the sides is replaced by a fresh one -- an
    /// older index MAY be stale on the joined path.
    fn vereinige(&mut self, andere: &Stand, frisch: &mut u64) {
        let mut arenan: HashSet<String> = HashSet::new();
        for k in self.zaehlung.keys() {
            arenan.insert(k.clone());
        }
        for k in andere.zaehlung.keys() {
            arenan.insert(k.clone());
        }
        for a in arenan {
            let z = self.zaehlung(&a).max(andere.zaehlung(&a));
            self.zaehlung.insert(a.clone(), z);
            if self.generation(&a) != andere.generation(&a) {
                *frisch = frisch.saturating_add(1);
                self.generation.insert(a, *frisch);
            }
        }
    }
}

struct Laeufer<'a> {
    u: &'a crate::umgebung::Umgebung,
    modul: String,
    absagen: &'a mut Absagen,
    stand: Stand,
    frisch: u64,
    /// (code, span) pairs already reported: a loop body walks twice (see
    /// `schleife`), and the second walk must not report the first walk's
    /// findings again.
    gemeldet: HashSet<(String, u32, u32)>,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    erklaerungen(baum, &u, absagen);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut l = Laeufer {
            u: &u,
            modul: modul.to_string(),
            absagen,
            stand: Stand::default(),
            frisch: 0,
            gemeldet: HashSet::new(),
        };
        for p in &f.parameter {
            l.stand.lokal.insert(p.name.text.clone());
        }
        l.block(b);
    });
}

/// **The declarations against their own shape.**
fn erklaerungen(baum: &Programm, u: &crate::umgebung::Umgebung, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Arena(a) = &item.art else {
            return;
        };
        let Some(q) = u.nennt_arena(modul, &a.name.text) else {
            return;
        };
        let Some(sig) = u.arenen.get(&q) else {
            return;
        };
        // **`N210` -- both bounds are constants with `0 <= lo <= hi`.**
        //
        // A bound that is no translation-time constant leaves the
        // reservation uncountable and the emitted array unsized; an
        // inverted pair reserves more than the capacity holds; a negative
        // bound is no capacity; zero holds nothing (`buf[0]` is no C
        // array); and beyond `u32::MAX` the emitted `used` counter cannot
        // name the slots. One rule -- the declaration carries a usable
        // capacity -- with one probe per face (`beispiele/gift/885` pins
        // the inverted face; the faces share the rule like `N065` does).
        let (lo, hi) = match (sig.lo, sig.hi) {
            (Some(lo), Some(hi)) => (lo, hi),
            _ => {
                melde_erklaerung(
                    absagen,
                    "N210",
                    a.span,
                    format!(
                        "`{}` declares no constant capacity: both bounds of \
                         `capacity lo .. hi` are translation-time constants",
                        a.name.text
                    ),
                    "without two constant bounds the checker cannot count \
                     the reservation and the emitter cannot size the array",
                );
                return;
            }
        };
        if lo < 0 || hi < 0 || lo > hi {
            melde_erklaerung(
                absagen,
                "N210",
                a.span,
                format!(
                    "`{}` reserves `{lo} .. {hi}`, and no reservation lies \
                     outside its capacity: `0 <= lo <= hi`",
                    a.name.text
                ),
                "an allocation within the reservation owes no `else` -- \
                 past an inverted pair that promise is about nothing",
            );
        } else if hi == 0 || hi > u32::MAX as i128 {
            melde_erklaerung(
                absagen,
                "N210",
                a.span,
                format!(
                    "`{}` holds `{hi}` elements, and the emitted array holds \
                     `1 ..= u32::MAX`: no zero-size array, no counter that \
                     cannot name its slots",
                    a.name.text
                ),
                "the emitter writes `buf[hi]` with a `uint32_t used` \
                 beside it -- both come from this declaration",
            );
        }
    });
}

fn melde_erklaerung(absagen: &mut Absagen, code: &'static str, span: Span, text: String, notiz: &str) {
    absagen.schiebe(Absage::fehler(code, span, text).mit_notiz(notiz));
}

impl<'a> Laeufer<'a> {
    fn melde(&mut self, code: &'static str, span: Span, text: String, notiz: &str) {
        let schluessel = (code.to_string(), span.von, span.bis);
        if self.gemeldet.insert(schluessel) {
            self.absagen
                .schiebe(Absage::fehler(code, span, text).mit_notiz(notiz));
        }
    }

    /// The reservation of `arena`, or `None` when the declaration never
    /// resolved to usable bounds (then `N210` already fell, and no count
    /// question is asked here).
    fn reservierung(&self, arena: &str) -> Option<i128> {
        let sig = self.u.arenen.get(arena)?;
        match (sig.lo, sig.hi) {
            (Some(lo), Some(hi)) if 0 <= lo && lo <= hi => Some(lo),
            _ => None,
        }
    }

    /// Bind a local name: it shadows any arena of the same spelling from
    /// here on, and it is no live index.
    fn binde_lokal(&mut self, name: &str) {
        self.stand.lokal.insert(name.to_string());
        self.stand.gebunden.remove(name);
        self.stand.unsicher.remove(name);
    }

    /// Walk a nested block WITH scope: a `let` inside dies with it (M1
    /// copies the same way); the arena flow -- generations, counts -- is
    /// global and survives. The function body walks through the same
    /// function: restoring its bindings at the end restores what nobody
    /// reads any more.
    fn block(&mut self, b: &Block) {
        // **Block scope.** A `let` inside a nested block dies with it (M1
        // copies the same way); the arena flow -- generations, counts --
        // is global and survives. Only the top-level body block has no
        // scope to restore, and restoring nothing there is the same code.
        let gesichert_gebunden = self.stand.gebunden.clone();
        let gesichert_unsicher = self.stand.unsicher.clone();
        let gesichert_lokal = self.stand.lokal.clone();
        for s in &b.anweisungen {
            self.anweisung(s);
        }
        self.stand.gebunden = gesichert_gebunden;
        self.stand.unsicher = gesichert_unsicher;
        self.stand.lokal = gesichert_lokal;
    }

    fn anweisung(&mut self, s: &Stmt) {
        match &s.art {
            StmtArt::Alloc(a) => self.alloc(a, s.span),
            StmtArt::ResetArena(tisch) => self.reset(tisch),
            StmtArt::Let(l) => {
                self.orte_in_expr(&l.wert);
                self.binde_lokal(&l.name.text);
            }
            StmtArt::LetSonst(l) => {
                match &l.quelle {
                    LetQuelle::Ruf(r) => {
                        for arg in &r.argumente {
                            self.orte_in_expr(arg);
                        }
                    }
                    LetQuelle::Ort(o) => self.ort(o),
                }
                self.binde_lokal(&l.name.text);
                self.binde_lokal(&l.fehlername.text);
                self.gabel(&l.sonst);
            }
            StmtArt::Zuweisung(z) => {
                self.ort(&z.ziel);
                self.orte_in_expr(&z.wert);
                // Rebinding an index kills the tracked generation: the name
                // keeps its TYPE (M1 is flow-insensitive), but the VALUE is
                // no longer the slot the binding remembers. Copying one live
                // index into another is the one shape that keeps tracking.
                let ziel = z.ziel.basis.text.clone();
                if self.stand.gebunden.contains_key(&ziel)
                    || self.stand.unsicher.contains(&ziel)
                {
                    let mut kopie: Option<(String, u64)> = None;
                    if z.op == ZuwOp::Setzt {
                        if let ExprArt::Ort(o) = &entklammert(&z.wert).art {
                            if o.suffixe.is_empty() {
                                if let Some(eintrag) = self.stand.gebunden.get(&o.basis.text) {
                                    kopie = Some(eintrag.clone());
                                }
                            }
                        }
                    }
                    match kopie {
                        Some(e) => {
                            self.stand.gebunden.insert(ziel.clone(), e);
                            self.stand.unsicher.remove(&ziel);
                        }
                        None => {
                            self.stand.gebunden.remove(&ziel);
                            self.stand.unsicher.insert(ziel.clone());
                        }
                    }
                    self.stand.lokal.insert(ziel);
                }
            }
            StmtArt::Wenn(w) => {
                for (bed, _) in &w.zweige {
                    self.orte_in_expr(bed);
                }
                let vor = self.stand.clone();
                let mut nach: Option<Stand> = None;
                for (_, rumpf) in &w.zweige {
                    self.stand = vor.clone();
                    self.block(rumpf);
                    match &mut nach {
                        None => nach = Some(self.stand.clone()),
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch),
                    }
                }
                if let Some(sonst) = &w.sonst {
                    self.stand = vor.clone();
                    self.block(sonst);
                    match &mut nach {
                        None => nach = Some(self.stand.clone()),
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch),
                    }
                } else if let Some(n) = &mut nach {
                    n.vereinige(&vor, &mut self.frisch);
                }
                // Bindings are block-scoped per arm (`block` restores them),
                // so the join holds flow only -- and `vereinige` touches
                // nothing but generations and counts.
                if let Some(n) = nach {
                    self.stand = n;
                }
            }
            StmtArt::Match(m) => {
                self.orte_in_expr(&m.gegenstand);
                let vor = self.stand.clone();
                let mut nach: Option<Stand> = None;
                for z in &m.zweige {
                    self.stand = vor.clone();
                    if let Some(binder) = &z.binder {
                        self.stand.lokal.insert(binder.text.clone());
                    }
                    self.block(&z.rumpf);
                    match &mut nach {
                        None => nach = Some(self.stand.clone()),
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch),
                    }
                }
                if let Some(n) = nach {
                    self.stand = n;
                }
            }
            StmtArt::Schleife(sch) => self.schleife(sch),
            StmtArt::Narrow(n) => {
                self.ort(&n.ort);
                self.gabel(&n.sonst);
            }
            StmtArt::Sperrt(x) => {
                self.ort(&x.sperre);
                self.block(&x.rumpf);
            }
            // `observes D` names an RCU domain, not a local: nothing to bind.
            StmtArt::Observiert(x) => self.block(&x.rumpf),
            StmtArt::Bricht(x) => self.block(&x.rumpf),
            StmtArt::AwaitLoad(a) => {
                self.ort(&a.quelle);
                for o in &a.erwartet {
                    self.ort(o);
                }
                self.binde_lokal(&a.name.text);
            }
            StmtArt::Exchange(e) => {
                self.ort(&e.ort);
                match &e.form {
                    XForm::Update { rumpf, .. } => self.block(rumpf),
                    XForm::Vergleich { wert, .. } => self.orte_in_expr(wert),
                }
                self.binde_lokal(&e.name.text);
            }
            StmtArt::Publish(p) => {
                self.ort(&p.ziel);
                self.orte_in_expr(&p.wert);
            }
            StmtArt::Ruf(r) => {
                for arg in &r.argumente {
                    self.orte_in_expr(arg);
                }
            }
            StmtArt::LibraryCall(r) => {
                for arg in &r.args {
                    self.orte_in_expr(arg);
                }
            }
            StmtArt::Return(Some(x)) => self.orte_in_expr(x),
            StmtArt::Return(None)
            | StmtArt::Leave(_)
            | StmtArt::Next(_) => {}
        }
    }

    /// The failure continuation runs instead of the main path; its state
    /// joins only when it falls through. `block` scopes the else branch's
    /// own bindings, so the join holds generations and counts only.
    fn gabel(&mut self, sonst: &Block) {
        let nach_haupt = self.stand.clone();
        self.block(sonst);
        if crate::endet_immer(sonst, &[]) {
            self.stand = nach_haupt;
        } else {
            let nach_sonst = self.stand.clone();
            self.stand = nach_haupt;
            self.stand.vereinige(&nach_sonst, &mut self.frisch);
        }
    }

    fn alloc(&mut self, a: &AllocStmt, span: Span) {
        self.orte_in_expr(&a.wert);
        // The annotation is M1's business (`passt` holds it against
        // `index into A`, `M101`: `m1.rs`): a second verdict here would put
        // one code in two files (`pruefe-kennungen.py`). What M1 cannot see
        // -- two arenas with the same bound under a crossed annotation --
        // is booked in the module head, not refused twice.
        let Some(q) = self.u.nennt_arena(&self.modul, &a.tisch.text) else {
            // **`N213` -- `alloc` names a declared arena.**
            //
            // No table, no global, no local reading reaches this statement:
            // the arena word is the only source of slots, so an undeclared
            // name here is not a value of another kind. (A bare unknown
            // name elsewhere is `M119` in `m1.rs`, not this rule.)
            if !self.stand.lokal.contains(&a.tisch.text) {
                self.melde(
                    "N213",
                    a.tisch.span,
                    format!(
                        "`{}` names no declared arena: `alloc` allocates \
                         out of an `arena` declaration",
                        a.tisch.text
                    ),
                    "the reservation the `else` is held against comes from \
                     `capacity lo .. hi` -- without the declaration there is \
                     no count and no generation",
                );
            }
            return;
        };
        // The owed `else`: the count standing here is the number of
        // allocations since the last reset on this path, and the next slot
        // is owed its failure branch exactly when that number may exceed
        // the reservation.
        if let Some(lo) = self.reservierung(&q) {
            let n = self.stand.zaehlung(&q);
            if n >= lo as u64 && a.sonst.is_none() {
                // **`N212` -- the `else` is owed beyond the reservation.**
                self.melde(
                    "N212",
                    span,
                    format!(
                        "`alloc` out of `{}` is allocation number {} since \
                         the last reset, past the reservation `{lo}` -- the \
                         `else` branch is owed",
                        a.tisch.text,
                        n + 1
                    ),
                    "inside the reservation no `else` is owed because none \
                     can run; past it the arena may be full, and the failure \
                     path is written down, not hoped away",
                );
            }
        }
        let g = self.stand.generation(&q);
        self.stand.zaehlung.insert(q.clone(), self.stand.zaehlung(&q).saturating_add(1));
        self.stand.gebunden.insert(a.name.text.clone(), (q, g));
        self.stand.unsicher.remove(&a.name.text);
        self.stand.lokal.insert(a.name.text.clone());
        if let Some(sonst) = &a.sonst {
            // The failure continuation runs instead of the main path; its
            // state joins only when it falls through.
            let nach_haupt = self.stand.clone();
            self.block(sonst);
            if crate::endet_immer(sonst, &[]) {
                self.stand = nach_haupt;
            } else {
                let nach_sonst = self.stand.clone();
                self.stand = nach_haupt;
                self.stand.vereinige(&nach_sonst, &mut self.frisch);
            }
        }
    }

    fn reset(&mut self, tisch: &Ident) {
        let Some(q) = self.u.nennt_arena(&self.modul, &tisch.text) else {
            // **`N213` -- `reset` names a declared arena**, like `alloc`.
            if !self.stand.lokal.contains(&tisch.text) {
                self.melde(
                    "N213",
                    tisch.span,
                    format!(
                        "`{}` names no declared arena: `reset` starts a fresh \
                         generation of an `arena` declaration",
                        tisch.text
                    ),
                    "without the declaration there is no generation to \
                     consume and no index to invalidate",
                );
            }
            return;
        };
        self.stand.reset(&q, &mut self.frisch);
    }

    /// A loop: the body walks from the entry state, then once more from the
    /// joined state -- the second walk is the later iterations, where an
    /// index bound in the first pass is already stale. Findings carry their
    /// (code, span), so the second walk reports nothing twice. After the
    /// loop the count is the entry plus the body delta times the bound
    /// (`retry … bounded N` carries its own; `traverse` and `forever` may
    /// repeat without one, so a growing body saturates); a body that resets
    /// takes a fresh generation, because the loop may have run.
    fn schleife(&mut self, sch: &Schleife) {
        let vor = self.stand.clone();
        match sch {
            Schleife::Traverse(t) => {
                self.stand.lokal.insert(t.variable.text.clone());
                self.stand.gebunden.remove(&t.variable.text);
                self.stand.unsicher.remove(&t.variable.text);
                if let Some(g) = &t.gegenstand {
                    self.orte_in_expr(g);
                }
                self.block(&t.rumpf);
                let nach_eins = self.stand.clone();
                let mut verbunden = vor.clone();
                verbunden.vereinige(&nach_eins, &mut self.frisch);
                self.stand = verbunden.clone();
                self.block(&t.rumpf);
                let mut nach = vor.clone();
                // A growing body inside an unbounded loop saturates: the
                // loop may run any number of times.
                for (a, z) in &nach_eins.zaehlung {
                    let delta = z.saturating_sub(vor.zaehlung(a));
                    if delta > 0 {
                        nach.zaehlung.insert(a.clone(), UNENDLICH);
                    } else {
                        nach.zaehlung.insert(a.clone(), *z);
                    }
                }
                for (a, g) in &nach_eins.generation {
                    if *g != vor.generation(a) {
                        self.frisch = self.frisch.saturating_add(1);
                        nach.generation.insert(a.clone(), self.frisch);
                    }
                }
                let gebunden = vor.gebunden.clone();
                let unsicher = vor.unsicher.clone();
                let lokal = vor.lokal.clone();
                self.stand = nach;
                self.stand.gebunden = gebunden;
                self.stand.unsicher = unsicher;
                self.stand.lokal = lokal;
                let _ = &verbunden;
            }
            Schleife::Retry(r) => {
                self.block(&r.rumpf);
                let nach_eins = self.stand.clone();
                let mut verbunden = vor.clone();
                verbunden.vereinige(&nach_eins, &mut self.frisch);
                self.stand = verbunden;
                self.block(&r.rumpf);
                let schranke = self.u.konst_wert(&self.modul, &r.schranke).unwrap_or(-1);
                let mut nach = vor.clone();
                for (a, z) in &nach_eins.zaehlung {
                    let delta = z.saturating_sub(vor.zaehlung(a));
                    if schranke < 0 {
                        if delta > 0 {
                            nach.zaehlung.insert(a.clone(), UNENDLICH);
                        }
                    } else {
                        let wachstum = delta.saturating_mul(schranke.max(0) as u64);
                        nach.zaehlung.insert(
                            a.clone(),
                            vor.zaehlung(a).saturating_add(wachstum),
                        );
                    }
                }
                for (a, g) in &nach_eins.generation {
                    if *g != vor.generation(a) {
                        self.frisch = self.frisch.saturating_add(1);
                        nach.generation.insert(a.clone(), self.frisch);
                    }
                }
                let gebunden = vor.gebunden.clone();
                let unsicher = vor.unsicher.clone();
                let lokal = vor.lokal.clone();
                self.stand = nach;
                self.stand.gebunden = gebunden;
                self.stand.unsicher = unsicher;
                self.stand.lokal = lokal;
            }
            Schleife::Forever(f) => {
                self.block(&f.rumpf);
                let nach_eins = self.stand.clone();
                let mut verbunden = vor.clone();
                verbunden.vereinige(&nach_eins, &mut self.frisch);
                self.stand = verbunden;
                self.block(&f.rumpf);
                let mut nach = vor.clone();
                for (a, z) in &nach_eins.zaehlung {
                    let delta = z.saturating_sub(vor.zaehlung(a));
                    if delta > 0 {
                        nach.zaehlung.insert(a.clone(), UNENDLICH);
                    }
                }
                for (a, g) in &nach_eins.generation {
                    if *g != vor.generation(a) {
                        self.frisch = self.frisch.saturating_add(1);
                        nach.generation.insert(a.clone(), self.frisch);
                    }
                }
                let gebunden = vor.gebunden.clone();
                let unsicher = vor.unsicher.clone();
                let lokal = vor.lokal.clone();
                self.stand = nach;
                self.stand.gebunden = gebunden;
                self.stand.unsicher = unsicher;
                self.stand.lokal = lokal;
            }
        }
    }

    /// Every `Ort` inside an expression, including the index expressions of
    /// arena reads nested in other places.
    fn orte_in_expr(&mut self, e: &Expr) {
        for o in crate::alle_orte(e) {
            self.ort(o);
        }
    }

    /// One place: when its basis is an unshadowed arena, the index must be
    /// a live index of the current generation.
    fn ort(&mut self, o: &Ort) {
        // Index expressions first: `A[B[j]]` reads inside out.
        for sx in &o.suffixe {
            if let OrtSuffix::Index(ix) = sx {
                self.orte_in_expr(ix);
            }
        }
        if self.stand.lokal.contains(&o.basis.text) {
            return;
        }
        let Some(q) = self.u.nennt_arena(&self.modul, &o.basis.text) else {
            return;
        };
        // A well-shaped read is exactly `A[i]`; M1 (`N214`) owns every
        // other shape, and this pass stays silent about them.
        let [OrtSuffix::Index(ix)] = o.suffixe.as_slice() else {
            return;
        };
        let ix_ohne = entklammert(ix);
        let ExprArt::Ort(io) = &ix_ohne.art else {
            return;
        };
        if !io.suffixe.is_empty() {
            return;
        }
        let name = &io.basis.text;
        if self.stand.unsicher.contains(name) {
            // **`N211` -- no use of an index whose generation is unknown.**
            self.melde(
                "N211",
                io.span,
                format!(
                    "`{name}` may not be a live index of `{}`: reassigned \
                     since its allocation, and no generation is tracked \
                     through the assignment",
                    o.basis.text
                ),
                "bind the index fresh from `alloc`, or read the slot before \
                 reassigning the name",
            );
            return;
        }
        match self.stand.gebunden.get(name) {
            Some((arena, g)) if arena == &q && *g == self.stand.generation(&q) => {}
            Some((arena, _)) if arena == &q => {
                // **`N211` -- no use of an index of a consumed generation.**
                //
                // `reset` consumed the generation this index was bound in;
                // the slot may hold another value now, or nothing yet. The
                // generation is a type index in the Lean model (`ArenaIdx g
                // n` against `Marke (g+1)` does not typecheck); here it is
                // a counter, and the refusal is its shadow.
                self.melde(
                    "N211",
                    io.span,
                    format!(
                        "`{name}` is an index of a consumed generation of \
                         `{}`: a `reset` stood between its `alloc` and this \
                         read",
                        o.basis.text
                    ),
                    "allocate again after the `reset` -- an index obtained \
                     before it names another lifetime of the same slots",
                );
            }
            _ => {
                // Another arena's index, or no tracked index at all: the
                // TYPE question, and M1 (`N214`) asks it.
            }
        }
    }
}

/// Parentheses carry no meaning for the index question.
fn entklammert<'b>(e: &'b Expr) -> &'b Expr {
    let mut e = e;
    while let ExprArt::Klammer(x) = &e.art {
        e = x;
    }
    e
}
