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
//! ## Growth accounting (wave D, lane 240)
//!
//! `PLAN-DYNAMISCH.md` §4 tracks, per function body and per path, a pair
//! `(count, committed)` per arena: `count` is the static allocation count
//! since the last reset (this file's `zaehlung`), `committed` is the storage
//! actually usable on the path. The growth points of a program are then
//! enumerable by grep: `alloc` moves `count`, `reset` restores `(0, floor)`.
//!
//! What stands HERE is the accounting with the ceiling read off the
//! declaration (lane 257): the `max` clause where it stands and is usable
//! (`N210` holds `hi <= max`), else the floor (`hi`), so static arenas keep
//! floor and ceiling coincident by construction (`M = hi`,
//! `committed = hi` on every path). `grow` bumps the committed prefix of
//! its path, capped by `M` (`N426` refuses the commit the checker sees
//! reach past it); `alloc` moves `count`, `reset` restores `(0, floor)`.
//! Joins take the maximum of counts (as before) and the minimum of
//! committed (the sound direction: what both paths guarantee); loops keep
//! the minimum, capped by `M` by construction, so committed needs no
//! `UNENDLICH` saturation. `reset` restores the floor: commit never shrinks.
//!
//! Every growth point is cost-visible where the latency promises live, and
//! that is measured, not asserted: `kosten.rs` counts `alloc` as one
//! primitive plus the value plus the `else` (the `Alloc` arm) and `reset`
//! as one primitive (the `ResetArena` arm); `sperrbloecke` walks the same
//! arms, so a `grow`-shaped body inside `locks` counts against `held`
//! (`K002`), and an uncountable alloc value stays unknown (`K003`).
//! Lane 232 owns `kosten.rs`; this file only reads its contract.
//!
//! What is NOT built, and why (finding, measured): `PLAN-DYNAMISCH.md` §4
//! `R-max` — refuse the `alloc` whose static count may reach `M` even with
//! an `else` beside it. Wired with `M = hi` it fires on
//! `beispiele/99-arena-grenze.gab`'s third `alloc` (`Klein capacity 2 .. 2`,
//! count 2 == `M`, `else` present): load-bearing corpus behavior (the
//! boundary demo, emission included) would go red. That is a tightening of
//! the kind lane 184 was rejected for. The `max` syntax now scopes `M`
//! above `hi` (lane 257), but wiring `R-max` is the checker-rules lane's
//! decision, not this one's: the over-cap shape without an `else` stays
//! `N212` (gift 1087 pins it past `hi`), and the shape with an `else`
//! stays accepted. What the ceiling DOES refuse today is the `grow` the
//! checker sees reaching past it (`N426`), branch or no branch.
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
///
/// Wave D adds the committed count per arena (`verpflichtet`): the storage
/// actually usable on this path. On paths no `grow` touches it coincides
/// with the floor (`hi`) — see the module head — and the joins already run
/// the §4 directions (counts join with `max`, committed with `min`), so the
/// `grow` arm (lane 257) only touches the bump site, never the merge.
#[derive(Debug, Clone, Default)]
struct Stand {
    generation: HashMap<String, u64>,
    zaehlung: HashMap<String, u64>,
    /// Committed prefix per arena on this path (`PLAN-DYNAMISCH.md` §4).
    /// Absent means the floor: `verpflichtung` falls back to `boden`.
    verpflichtet: HashMap<String, u64>,
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
    /// The committed count returns to the floor: commit never shrinks
    /// (`PLAN-DYNAMISCH.md` §3, monotone commit). `boden` is `None` exactly
    /// when the declaration never resolved to usable bounds (then `N210`
    /// already fell, and no count question is asked anywhere).
    fn reset(&mut self, arena: &str, frisch: &mut u64, boden: Option<u64>) {
        *frisch = frisch.saturating_add(1);
        self.generation.insert(arena.to_string(), *frisch);
        self.zaehlung.insert(arena.to_string(), 0);
        match boden {
            Some(f) => {
                self.verpflichtet.insert(arena.to_string(), f);
            }
            None => {
                self.verpflichtet.remove(arena);
            }
        }
    }

    /// Join two branch states: the count is the maximum, and a generation
    /// that differs between the sides is replaced by a fresh one -- an
    /// older index MAY be stale on the joined path.
    ///
    /// The committed count joins with the minimum — the sound direction:
    /// what both paths guarantee (`PLAN-DYNAMISCH.md` §4). A side that never
    /// touched the arena stands at the floor, so `boden` (the floor per
    /// arena, `None` where the declaration is unusable) fills absent
    /// entries. The result never exceeds either side and never the ceiling.
    fn vereinige(
        &mut self,
        andere: &Stand,
        frisch: &mut u64,
        boden: &HashMap<String, u64>,
    ) {
        let mut arenan: HashSet<String> = HashSet::new();
        for k in self.zaehlung.keys() {
            arenan.insert(k.clone());
        }
        for k in andere.zaehlung.keys() {
            arenan.insert(k.clone());
        }
        for k in self.verpflichtet.keys() {
            arenan.insert(k.clone());
        }
        for k in andere.verpflichtet.keys() {
            arenan.insert(k.clone());
        }
        for a in arenan {
            let z = self.zaehlung(&a).max(andere.zaehlung(&a));
            self.zaehlung.insert(a.clone(), z);
            if self.generation(&a) != andere.generation(&a) {
                *frisch = frisch.saturating_add(1);
                self.generation.insert(a.clone(), *frisch);
            }
            match (self.verpflichtet.get(&a).copied(), andere.verpflichtet.get(&a).copied()) {
                (Some(x), Some(y)) => {
                    self.verpflichtet.insert(a, x.min(y));
                }
                (Some(x), None) => {
                    let c = boden.get(&a).copied().map(|f| x.min(f)).unwrap_or(x);
                    self.verpflichtet.insert(a, c);
                }
                (None, Some(y)) => {
                    let c = boden.get(&a).copied().map(|f| y.min(f)).unwrap_or(y);
                    self.verpflichtet.insert(a, c);
                }
                // Both sides at the floor: absent means the floor, so no
                // entry is written.
                (None, None) => {}
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
    /// The commit floor per arena (qualified name -> `hi`), built once per
    /// pass from the declarations. Without a `max` clause the floor is
    /// also the ceiling (`M = hi`); the ceiling map beside this one splits
    /// the two where the clause stands. Absent exactly where the
    /// declaration is unusable (`N210`).
    boden: HashMap<String, u64>,
    /// The ceiling per arena (qualified name -> `M`), built once per pass
    /// (lane 257): the `max` clause where it stands and is usable, else
    /// the floor (`hi`). Absent exactly where the declaration is
    /// unusable (`N210`) -- then no commit question is asked either.
    decke: HashMap<String, u64>,
    /// (code, span) pairs already reported: a loop body walks twice (see
    /// `schleife`), and the second walk must not report the first walk's
    /// findings again.
    gemeldet: HashSet<(String, u32, u32)>,
}

/// The floor of `sig`: the initially committed count. `Some(hi)` exactly
/// when the declaration resolves to usable bounds (the `N210` shape —
/// `0 <= lo <= hi`, `hi >= 1`, `hi` namable); `None` where `N210` already
/// fell, so no committed question is asked there either.
fn bodenwert(sig: &crate::umgebung::ArenaSig) -> Option<u64> {
    match (sig.lo, sig.hi) {
        (Some(lo), Some(hi))
            if 0 <= lo && lo <= hi && hi >= 1 && hi <= u32::MAX as i128 =>
        {
            Some(hi as u64)
        }
        _ => None,
    }
}

/// The ceiling of `sig`: the reservable count. `Some(M)` exactly when
/// the declaration resolves to usable bounds (the `N210` shape --
/// `0 <= lo <= hi <= M`, `M >= 1`, `M` namable) with `hat_decke` saying
/// whether a `max` clause stands: without one the ceiling is the floor
/// (`hi`); with one it is the clause, and a clause that never resolved
/// to a usable value is `None` (`N210` owns that shape, and no commit
/// question is asked there either).
fn deckenwert(sig: &crate::umgebung::ArenaSig, hat_decke: bool) -> Option<u64> {
    let (lo, hi) = match (sig.lo, sig.hi) {
        (Some(lo), Some(hi))
            if 0 <= lo && lo <= hi && hi >= 1 && hi <= u32::MAX as i128 =>
        {
            (lo, hi)
        }
        _ => return None,
    };
    let _ = lo;
    if !hat_decke {
        return Some(hi as u64);
    }
    match sig.max {
        Some(m) if hi <= m && m <= u32::MAX as i128 => Some(m as u64),
        _ => None,
    }
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    erklaerungen(baum, &u, absagen);
    let mut boden: HashMap<String, u64> = HashMap::new();
    for (q, sig) in &u.arenen {
        if let Some(f) = bodenwert(sig) {
            boden.insert(q.clone(), f);
        }
    }
    // **Lane 257:** which arenas carry a `max` clause -- the ceiling map
    // needs the clause presence, not just its value (an unresolved clause
    // is `None` in the map like no clause, but only the first is `N210`).
    let mut mit_decke: HashSet<String> = HashSet::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Arena(a) = &item.art else {
            return;
        };
        if a.max.is_some() {
            if let Some(q) = u.nennt_arena(modul, &a.name.text) {
                mit_decke.insert(q);
            }
        }
    });
    let mut decke: HashMap<String, u64> = HashMap::new();
    for (q, sig) in &u.arenen {
        if let Some(m) = deckenwert(sig, mit_decke.contains(q)) {
            decke.insert(q.clone(), m);
        }
    }
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
            boden: boden.clone(),
            decke: decke.clone(),
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
        } else {
            // **Lane 257: the ceiling beside the pair (`N210`).** The
            // bounds are usable here, so the ceiling question is asked;
            // where they are not, the bound refusal above already fell
            // and no second verdict piles onto the declaration. A clause
            // that is no translation-time constant leaves the ceiling
            // uncountable; a ceiling below the hard bound reserves less
            // address than storage starts committed; beyond `u32::MAX`
            // the counter cannot name the slots it would commit.
            match (&a.max, sig.max) {
                (Some(_), None) => {
                    melde_erklaerung(
                        absagen,
                        "N210",
                        a.span,
                        format!(
                            "`{}` declares no constant ceiling: the `max` \
                             clause of an `arena` is a translation-time \
                             constant like both bounds",
                            a.name.text
                        ),
                        "without a constant ceiling the checker cannot hold \
                         a commit below it and the loader cannot reserve it",
                    );
                }
                (Some(_), Some(m)) if m < hi => {
                    melde_erklaerung(
                        absagen,
                        "N210",
                        a.span,
                        format!(
                            "`{}` commits `{hi}` slots under a ceiling of \
                             `{m}`: `hi <= max`, the ceiling never stands \
                             below the committed prefix",
                            a.name.text
                        ),
                        "storage starts committed up to `hi` -- a ceiling \
                         below it is about a range that is already smaller",
                    );
                }
                // (`hi >= 1` stands in this branch, so `m >= hi >= 1`
                // here: only the upper side is still open.)
                (Some(_), Some(m)) if m > u32::MAX as i128 => {
                    melde_erklaerung(
                        absagen,
                        "N210",
                        a.span,
                        format!(
                            "`{}` reserves `{m}` slots, and the reservation \
                             holds `1 ..= u32::MAX`: no empty address range, \
                             no counter that cannot name its slots",
                            a.name.text
                        ),
                        "the loader reserves the virtual range for `max` \
                         slots beside the `uint32_t` commit count",
                    );
                }
                _ => {}
            }
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

    /// The ceiling of `arena` (`M` in `PLAN-DYNAMISCH.md` §4): the `max`
    /// clause where it stands and is usable, else the floor (`hi`).
    /// `None` where the declaration is unusable.
    fn obergrenze(&self, arena: &str) -> Option<u64> {
        self.decke.get(arena).copied()
    }

    /// The committed prefix on this path: the tracked value, or the floor
    /// where the path never moved it (absent means the floor).
    fn verpflichtung(&self, arena: &str) -> Option<u64> {
        self.stand
            .verpflichtet
            .get(arena)
            .copied()
            .or_else(|| self.boden.get(arena).copied())
    }

    /// Loop join for the committed axis only: per arena the minimum of the
    /// entry and the one-pass exit, with the floor filling the side that
    /// never moved it. Counts and generations keep their own loop rules
    /// (saturation, fresh generation); this axis needs neither, since the
    /// ceiling caps it by construction.
    fn verbinde_verpflichtung(&self, vor: &Stand, nach_eins: &Stand, nach: &mut Stand) {
        let mut arenan: HashSet<String> = HashSet::new();
        for k in vor.verpflichtet.keys().chain(nach_eins.verpflichtet.keys()) {
            arenan.insert(k.clone());
        }
        for a in arenan {
            let c = match (
                vor.verpflichtet.get(&a).copied(),
                nach_eins.verpflichtet.get(&a).copied(),
            ) {
                (Some(x), Some(y)) => Some(x.min(y)),
                (Some(x), None) | (None, Some(x)) => {
                    Some(self.boden.get(&a).copied().map(|f| x.min(f)).unwrap_or(x))
                }
                (None, None) => None,
            };
            match c {
                Some(c) => {
                    nach.verpflichtet.insert(a, c);
                }
                None => {
                    nach.verpflichtet.remove(&a);
                }
            }
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
            StmtArt::Grow(g) => self.grow(g, s.span),
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
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch, &self.boden),
                    }
                }
                if let Some(sonst) = &w.sonst {
                    self.stand = vor.clone();
                    self.block(sonst);
                    match &mut nach {
                        None => nach = Some(self.stand.clone()),
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch, &self.boden),
                    }
                } else if let Some(n) = &mut nach {
                    n.vereinige(&vor, &mut self.frisch, &self.boden);
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
                        Some(n) => n.vereinige(&self.stand, &mut self.frisch, &self.boden),
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
            // **Lane O-1:** generations and counts flow through the child
            // path like any block.
            StmtArt::Child(x) => self.block(x),
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
            // **Lane 253:** `start` moves no generation and binds nothing.
            StmtArt::Start(_)
            | StmtArt::Return(None)
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
            self.stand.vereinige(&nach_sonst, &mut self.frisch, &self.boden);
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
        //
        // Unchanged by lane 257 on purpose: the `else` is still held
        // against the reservation `lo`, not the committed value
        // (`verpflichtung`, `R-commit` in `PLAN-DYNAMISCH.md` §4) -- `hi >=
        // lo`, so holding it against `lo` is the sharper of the two, and a
        // refusal `R-commit` would add is one `N212` already carries.
        // Re-pointing this comparison at the committed value where it
        // exceeds `hi` is the checker-rules lane's decision, not this one's.
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
            // **Wave D: the ceiling invariant, pinned without a verdict.**
            //
            // The committed prefix never exceeds the ceiling `M`
            // (`obergrenze`: the `max` clause where it stands, else `hi`).
            // `R-max` — refusing the `alloc` that reaches `M` even with an
            // `else` — is NOT wired here: on `beispiele/99` (`Klein capacity
            // 2 .. 2`, third `alloc`, count 2 == `M`, `else` present) it
            // fires, so wiring it reddens load-bearing corpus behavior. See
            // the module head and the lane report; the `else`-less over-cap
            // shape stays `N212`.
            if let Some(m) = self.obergrenze(&q) {
                debug_assert!(
                    self.verpflichtung(&q).map_or(true, |c| c <= m),
                    "committed prefix exceeds the ceiling on `{}`",
                    a.tisch.text
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
                self.stand.vereinige(&nach_sonst, &mut self.frisch, &self.boden);
            }
        }
    }

    /// **`grow A by n else { … };` -- commit `n` slots below the ceiling.**
    ///
    /// The amount is an ordinary expression for the reads inside it, and a
    /// translation-time constant for the commit (`N426` owns both faces of
    /// the uncountable shape). Where the commit fits below the ceiling the
    /// path's committed prefix grows by it; where the checker sees it
    /// reach past the ceiling it is refused (`N426`) -- past the ceiling
    /// there is no commit, only the stop, with or without the branch.
    /// The failure continuation joins like `alloc`'s `else`: it runs
    /// instead of the main path, and its state joins only when it falls
    /// through. `grow` moves no generation and binds no index.
    fn grow(&mut self, g: &GrowStmt, span: Span) {
        self.orte_in_expr(&g.mehr);
        let Some(q) = self.u.nennt_arena(&self.modul, &g.tisch.text) else {
            // **`N213` -- `grow` names a declared arena**, like `alloc`
            // and `reset`.
            if !self.stand.lokal.contains(&g.tisch.text) {
                self.melde(
                    "N213",
                    g.tisch.span,
                    format!(
                        "`{}` names no declared arena: `grow` commits slots \
                         of an `arena` declaration",
                        g.tisch.text
                    ),
                    "the ceiling the commit is held against comes from \
                     `max` -- without the declaration there is no ceiling \
                     to hold it against",
                );
            }
            return;
        };
        // The amount: a constant count of `0 ..= u32::MAX`. A negative or
        // huge amount is no count, and a non-constant one leaves the
        // commit uncountable -- the ceiling cannot be held against a
        // number nobody wrote down.
        let mut menge: Option<u64> = None;
        match self.u.konst_wert(&self.modul, &g.mehr) {
            Some(n) if 0 <= n && n <= u32::MAX as i128 => {
                menge = Some(n as u64);
            }
            _ => {
                self.melde(
                    "N426",
                    g.mehr.span,
                    format!(
                        "`grow` out of `{}` commits no constant slot count: \
                         the `by` amount is a translation-time constant",
                        g.tisch.text
                    ),
                    "the checker holds every commit below the ceiling \
                     before the loader reserves it -- an uncountable commit \
                     is refused where it stands",
                );
            }
        }
        // The ceiling hold: the committed prefix plus the amount never
        // passes `M`. The `else` runs on OOM *below* the ceiling; past it
        // the request is refused before it runs, branch or no branch.
        if let (Some(n), Some(m)) = (menge, self.decke.get(&q).copied()) {
            let committed = self.verpflichtung(&q).unwrap_or(0);
            if committed.saturating_add(n) > m {
                self.melde(
                    "N426",
                    span,
                    format!(
                        "`grow` out of `{}` commits `{n}` slots over \
                         `{committed}` committed: past the ceiling `{m}` -- \
                         past the ceiling there is no commit, only the stop",
                        g.tisch.text
                    ),
                    "the `else` branch runs when the commit fails below the \
                     ceiling; a request the checker sees reaching past it \
                     is refused before it runs",
                );
            } else {
                self.stand.verpflichtet.insert(q.clone(), committed + n);
            }
        }
        self.gabel(&g.sonst);
    }

    fn reset(&mut self, tisch: &Ident) {        let Some(q) = self.u.nennt_arena(&self.modul, &tisch.text) else {
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
        // A reset restores the commit floor beside the fresh generation:
        // commit never shrinks (`PLAN-DYNAMISCH.md` §3).
        let boden = self.boden.get(&q).copied();
        self.stand.reset(&q, &mut self.frisch, boden);
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
                verbunden.vereinige(&nach_eins, &mut self.frisch, &self.boden);
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
                // Wave D: the committed axis joins with the minimum over
                // entry and exit — the loop analogue of `vereinige`, capped
                // by `M` by construction, so no `UNENDLICH` saturation.
                self.verbinde_verpflichtung(&vor, &nach_eins, &mut nach);
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
                verbunden.vereinige(&nach_eins, &mut self.frisch, &self.boden);
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
                // Wave D: the committed axis joins with the minimum over
                // entry and exit — the loop analogue of `vereinige`, capped
                // by `M` by construction, so no `UNENDLICH` saturation.
                self.verbinde_verpflichtung(&vor, &nach_eins, &mut nach);
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
                verbunden.vereinige(&nach_eins, &mut self.frisch, &self.boden);
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
                // Wave D: the committed axis joins with the minimum over
                // entry and exit — the loop analogue of `vereinige`, capped
                // by `M` by construction, so no `UNENDLICH` saturation.
                self.verbinde_verpflichtung(&vor, &nach_eins, &mut nach);
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

/// **Wave-D growth accounting, pinned at the unit level.**
///
/// These tests drive the merge directions (`max` on counts, `min` on
/// committed) and the floor discipline directly: through the real pass they
/// would be invisible on static arenas, because with no `grow` every
/// committed value coincides with the floor and no verdict moves.
#[cfg(test)]
mod wachstumstests {
    use super::*;
    use std::collections::HashMap;

    fn boden(paare: &[(&str, u64)]) -> HashMap<String, u64> {
        paare.iter().map(|(k, v)| ((*k).to_string(), *v)).collect()
    }

    #[test]
    fn verbindung_max_zaehlung_min_verpflichtung() {
        let b = boden(&[("m::A", 8)]);
        let mut links = Stand::default();
        links.zaehlung.insert("m::A".to_string(), 3);
        links.verpflichtet.insert("m::A".to_string(), 8);
        let mut rechts = Stand::default();
        rechts.zaehlung.insert("m::A".to_string(), 5);
        rechts.verpflichtet.insert("m::A".to_string(), 6);
        let mut frisch = 0u64;
        links.vereinige(&rechts, &mut frisch, &b);
        assert_eq!(links.zaehlung.get("m::A"), Some(&5));
        assert_eq!(links.verpflichtet.get("m::A"), Some(&6));
    }

    #[test]
    fn unberuehrte_seite_steht_am_boden() {
        let b = boden(&[("m::A", 8)]);
        let mut links = Stand::default();
        links.zaehlung.insert("m::A".to_string(), 3);
        links.verpflichtet.insert("m::A".to_string(), 8);
        let rechts = Stand::default();
        let mut frisch = 0u64;
        links.vereinige(&rechts, &mut frisch, &b);
        assert_eq!(links.verpflichtet.get("m::A"), Some(&8));
    }

    #[test]
    fn seite_ueber_boden_wird_am_minimum_gekappt() {
        // A grown side (the `grow` bump shape) joined with an untouched one
        // falls back to the floor: the joined path guarantees only what
        // both sides guarantee.
        let b = boden(&[("m::A", 8)]);
        let mut links = Stand::default();
        links.zaehlung.insert("m::A".to_string(), 9);
        links.verpflichtet.insert("m::A".to_string(), 12);
        let rechts = Stand::default();
        let mut frisch = 0u64;
        links.vereinige(&rechts, &mut frisch, &b);
        assert_eq!(links.verpflichtet.get("m::A"), Some(&8));
        assert_eq!(links.zaehlung.get("m::A"), Some(&9));
    }

    #[test]
    fn reset_stellt_boden_wieder_her() {
        let mut s = Stand::default();
        let mut frisch = 0u64;
        s.zaehlung.insert("m::A".to_string(), 7);
        s.verpflichtet.insert("m::A".to_string(), 12);
        s.reset("m::A", &mut frisch, Some(8));
        assert_eq!(s.zaehlung.get("m::A"), Some(&0));
        assert_eq!(s.verpflichtet.get("m::A"), Some(&8));
        // An unusable declaration leaves unknown state, not zero: `N210`
        // owns that shape, and no count is invented for it.
        s.verpflichtet.insert("m::B".to_string(), 5);
        s.reset("m::B", &mut frisch, None);
        assert_eq!(s.verpflichtet.get("m::B"), None);
    }

    #[test]
    fn bodenwert_nur_brauchbare_schranken() {
        use crate::typen::Typ;
        let sig = |lo, hi| crate::umgebung::ArenaSig {
            lo,
            hi,
            max: None,
            element: Typ::Unbekannt,
        };
        assert_eq!(bodenwert(&sig(Some(2), Some(8))), Some(8));
        assert_eq!(bodenwert(&sig(Some(8), Some(2))), None);
        assert_eq!(bodenwert(&sig(Some(0), Some(0))), None);
        assert_eq!(bodenwert(&sig(None, Some(8))), None);
        assert_eq!(bodenwert(&sig(Some(2), None)), None);
    }
    /// The `R-max` shape (`PLAN-DYNAMISCH.md` §4) as a predicate, NOT wired
    /// into the pass: with `M = hi` it fires on `beispiele/99`'s third
    /// `alloc` (`Klein capacity 2 .. 2`, count 2, `else` present), so wiring
    /// it would redden load-bearing corpus behavior (the lane-184 class of
    /// tightening). Wiring it -- also above `hi` now that `max` scopes `M`
    /// there -- is the checker-rules lane's decision.
    #[test]
    fn decke_ohne_klausel_ist_boden_mit_klausel_ist_max() {
        use crate::typen::Typ;
        let sig = |lo, hi, max| crate::umgebung::ArenaSig {
            lo,
            hi,
            max,
            element: Typ::Unbekannt,
        };
        // Static form: the ceiling is the floor.
        assert_eq!(deckenwert(&sig(Some(2), Some(8), None), false), Some(8));
        // Dynamic form: the clause scopes the ceiling above `hi`.
        assert_eq!(deckenwert(&sig(Some(2), Some(8), Some(64)), true), Some(64));
        // A clause at the floor is the static shape spelled out.
        assert_eq!(deckenwert(&sig(Some(2), Some(8), Some(8)), true), Some(8));
        // Unusable in either direction: inverted bounds, a ceiling below
        // the floor, an unresolved clause, a clause past `u32::MAX`.
        assert_eq!(deckenwert(&sig(Some(8), Some(2), None), false), None);
        assert_eq!(deckenwert(&sig(Some(2), Some(8), Some(7)), true), None);
        assert_eq!(deckenwert(&sig(Some(2), Some(8), None), true), None);
        assert_eq!(
            deckenwert(&sig(Some(2), Some(8), Some(u32::MAX as i128 + 1)), true),
            None
        );
        assert_eq!(deckenwert(&sig(None, Some(8), None), false), None);
    }
    #[test]
    fn kappe_erreicht_feuert_auf_neunundneunzig() {
        fn kappe_erreicht(zaehlung: u64, maximum: u64) -> bool {
            zaehlung >= maximum
        }
        // 99's third alloc: two allocations stand, the ceiling is two.
        assert!(kappe_erreicht(2, 2));
        // The first two owe nothing to the ceiling.
        assert!(!kappe_erreicht(0, 2));
        assert!(!kappe_erreicht(1, 2));
    }
}
