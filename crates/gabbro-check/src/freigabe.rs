//! **O12: the release obligation, STATED in the obligation channels** (`gabbro obligations
//! --g` and `gabbro counterexample`). One analysis, shared by both subcommands since fix lane
//! F7 (review G02 F3, 2026-09-22); it stood twice until then, byte-for-byte apart from the
//! wording, and every repair had to land twice.
//!
//! At every `locks L { … }` exit the lock invariant of `L` must hold again. No checker rule
//! refuses a locked section whose callees cannot re-establish it from what they PROMISE (their
//! `ensures`), so such a section is checker-clean and still leaves premise (b) of the goal
//! theorem (`NutzerPflicht`) unproved. What follows states that gap per locked section -- as
//! Lean comments in the output, never as a diagnostic: the checker verdict of the file is
//! unchanged by this section.
//!
//! ## The reading (SYNTACTIC, one-sided, and since F7 ORDER-AWARE)
//!
//! It collects the slot cells (`T.slots[i].f`, index included) the invariant reads, then walks
//! the section in execution order with one set: the cells PROMISED at this point.
//!
//! * An unconditional direct call of a uniquely declared callee first KILLS every cell of a
//!   table the callee's `effects` write (its `writes`/`consumes`/`publishes`, and all cells when
//!   the callee has no written `effects` or writes through something that is not a declared
//!   carrier), then ADDS the cells its `ensures` reads (current state only -- `old(..)` speaks
//!   about the entry state). Only the call a statement makes last (the statement call, the
//!   `let` value, the right-hand side of an assignment) promises; a call nested in an argument
//!   or an operand only kills.
//! * A direct write (`=`, `publishes`, `exchange`, `alloc`, `reset`, `grow`) kills the cells of
//!   the table it writes -- every cell at once when the target is not a declared carrier (a
//!   pointer, a field of something unknown). A LATER promise re-establishes them; nothing else
//!   does.
//! * Everything under a branch, a loop, a `narrow`, a `let … else`, a `child` or an `exchange`
//!   update is conditional: its calls are NEVER promises (each is named in the row), and its
//!   writes and callee writes still kill.
//! * A `locks` and an `observes` body are brackets, not branches: walked in line.
//! * An exit (`return`, `leave`, `next`) inside the section is a release too: the cells owed
//!   there are checked at that point.
//! * Indirect calls, library calls, unknown or twice-declared callees are uncountable: named,
//!   and every cell is killed.
//!
//! **Cells are named binder-aware.** A quantifier or `count` variable used as an index, and a
//! callee PARAMETER used as an index in its `ensures`, render as `[…]` -- and a `[…]` cell is
//! never countable: owed, it is always missing; promised, it counts for nothing. (Before F7 a
//! bound `i` in the invariant and a parameter `i` in the callee rendered the same cell and the
//! row said HOLDS.)
//!
//! So the verdicts read:
//!
//! * `RELEASE HOLDS (syntactic)` -- at every exit each owed cell is promised by an unconditional
//!   callee after the last write that could touch it, with no uncounted call in the section.
//!   This is NOT a proof (arithmetic between the promised cells, aliasing beyond declared
//!   carriers and transitive promises are all beyond this text), only the absence of a
//!   syntactic gap.
//! * `RELEASE UNPROVED` -- the exact gap: cells no callee promises, cells written after their
//!   last promise, early exits, and calls whose promise cannot be counted.
//!
//! A missed form stays on the obliging side: an unknown expression shape contributes no promised
//! cell, and every statement shape is walked (`crate::unterbloecke`, exhaustive).

use gabbro_syntax::ast::*;

use std::collections::{BTreeMap, BTreeSet};

/// The marker a cell carries when one of its indices is not countable.
const UNZAEHLBAR: &str = "[…]";

/// An index as the cell name carries it: a literal by value, a free bare name by name, a bound
/// name (quantifier, `count`, callee parameter) or anything else as `[…]`.
fn index_text(e: &Expr, gebunden: &BTreeSet<String>) -> String {
    match &e.art {
        ExprArt::Zahl(n) => format!("[{n}]"),
        ExprArt::Klammer(x) => index_text(x, gebunden),
        ExprArt::Ort(o) if o.suffixe.is_empty() && !gebunden.contains(&o.basis.text) => {
            format!("[{}]", o.basis.text)
        }
        _ => UNZAEHLBAR.to_string(),
    }
}

/// A slot read `T.slots[i].f`, rendered with its index -- or `None` for any other place.
fn als_schlitz(o: &Ort, gebunden: &BTreeSet<String>) -> Option<String> {
    match o.suffixe.as_slice() {
        [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)]
            if slots.text == "slots" && !gebunden.contains(&o.basis.text) =>
        {
            Some(format!("{}.slots{}.{}", o.basis.text, index_text(i, gebunden), f.text))
        }
        _ => None,
    }
}

/// Slot cells read by an expression (no `old`: it promises nothing about the release state).
fn zellen_expr(e: &Expr, gebunden: &BTreeSet<String>, acc: &mut BTreeSet<String>) {
    match &e.art {
        ExprArt::Ort(o) => {
            if let Some(z) = als_schlitz(o, gebunden) {
                acc.insert(z);
            }
        }
        ExprArt::Alt(_) => {}
        ExprArt::Klammer(x) => zellen_expr(x, gebunden, acc),
        ExprArt::Unaer(_, x) => zellen_expr(x, gebunden, acc),
        ExprArt::Binaer(_, a, b) => {
            zellen_expr(a, gebunden, acc);
            zellen_expr(b, gebunden, acc);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                zellen_expr(a, gebunden, acc);
            }
        }
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                zellen_expr(a, gebunden, acc);
            }
        }
        ExprArt::Eingebaut(b) => match &**b {
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                if let Some(z) = als_schlitz(o, gebunden) {
                    acc.insert(z);
                }
            }
            Eingebaut::Aligned(a, b) => {
                zellen_expr(a, gebunden, acc);
                zellen_expr(b, gebunden, acc);
            }
            Eingebaut::Sizeof(TypOderOrt::Typ(_)) | Eingebaut::Lenof(TypOderOrt::Typ(_)) => {}
        },
        ExprArt::Zaehle { variable, rumpf, .. } => {
            let mut innen = gebunden.clone();
            innen.insert(variable.text.clone());
            zellen_pred(rumpf, &innen, acc);
        }
        ExprArt::ArrayLit(es) => {
            for x in es {
                zellen_expr(x, gebunden, acc);
            }
        }
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        // **Lane 261:** a string literal reads no cell -- bytes name nothing.
        | ExprArt::Kette(_)
        | ExprArt::FnWert(_)
        | ExprArt::Grund { .. }
        | ExprArt::Ergebnis => {}
    }
}

/// Slot cells read by a contract predicate; a quantifier binds its variable.
fn zellen_pred(p: &Pred, gebunden: &BTreeSet<String>, acc: &mut BTreeSet<String>) {
    match &p.art {
        PredArt::Vergleich(e) => zellen_expr(e, gebunden, acc),
        PredArt::Quantor(q) => {
            let mut innen = gebunden.clone();
            innen.insert(q.variable.text.clone());
            zellen_pred(&q.rumpf, &innen, acc);
        }
        PredArt::Element(e, _) => zellen_expr(e, gebunden, acc),
        PredArt::Erreicht { von, nach, .. } => {
            for o in [von, nach] {
                if let Some(z) = als_schlitz(o, gebunden) {
                    acc.insert(z);
                }
            }
        }
        PredArt::Held { .. } => {}
        PredArt::Klammer(q) => zellen_pred(q, gebunden, acc),
        PredArt::Nicht(q) => zellen_pred(q, gebunden, acc),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            zellen_pred(a, gebunden, acc);
            zellen_pred(b, gebunden, acc);
        }
    }
}

/// What a write reaches: the cells of named tables, or anything at all.
#[derive(Clone)]
enum Toetet {
    Tabellen(BTreeSet<String>),
    Alles,
}

/// One callee as the rows count it.
struct Gerufener {
    /// Promised cells (countable ones only).
    verspricht: BTreeSet<String>,
    /// What its declared effects may write.
    toetet: Toetet,
}

/// The whole-program facts the rows are read against.
struct Welt {
    /// Short name -> callee; `None` when declared twice (ambiguous).
    gerufene: BTreeMap<String, Option<Gerufener>>,
    /// Every declared carrier name (tables, statics, atomics, arenas, …): a write to one of
    /// them reaches that carrier and no other.
    traeger: BTreeSet<String>,
}

/// The table a place writes, or `Alles` when the place is no declared carrier.
fn ziel_toetet(o: &Ort, welt: &Welt) -> Toetet {
    if welt.traeger.contains(&o.basis.text) {
        Toetet::Tabellen(BTreeSet::from([o.basis.text.clone()]))
    } else if o.suffixe.is_empty() {
        // A bare local (or parameter) re-bound: it writes no carrier.
        Toetet::Tabellen(BTreeSet::new())
    } else {
        Toetet::Alles
    }
}

/// The state of one walk over one section.
struct Lauf<'w> {
    welt: &'w Welt,
    /// The cells the invariant reads.
    braucht: &'w BTreeSet<String>,
    /// Cells promised at this point.
    hat: BTreeSet<String>,
    /// Promised cells killed since their promise, with what killed them.
    getoetet: BTreeMap<String, String>,
    /// Permanent reasons (conditional or uncountable calls, early exits).
    gruende: Vec<String>,
    /// Unconditional promising calls in order, for the row text.
    rufer: Vec<String>,
}

impl Lauf<'_> {
    fn toete(&mut self, t: &Toetet, durch: &str) {
        let weg: Vec<String> = self
            .hat
            .iter()
            .filter(|z| match t {
                Toetet::Alles => true,
                Toetet::Tabellen(ts) => ts.iter().any(|tab| z.starts_with(&format!("{tab}."))),
            })
            .cloned()
            .collect();
        for z in weg {
            self.hat.remove(&z);
            self.getoetet.insert(z, durch.to_string());
        }
    }

    /// One call: `verspricht` says whether its promise counts (the statement's last,
    /// unconditional call).
    fn ruf(&mut self, r: &Ruf, verspricht: bool, bedingt: bool) {
        if r.ist_verbundwert() {
            return;
        }
        let name = match r.path().and_then(|p| p.teile.last()) {
            Some(n) => n.text.clone(),
            None => {
                self.gruende.push(if bedingt {
                    "conditional indirect call".to_string()
                } else {
                    "indirect call".to_string()
                });
                self.toete(&Toetet::Alles, "an indirect call");
                return;
            }
        };
        match self.welt.gerufene.get(&name) {
            None => {
                self.gruende.push(format!("unknown callee {name}"));
                self.toete(&Toetet::Alles, &format!("the unknown callee {name}"));
            }
            Some(None) => {
                self.gruende.push(format!("ambiguous callee {name}"));
                self.toete(&Toetet::Alles, &format!("the ambiguous callee {name}"));
            }
            Some(Some(g)) => {
                self.toete(&g.toetet.clone(), &format!("a write of {name}"));
                if bedingt {
                    self.gruende.push(format!("conditional call of {name}"));
                } else if verspricht {
                    for z in &g.verspricht {
                        self.hat.insert(z.clone());
                        self.getoetet.remove(z);
                    }
                    self.rufer.push(format!("{name} promises {}", menge_text(&g.verspricht)));
                } else {
                    self.rufer.push(format!("{name} (nested) promises nothing countable"));
                }
            }
        }
    }

    /// Every call inside an expression, innermost first; `oben` (the expression itself being
    /// the statement's last call) promises.
    fn ausdruck(&mut self, e: &Expr, oben_verspricht: bool, bedingt: bool) {
        let e = crate::ohne_klammern(e);
        let mut innen: Vec<&Expr> = crate::alle_ausdruecke(e);
        // `alle_ausdruecke` is pre-order: the root comes first. Arguments are evaluated before
        // the call that takes them, so walk from the leaves up.
        innen.reverse();
        for x in innen {
            match &x.art {
                ExprArt::Ruf(r) => {
                    let ist_oben = std::ptr::eq(x, e);
                    self.ruf(r, oben_verspricht && ist_oben, bedingt);
                }
                ExprArt::LibraryCall(l) => {
                    self.gruende.push(format!("library call @{}#{}", l.library.text, l.function.text));
                    self.toete(&Toetet::Alles, "a library call");
                }
                _ => {}
            }
        }
    }

    fn pruefe_ausgang(&mut self, wie: &str) {
        for z in self.braucht.iter() {
            if z.contains(UNZAEHLBAR) || !self.hat.contains(z) {
                let g = format!("early exit (`{wie}`) with {z} not promised");
                if !self.gruende.contains(&g) {
                    self.gruende.push(g);
                }
            }
        }
    }

    fn block(&mut self, b: &Block, bedingt: bool) {
        for s in &b.anweisungen {
            self.stmt(s, bedingt);
        }
    }

    fn stmt(&mut self, s: &Stmt, bedingt: bool) {
        // 1. The statement's own evaluated expressions and predicates, calls first.
        let letzter_ruf_verspricht = matches!(
            &s.art,
            StmtArt::Ruf(_) | StmtArt::Let(_) | StmtArt::Zuweisung(_)
        );
        match &s.art {
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    self.ausdruck(a, false, bedingt);
                }
                self.ruf(r, true, bedingt);
            }
            StmtArt::LetSonst(l) => {
                if let LetQuelle::Ruf(r) = &l.quelle {
                    for a in &r.argumente {
                        self.ausdruck(a, false, bedingt);
                    }
                    // The call may answer the error channel: its promise is conditional.
                    self.ruf(r, false, true);
                }
            }
            _ => {
                for e in crate::eigene_ausdruecke(s) {
                    self.ausdruck(e, letzter_ruf_verspricht, bedingt);
                }
            }
        }
        for p in crate::eigene_praedikate(s) {
            for e in crate::ausdruecke_im_praedikat(p) {
                self.ausdruck(e, false, bedingt);
            }
        }
        // 2. The statement's own write, after its right-hand side.
        let toetet = match &s.art {
            StmtArt::Zuweisung(z) => {
                for e in crate::ausdruecke_im_ort(&z.ziel) {
                    self.ausdruck(e, false, bedingt);
                }
                Some((ziel_toetet(&z.ziel, self.welt), format!("the write to {}", z.ziel.text())))
            }
            StmtArt::Publish(p) => {
                Some((ziel_toetet(&p.ziel, self.welt), format!("the write to {}", p.ziel.text())))
            }
            StmtArt::Exchange(e) => {
                Some((ziel_toetet(&e.ort, self.welt), format!("the exchange on {}", e.ort.text())))
            }
            StmtArt::Alloc(a) => Some((
                Toetet::Tabellen(BTreeSet::from([a.tisch.text.clone()])),
                format!("the allocation in {}", a.tisch.text),
            )),
            StmtArt::ResetArena(a) => Some((
                Toetet::Tabellen(BTreeSet::from([a.text.clone()])),
                format!("the reset of {}", a.text),
            )),
            StmtArt::Grow(g) => Some((
                Toetet::Tabellen(BTreeSet::from([g.tisch.text.clone()])),
                format!("the growth of {}", g.tisch.text),
            )),
            StmtArt::LibraryCall(l) => {
                self.gruende.push(format!("library call @{}#{}", l.library.text, l.function.text));
                Some((Toetet::Alles, "a library call".to_string()))
            }
            StmtArt::Let(_)
            | StmtArt::LetSonst(_)
            | StmtArt::Wenn(_)
            | StmtArt::Match(_)
            | StmtArt::Schleife(_)
            | StmtArt::Bricht(_)
            | StmtArt::Narrow(_)
            | StmtArt::Sperrt(_)
            | StmtArt::Observiert(_)
            | StmtArt::Leave(_)
            | StmtArt::Next(_)
            | StmtArt::AwaitLoad(_)
            | StmtArt::Return(_)
            | StmtArt::Ruf(_)
            | StmtArt::Child(_)
            | StmtArt::Start(_) => None,
        };
        if let Some((t, durch)) = toetet {
            self.toete(&t, &durch);
        }
        // 3. Sub-blocks: brackets in line, everything else conditional.
        let klammer = matches!(&s.art, StmtArt::Sperrt(_) | StmtArt::Observiert(_));
        for k in crate::unterbloecke(s) {
            self.block(k, bedingt || !klammer);
        }
        // 4. An exit releases here.
        match &s.art {
            StmtArt::Return(_) => self.pruefe_ausgang("return"),
            StmtArt::Leave(_) => self.pruefe_ausgang("leave"),
            StmtArt::Next(_) => self.pruefe_ausgang("next"),
            _ => {}
        }
    }
}

/// Every `locks L { … }` section of a body, with a nested section getting its own row --
/// through every sub-block (`observes` and `child` included since F7).
fn sperr_abschnitte<'b>(b: &'b Block, acc: &mut Vec<&'b SperrtStmt>) {
    for s in &b.anweisungen {
        if let StmtArt::Sperrt(sp) = &s.art {
            acc.push(sp);
        }
        for k in crate::unterbloecke(s) {
            sperr_abschnitte(k, acc);
        }
    }
}

fn sammle_items<'a>(
    items: &'a [Item],
    fns: &mut Vec<&'a FnDecl>,
    sperren: &mut Vec<&'a LockDecl>,
    traeger: &mut BTreeSet<String>,
) {
    for item in items {
        match &item.art {
            ItemArt::Funktion(f) => fns.push(f),
            ItemArt::Lock(l) => sperren.push(l),
            ItemArt::Modul(m) => sammle_items(&m.items, fns, sperren, traeger),
            ItemArt::Tabelle(t) => {
                traeger.insert(t.name.text.clone());
            }
            ItemArt::Statisch(s) => {
                traeger.insert(s.name.text.clone());
            }
            ItemArt::Atomic(a) => {
                traeger.insert(a.name.text.clone());
            }
            ItemArt::Arena(a) => {
                traeger.insert(a.name.text.clone());
            }
            _ => {}
        }
    }
}

fn menge_text(m: &BTreeSet<String>) -> String {
    if m.is_empty() {
        return "{}".to_string();
    }
    let v: Vec<&str> = m.iter().map(|s| s.as_str()).collect();
    format!("{{{}}}", v.join(", "))
}

/// What a callee's declared effects may write.
fn toetet_von(f: &FnDecl, traeger: &BTreeSet<String>) -> Toetet {
    let Some(w) = &f.effects else {
        // Derived effects: this text does not see them -- anything.
        return Toetet::Alles;
    };
    let mut ts = BTreeSet::new();
    for e in &w.liste {
        match &e.art {
            WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                if traeger.contains(&o.basis.text) {
                    ts.insert(o.basis.text.clone());
                } else {
                    return Toetet::Alles;
                }
            }
            WirkungArt::Belegt(a) => {
                ts.insert(a.text.clone());
            }
            WirkungArt::Liest(_)
            | WirkungArt::Sperrt(_)
            | WirkungArt::SperrtGeteilt(_)
            | WirkungArt::Maskiert(_)
            | WirkungArt::Divergiert
            | WirkungArt::Rein => {}
        }
    }
    Toetet::Tabellen(ts)
}

/// The O12 release-obligation section: one row per `locks L { … }` section, as Lean comments
/// (never a diagnostic -- the checker verdict stands). `zusatz` is appended to the header's
/// last sentence (a subcommand's own note, or empty).
pub fn freigabe_abschnitt(tree: &Programm, zusatz: &str) -> String {
    let mut out = String::new();
    out.push_str("\n-- RELEASE OBLIGATIONS (stated, not discharged -- O12).\n");
    out.push_str("--\n");
    out.push_str("-- At every `locks L { ... }` exit the lock invariant of `L` must hold\n");
    out.push_str("-- again, and it must follow from what the section's callees PROMISE\n");
    out.push_str("-- (their `ensures`), not from what their bodies happen to do. No checker\n");
    out.push_str("-- rule refuses a section whose callees cannot re-establish it, so such\n");
    out.push_str("-- a section is checker-clean and still leaves `NutzerPflicht` unproved.\n");
    out.push_str("-- Each row below is syntactic, one-sided and order-aware (see\n");
    out.push_str("-- `crates/gabbro-check/src/freigabe.rs`): a write or a callee write after\n");
    out.push_str("-- the last promise of a cell breaks it. `RELEASE HOLDS (syntactic)` is\n");
    out.push_str("-- not a proof, while `RELEASE UNPROVED` names the exact gap.");
    out.push_str(zusatz);
    out.push('\n');
    let mut fns = Vec::new();
    let mut sperren = Vec::new();
    let mut traeger = BTreeSet::new();
    sammle_items(&tree.items, &mut fns, &mut sperren, &mut traeger);
    if sperren.iter().all(|l| l.invariante.is_none()) {
        out.push_str("-- No lock carries an invariant -- nothing is owed at any release.\n");
        return out;
    }
    // Callees by short name; a short name declared twice promises nothing countable --
    // guessing the body would wed the row to the wrong contract.
    let mut gerufene: BTreeMap<String, Option<Gerufener>> = BTreeMap::new();
    for f in &fns {
        let params: BTreeSet<String> = f.parameter.iter().map(|p| p.name.text.clone()).collect();
        let mut zellen = BTreeSet::new();
        for e in &f.ensures {
            zellen_pred(e, &params, &mut zellen);
        }
        zellen.retain(|z| !z.contains(UNZAEHLBAR));
        let g = Gerufener { verspricht: zellen, toetet: toetet_von(f, &traeger) };
        if gerufene.contains_key(&f.name.text) {
            gerufene.insert(f.name.text.clone(), None);
        } else {
            gerufene.insert(f.name.text.clone(), Some(g));
        }
    }
    let welt = Welt { gerufene, traeger };
    let mut zeilen = 0;
    for f in &fns {
        let FnRumpf::Block(b) = &f.rumpf else {
            continue;
        };
        let mut abschnitte = Vec::new();
        sperr_abschnitte(b, &mut abschnitte);
        for sp in abschnitte {
            zeilen += 1;
            let sperre_name = &sp.sperre.basis.text;
            // Same rule as for callees: a short lock name declared twice resolves to nothing
            // countable.
            let treffer: Vec<&&LockDecl> =
                sperren.iter().filter(|l| &l.name.text == sperre_name).collect();
            let [sperre] = treffer.as_slice() else {
                out.push_str(&format!(
                    "-- * {} locks `{}`: that lock is declared nowhere or ambiguously -- RELEASE UNPROVED (unknown lock).\n",
                    f.name.text, sperre_name
                ));
                continue;
            };
            let Some(inv) = &sperre.invariante else {
                out.push_str(&format!(
                    "-- * {} locks `{}`: no invariant -- nothing is owed at this release.\n",
                    f.name.text, sperre_name
                ));
                continue;
            };
            let mut braucht = BTreeSet::new();
            zellen_pred(inv, &BTreeSet::new(), &mut braucht);
            if braucht.is_empty() {
                out.push_str(&format!(
                    "-- * {} locks `{}`: the invariant mentions no slot cell -- nothing countable is owed at this release.\n",
                    f.name.text, sperre_name
                ));
                continue;
            }
            let mut lauf = Lauf {
                welt: &welt,
                braucht: &braucht,
                hat: BTreeSet::new(),
                getoetet: BTreeMap::new(),
                gruende: Vec::new(),
                rufer: Vec::new(),
            };
            lauf.block(&sp.rumpf, false);
            let mut gruende: Vec<String> = Vec::new();
            for z in &braucht {
                if z.contains(UNZAEHLBAR) {
                    gruende.push(format!(
                        "no callee promises {z} (a bound or computed index is never countable)"
                    ));
                } else if !lauf.hat.contains(z) {
                    match lauf.getoetet.get(z) {
                        Some(durch) => gruende.push(format!(
                            "{z} is overwritten after its last promise (by {durch})"
                        )),
                        None => gruende.push(format!("no callee promises {z}")),
                    }
                }
            }
            gruende.extend(lauf.gruende.iter().cloned());
            let ruf_text =
                if lauf.rufer.is_empty() { "no calls".to_string() } else { lauf.rufer.join("; ") };
            if gruende.is_empty() {
                out.push_str(&format!(
                    "-- * {} locks `{}`: invariant over {}; {} -- RELEASE HOLDS (syntactic).\n",
                    f.name.text,
                    sperre_name,
                    menge_text(&braucht),
                    ruf_text
                ));
            } else {
                out.push_str(&format!(
                    "-- * {} locks `{}`: invariant over {}; {} -- RELEASE UNPROVED: {}.\n",
                    f.name.text,
                    sperre_name,
                    menge_text(&braucht),
                    ruf_text,
                    gruende.join("; ")
                ));
            }
        }
    }
    if zeilen == 0 {
        out.push_str("-- No `locks` section in any body -- nothing is owed at any release.\n");
    }
    out
}
