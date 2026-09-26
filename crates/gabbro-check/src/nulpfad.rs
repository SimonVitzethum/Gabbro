//! **`N507` -- a NUL-terminated path the program builds carries its terminator**
//! (lane 262, OFFEN O23).
//!
//! The NUL-terminated path is a named caller obligation (`beispiele/149`: `spec fn
//! path_nul_terminated(path, pathlen)`, counted as `V` at every call). No rule read a
//! byte's value, so a program that never established the terminator called `open` with a
//! frame the kernel may read past. This pass decides the obligation where the program
//! builds the buffer itself:
//!
//! * the buffer is a byte array the pass sees constructed in this body -- a `static`
//!   `[u8; M]` of this module or a `let`-bound `[u8; M]` with a readable length -- and
//! * the terminator is proved: the length argument reads as one constant `L` (a literal,
//!   a `const`, a narrowed range of one value) with a store `buf[L-1] = 0` dominating the
//!   call and no later store that could clear it, or every cell is still zero (a
//!   zero-initialised buffer with no store since).
//!
//! Three shapes answer a call whose callee requires `path_nul_terminated(p, n)`, and only
//! those three are decided here:
//!
//! * **forwarding**: both actuals are the caller's own parameters beside the caller's own
//!   identical clause -- the obligation travels up, as under `N463`;
//! * **a proved buffer**: the shape above;
//! * **anything else is refused (`N507`)**: a caller parameter pair without the clause
//!   (the obligation dropped on the floor), or a built-here buffer with no proof.
//!
//! **What keeps the named obligation instead.** A pointer the pass cannot see built -- a
//! parameter alone, a field, a computed pointer -- is not decided here: the `V` row stays
//! exactly as it stood, and no new code falls beside it. A length that reads as no single
//! constant is proved only by an untouched zeroed buffer; any store since the
//! initialisation narrows the proof to the constant-length shape. Stores under a branch,
//! a loop or an error continuation never count as proof (they may not run) but still kill
//! (they may overwrite). A call that takes the buffer kills every cell (the callee may
//! write through the pointer).
//!
//! **What is NOT decided here.** Strings (`string max N`, lane 261/`zeichenfolge.rs`)
//! never reach a `ptr<u8>` parameter -- they stand only in parameters, results and
//! `let`s (`N465`) and have no lowering (`C001`) -- so no string shape is checked. The
//! kernel honouring the length is still the gate's named assumption. Cross-module
//! statics by bare name are not tracked (same-module statics and locals are).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

/// **One tracked byte buffer**: the length, and which cells provably read `0`.
///
/// `voll` is the zero-initialised baseline (`= 0` with no store since): every index reads
/// `0` except `ausnahmen`, which read unknown. Without the baseline (`voll == false`),
/// `ausnahmen` is the set of indices that provably read `0` instead. Either way the
/// representation stays small: no cell is ever materialised.
#[derive(Debug, Clone)]
struct Puffer {
    laenge: u128,
    voll: bool,
    ausnahmen: HashSet<u128>,
}

impl Puffer {
    /// Does cell `k` provably read `0`?
    fn ist_null(&self, k: u128) -> bool {
        if self.voll {
            !self.ausnahmen.contains(&k)
        } else {
            self.ausnahmen.contains(&k)
        }
    }

    /// Is every cell provably `0` (an untouched zeroed buffer)?
    fn alle_null(&self) -> bool {
        self.voll && self.ausnahmen.is_empty()
    }

    /// Record `buf[k] = 0`.
    fn lege_null(&mut self, k: u128) {
        if self.voll {
            self.ausnahmen.remove(&k);
        } else if k < self.laenge {
            self.ausnahmen.insert(k);
        }
    }

    /// Record `buf[k] = <not provably zero>`.
    fn lege_unklar(&mut self, k: u128) {
        if self.voll {
            if k < self.laenge {
                self.ausnahmen.insert(k);
            }
        } else {
            self.ausnahmen.remove(&k);
        }
    }

    /// A store no index is read from: every cell is unknown afterwards.
    fn toete(&mut self) {
        self.voll = false;
        self.ausnahmen.clear();
    }
}

/// **A `path_nul_terminated(p, n)` clause of a contract**: the two parameter names, with
/// the site of the clause behind them.
struct NulKlausel {
    zeiger: String,
    laenge: String,
    span: Span,
}

/// A bare name through parentheses, or `None`.
fn blanker_name(e: &Expr) -> Option<&str> {
    match &e.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() => Some(o.basis.text.as_str()),
        ExprArt::Klammer(i) => blanker_name(i),
        _ => None,
    }
}

/// Is this expression a call to `path_nul_terminated(p, n)` with two bare names? The last
/// path segment carries the name, so a qualified spelling answers the same way.
fn als_nulklausel(e: &Expr) -> Option<(String, String)> {
    let e = match &e.art {
        ExprArt::Klammer(i) => return als_nulklausel(i),
        ExprArt::Ruf(r) => r,
        _ => return None,
    };
    let name = e.heisst("path_nul_terminated");
    if !name || e.argumente.len() != 2 {
        return None;
    }
    Some((
        blanker_name(&e.argumente[0])?.to_string(),
        blanker_name(&e.argumente[1])?.to_string(),
    ))
}

fn klauseln_in_pred(p: &Pred, aus: &mut Vec<NulKlausel>) {
    match &p.art {
        PredArt::Vergleich(e) => {
            if let Some((zeiger, laenge)) = als_nulklausel(e) {
                aus.push(NulKlausel { zeiger, laenge, span: e.span });
            }
        }
        PredArt::Klammer(i) => klauseln_in_pred(i, aus),
        PredArt::Und(a, b) => {
            klauseln_in_pred(a, aus);
            klauseln_in_pred(b, aus);
        }
        // `or`, `not`, `=>`, quantifiers: no obligation that holds on every path.
        _ => {}
    }
}

/// **Every NUL obligation a contract states** -- read through conjunctions only, the same
/// cut `rahmenlaenge::bounds` makes for the length bound.
fn nul_klauseln(preds: &[Pred]) -> Vec<NulKlausel> {
    let mut aus = Vec::new();
    for p in preds {
        klauseln_in_pred(p, &mut aus);
    }
    aus
}

/// Every call inside an expression, however nested.
fn rufe_in_expr<'a>(e: &'a Expr, aus: &mut Vec<&'a Ruf>) {
    if let ExprArt::Ruf(r) = &e.art {
        aus.push(r);
    }
    for u in crate::unterausdruecke(e) {
        rufe_in_expr(u, aus);
    }
}

/// Is this spelling a byte array `[u8; _]` / `[i8; _]`? Only the direct spelling counts:
/// an alias may resolve to a byte, but the store discipline below reads cells, and a
/// cell of an opaque carrier is not a byte the program wrote.
fn ist_bytefeld(t: &TypExpr) -> bool {
    match t {
        TypExpr::Feld(a) => matches!(
            &a.element,
            TypExpr::Int(i)
                if matches!(i.wort, gabbro_syntax::kw::Kw::U8 | gabbro_syntax::kw::Kw::I8)
        ),
        _ => false,
    }
}

/// A tracked buffer from a declaration type and its initialiser, or `None` where the
/// shape is not a readable byte array (another element type, an unreadable length).
fn puffer_aus(
    u: &crate::umgebung::Umgebung,
    modul: &str,
    t: &TypExpr,
    wert: &Expr,
) -> Option<Puffer> {
    if !ist_bytefeld(t) {
        return None;
    }
    let TypExpr::Feld(a) = t else { return None };
    let laenge = u.konst_wert(modul, &a.laenge)?;
    if laenge < 0 {
        return None;
    }
    let voll = matches!(&wert.art, ExprArt::Zahl(0));
    Some(Puffer { laenge: laenge as u128, voll, ausnahmen: HashSet::new() })
}

struct Gaenger<'a> {
    u: &'a crate::umgebung::Umgebung,
    modul: &'a str,
    rufer: String,
    params: HashSet<String>,
    klauseln: Vec<NulKlausel>,
    puffer: HashMap<String, Puffer>,
    absagen: &'a mut Absagen,
}

impl<'a> Gaenger<'a> {
    /// Check every call inside one expression against the NUL obligations of its callee.
    fn pruefe_rufe_in_expr(&mut self, e: &Expr) {
        let mut rufe = Vec::new();
        rufe_in_expr(e, &mut rufe);
        for r in rufe {
            self.ruf_pruefen(r);
        }
    }

    /// Check every call inside the index expressions of one place.
    fn pruefe_rufe_in_ort(&mut self, o: &Ort) {
        for e in crate::ausdruecke_im_ort(o) {
            self.pruefe_rufe_in_expr(e);
        }
    }

    /// A call may write through every buffer it takes: kill the cells of each tracked
    /// array passed as a bare argument to any call inside these expressions.
    fn toete_fuer_expr(&mut self, e: &Expr) {
        let mut rufe = Vec::new();
        rufe_in_expr(e, &mut rufe);
        for r in rufe {
            self.toete_fuer_ruf(r);
        }
    }

    fn toete_fuer_ruf(&mut self, r: &Ruf) {
        for a in &r.argumente {
            if let Some(n) = blanker_name(a) {
                if let Some(p) = self.puffer.get_mut(n) {
                    p.toete();
                }
            }
        }
    }

    /// Process one store to a tracked buffer: `buf[k] = v` with `op`.
    ///
    /// Under `bedingt` (a branch, a loop, an error continuation) a store may not run, so
    /// it never proves -- but it may overwrite, so it still kills, except for a
    /// maybe-`0` over any cell, which changes nothing either way.
    fn speichere(
        &mut self,
        basis: &str,
        suffixe: &[OrtSuffix],
        wertc: Option<i128>,
        op: &ZuwOp,
        bedingt: bool,
    ) {
        let [OrtSuffix::Index(k)] = suffixe else {
            // A bare rebinding, a field suffix, `->`, several suffixes: the whole
            // object may have moved.
            if let Some(p) = self.puffer.get_mut(basis) {
                p.toete();
            }
            return;
        };
        let kk = self.u.konst_wert(self.modul, k).filter(|n| *n >= 0).map(|n| n as u128);
        let Some(p) = self.puffer.get_mut(basis) else { return };
        let Some(kk) = kk else {
            p.toete();
            return;
        };
        if kk >= p.laenge {
            // Past the object: another rule's case (`N463` at the bound, `M115`
            // elsewhere), not a cell this discipline reads.
            return;
        }
        if *op != ZuwOp::Setzt {
            // `+=` and kin read the cell and write it back: unknown afterwards.
            p.lege_unklar(kk);
            return;
        }
        if bedingt {
            if wertc != Some(0) {
                p.lege_unklar(kk);
            }
        } else if wertc == Some(0) {
            p.lege_null(kk);
        } else {
            p.lege_unklar(kk);
        }
    }

    /// **`N507` -- one call against the NUL obligations of its callee.**
    ///
    /// Three outcomes, and only the third is silent without proof: forwarding under the
    /// caller's own clause passes, a proved buffer passes, a caller parameter pair without
    /// the clause and an unproved buffer fall. A pointer this pass cannot see built keeps
    /// its named `V` obligation and nothing else.
    fn ruf_pruefen(&mut self, r: &Ruf) {
        let Some(pfad) = r.path() else { return };
        let Some(sig) = self.u.funktion(self.modul, pfad) else { return };
        let klauseln = nul_klauseln(&sig.requires);
        if klauseln.is_empty() {
            return;
        }
        let ziel = r.ziel.text();
        for k in &klauseln {
            let pos = |n: &str| sig.parameter.iter().position(|(pn, _)| pn == n);
            let (Some(ix), Some(ip)) = (pos(&k.laenge), pos(&k.zeiger)) else { continue };
            let (Some(al), Some(ap)) = (r.argumente.get(ix), r.argumente.get(ip)) else {
                continue;
            };
            let q = blanker_name(ap);
            let y = blanker_name(al);
            if let (Some(q), Some(y)) = (q, y) {
                if self.params.contains(q) && self.params.contains(y) {
                    if self.klauseln.iter().any(|e| e.zeiger == q && e.laenge == y) {
                        continue;
                    }
                    self.absagen.schiebe(
                        Absage::fehler(
                            "N507",
                            ap.span,
                            format!(
                                "`{}` forwards its parameters `{q}` and `{y}` into `{ziel}`, \
                                 and its own contract carries no \
                                 `path_nul_terminated({q}, {y})`",
                                self.rufer
                            ),
                        )
                        .mit_notiz(
                            "the NUL the gate is owed travels with the clause, or it travels \
                             with nobody: a wrapper that does not require the terminator \
                             cannot pass one on",
                        ),
                    );
                    continue;
                }
            }
            let Some(q) = q else {
                // A field, a computed pointer, a literal: no buffer this pass sees
                // built -- the named obligation stays, and nothing falls beside it.
                continue;
            };
            let Some(p) = self.puffer.get(q) else {
                // Not a caller parameter pair and not a tracked buffer (a lone
                // parameter, a foreign static): the `V` row stays, undecided here.
                continue;
            };
            let grund: Option<String> = match self.u.konst_wert(self.modul, al) {
                Some(l) if l < 1 || (l as u128) > p.laenge => None,
                Some(l) if p.ist_null((l as u128) - 1) => None,
                Some(l) => Some(format!(
                    "no store `{q}[{}] = 0` dominates this call -- the byte the gate \
                     reads is not proved to be a NUL",
                    (l as u128) - 1
                )),
                None if p.alle_null() => None,
                None => Some(format!(
                    "the length is no single constant and `{q}` is not an untouched \
                     zeroed buffer -- no index is proved to carry the NUL the gate reads"
                )),
            };
            if let Some(grund) = grund {
                self.absagen.schiebe(
                    Absage::fehler(
                        "N507",
                        ap.span,
                        format!(
                            "`{ziel}` requires `path_nul_terminated({}, {})` -- {grund}",
                            k.zeiger, k.laenge
                        ),
                    )
                    .mit_notiz(
                        "a kernel that finds the end of its data by a NUL reads past the \
                         frame unless the program put the terminator there -- the checker \
                         proves `buf[k] = 0` below the length, or the call stays a named \
                         obligation nowhere discharged",
                    )
                    .mit_notiz(
                        "proved today: a literal `0` store under straight-line code, an \
                         untouched zero-initialised buffer, a forwarded parameter pair \
                         under the caller's own clause. Branches, loops and computed \
                         lengths prove nothing here",
                    ),
                );
            }
        }
    }

    /// Walk one block. Under `bedingt` stores never prove (they may not run) but still
    /// kill (they may overwrite); straight-line stores do both.
    fn lauf(&mut self, block: &Block, bedingt: bool) {
        for s in &block.anweisungen {
            match &s.art {
                StmtArt::Let(l) => {
                    self.pruefe_rufe_in_expr(&l.wert);
                    self.toete_fuer_expr(&l.wert);
                    self.puffer.remove(&l.name.text);
                    if let Some(q) = blanker_name(&l.wert) {
                        if let Some(p) = self.puffer.get(q).cloned() {
                            // A copy carries the bytes: `let ab = buf;` tracks on.
                            self.puffer.insert(l.name.text.clone(), p);
                            continue;
                        }
                    }
                    if let Some(t) = &l.typ {
                        if let Some(p) = puffer_aus(self.u, self.modul, t, &l.wert) {
                            self.puffer.insert(l.name.text.clone(), p);
                        }
                    }
                }
                StmtArt::LetSonst(l) => {
                    if let LetQuelle::Ruf(r) = &l.quelle {
                        self.ruf_pruefen(r);
                        self.toete_fuer_ruf(r);
                    }
                    self.lauf(&l.sonst, true);
                }
                StmtArt::Zuweisung(z) => {
                    self.pruefe_rufe_in_expr(&z.wert);
                    for suffix in &z.ziel.suffixe {
                        if let OrtSuffix::Index(k) = suffix {
                            self.pruefe_rufe_in_expr(k);
                            self.toete_fuer_expr(k);
                        }
                    }
                    self.toete_fuer_expr(&z.wert);
                    let wertc = self.u.konst_wert(self.modul, &z.wert);
                    self.speichere(&z.ziel.basis.text, &z.ziel.suffixe, wertc, &z.op, bedingt);
                }
                StmtArt::Ruf(r) => {
                    self.ruf_pruefen(r);
                    self.toete_fuer_ruf(r);
                }
                StmtArt::Wenn(w) => {
                    for (bed, block) in &w.zweige {
                        self.pruefe_rufe_in_expr(bed);
                        self.toete_fuer_expr(bed);
                        self.lauf(block, true);
                    }
                    if let Some(s) = &w.sonst {
                        self.lauf(s, true);
                    }
                }
                StmtArt::Match(m) => {
                    self.pruefe_rufe_in_expr(&m.gegenstand);
                    self.toete_fuer_expr(&m.gegenstand);
                    for z in &m.zweige {
                        self.lauf(&z.rumpf, true);
                    }
                }
                StmtArt::Schleife(sch) => {
                    for e in crate::eigene_ausdruecke(s) {
                        self.pruefe_rufe_in_expr(e);
                        self.toete_fuer_expr(e);
                    }
                    for b in crate::unterbloecke(s) {
                        self.lauf(b, true);
                    }
                }
                StmtArt::Bricht(x) => self.lauf(&x.rumpf, bedingt),
                StmtArt::Narrow(x) => {
                    self.pruefe_rufe_in_ort(&x.ort);
                    self.lauf(&x.sonst, true);
                }
                StmtArt::Sperrt(x) => self.lauf(&x.rumpf, bedingt),
                StmtArt::Observiert(x) => self.lauf(&x.rumpf, bedingt),
                StmtArt::Publish(p) => {
                    self.pruefe_rufe_in_expr(&p.wert);
                    self.toete_fuer_expr(&p.wert);
                    let wertc = self.u.konst_wert(self.modul, &p.wert);
                    self.speichere(
                        &p.ziel.basis.text,
                        &p.ziel.suffixe,
                        wertc,
                        &ZuwOp::Setzt,
                        bedingt,
                    );
                }
                StmtArt::AwaitLoad(a) => {
                    self.pruefe_rufe_in_ort(&a.quelle);
                    self.puffer.remove(&a.name.text);
                }
                StmtArt::Exchange(e) => {
                    self.pruefe_rufe_in_ort(&e.ort);
                    match &e.form {
                        XForm::Vergleich { wert, .. } => self.pruefe_rufe_in_expr(wert),
                        XForm::Update { rumpf, .. } => self.lauf(rumpf, bedingt),
                    }
                    if let Some(p) = self.puffer.get_mut(e.ort.basis.text.as_str()) {
                        p.toete();
                    }
                }
                StmtArt::Return(e) => {
                    if let Some(e) = e {
                        self.pruefe_rufe_in_expr(e);
                    }
                }
                StmtArt::Alloc(a) => {
                    self.pruefe_rufe_in_expr(&a.wert);
                    self.toete_fuer_expr(&a.wert);
                    self.puffer.remove(&a.name.text);
                    self.lauf_opt(&a.sonst);
                }
                StmtArt::Grow(g) => {
                    self.pruefe_rufe_in_expr(&g.mehr);
                    self.lauf(&g.sonst, true);
                }
                StmtArt::Child(b) => self.lauf(b, true),
                // `leave`, `next`, `reset`, `start`: no blocks, no expressions.
                // A `@lib` call is refused by name elsewhere (`N057`); its contract
                // is not read here and its arguments are left alone with it.
                StmtArt::Leave(_)
                | StmtArt::Next(_)
                | StmtArt::ResetArena(_)
                | StmtArt::Start(_)
                | StmtArt::LibraryCall(_) => {}
            }
        }
    }

    fn lauf_opt(&mut self, b: &Option<Block>) {
        if let Some(b) = b {
            self.lauf(b, true);
        }
    }
}

/// **`N507` -- the NUL-terminator discipline** (lane 262, OFFEN O23; the rule in full
/// stands in this file's header).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut statik: HashMap<(String, String), Puffer> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Statisch(s) = &item.art {
            if let Some(p) = puffer_aus(&u, modul, &s.typ, &s.wert) {
                statik.insert((modul.to_string(), s.name.text.clone()), p);
            }
        }
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut puffer = HashMap::new();
        for ((m, n), p) in &statik {
            if m == modul {
                puffer.insert(n.clone(), p.clone());
            }
        }
        let mut g = Gaenger {
            u: &u,
            modul,
            rufer: f.name.text.clone(),
            params: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            klauseln: nul_klauseln(&f.requires),
            puffer,
            absagen,
        };
        g.lauf(b, false);
    });
}
