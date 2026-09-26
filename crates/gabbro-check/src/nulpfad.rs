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
/// `full` is the zero-initialised baseline (`= 0` with no store since): every index reads
/// `0` except `exceptions`, which read unknown. Without the baseline (`full == false`),
/// `exceptions` is the set of indices that provably read `0` instead. Either way the
/// representation stays small: no cell is ever materialised.
#[derive(Debug, Clone)]
struct NulBuffer {
    len: u128,
    full: bool,
    exceptions: HashSet<u128>,
}

impl NulBuffer {
    /// Does cell `k` provably read `0`?
    fn is_zero(&self, k: u128) -> bool {
        if self.full {
            !self.exceptions.contains(&k)
        } else {
            self.exceptions.contains(&k)
        }
    }

    /// Is every cell provably `0` (an untouched zeroed buffer)?
    fn all_zero(&self) -> bool {
        self.full && self.exceptions.is_empty()
    }

    /// Record `buf[k] = 0`.
    fn set_zero(&mut self, k: u128) {
        if self.full {
            self.exceptions.remove(&k);
        } else if k < self.len {
            self.exceptions.insert(k);
        }
    }

    /// Record `buf[k] = <not provably zero>`.
    fn set_unknown(&mut self, k: u128) {
        if self.full {
            if k < self.len {
                self.exceptions.insert(k);
            }
        } else {
            self.exceptions.remove(&k);
        }
    }

    /// A store no index is read from: every cell is unknown afterwards.
    fn kill(&mut self) {
        self.full = false;
        self.exceptions.clear();
    }
}

/// **A `path_nul_terminated(p, n)` clause of a contract**: the two parameter names, with
/// the site of the clause behind them.
struct NulClause {
    pointer: String,
    length: String,
    span: Span,
}

/// Is this expression a call to `path_nul_terminated(p, n)` with two bare names? The last
/// path segment carries the name, so a qualified spelling answers the same way.
fn as_nul_clause(e: &Expr) -> Option<(String, String)> {
    let e = match &e.art {
        ExprArt::Klammer(i) => return as_nul_clause(i),
        ExprArt::Ruf(r) => r,
        _ => return None,
    };
    let name = e.heisst("path_nul_terminated");
    if !name || e.argumente.len() != 2 {
        return None;
    }
    Some((
        crate::rahmenlaenge::bare_name(&e.argumente[0])?.to_string(),
        crate::rahmenlaenge::bare_name(&e.argumente[1])?.to_string(),
    ))
}

fn clauses_in_pred(p: &Pred, out: &mut Vec<NulClause>) {
    match &p.art {
        PredArt::Vergleich(e) => {
            if let Some((pointer, length)) = as_nul_clause(e) {
                out.push(NulClause { pointer, length, span: e.span });
            }
        }
        PredArt::Klammer(i) => clauses_in_pred(i, out),
        PredArt::Und(a, b) => {
            clauses_in_pred(a, out);
            clauses_in_pred(b, out);
        }
        // `or`, `not`, `=>`, quantifiers: no obligation that holds on every path.
        _ => {}
    }
}

/// **Every NUL obligation a contract states** -- read through conjunctions only, the same
/// cut `rahmenlaenge::bounds` makes for the length bound.
fn nul_clauses(preds: &[Pred]) -> Vec<NulClause> {
    let mut out = Vec::new();
    for p in preds {
        clauses_in_pred(p, &mut out);
    }
    out
}

/// Every call inside an expression, however nested.
fn calls_in_expr<'a>(e: &'a Expr, out: &mut Vec<&'a Ruf>) {
    if let ExprArt::Ruf(r) = &e.art {
        out.push(r);
    }
    for sub in crate::unterausdruecke(e) {
        calls_in_expr(sub, out);
    }
}

/// Is this spelling a byte array `[u8; _]` / `[i8; _]`? Only the direct spelling counts:
/// an alias may resolve to a byte, but the store discipline below reads cells, and a
/// cell of an opaque carrier is not a byte the program wrote.
fn is_byte_array(t: &TypExpr) -> bool {
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
fn buffer_from(
    u: &crate::umgebung::Umgebung,
    modul: &str,
    t: &TypExpr,
    wert: &Expr,
) -> Option<NulBuffer> {
    if !is_byte_array(t) {
        return None;
    }
    let TypExpr::Feld(a) = t else { return None };
    let len = u.konst_wert(modul, &a.laenge)?;
    if len < 0 {
        return None;
    }
    let full = matches!(&wert.art, ExprArt::Zahl(0));
    Some(NulBuffer { len: len as u128, full, exceptions: HashSet::new() })
}

struct Walker<'a> {
    u: &'a crate::umgebung::Umgebung,
    modul: &'a str,
    caller: String,
    params: HashSet<String>,
    clauses: Vec<NulClause>,
    buffers: HashMap<String, NulBuffer>,
    absagen: &'a mut Absagen,
}

impl<'a> Walker<'a> {
    /// Check every call inside one expression against the NUL obligations of its callee.
    fn check_calls_in_expr(&mut self, e: &Expr) {
        let mut rufe = Vec::new();
        calls_in_expr(e, &mut rufe);
        for r in rufe {
            self.check_call(r);
        }
    }

    /// Check every call inside the index expressions of one place.
    fn check_calls_in_place(&mut self, o: &Ort) {
        for e in crate::ausdruecke_im_ort(o) {
            self.check_calls_in_expr(e);
        }
    }

    /// A call may write through every buffer it takes: kill the cells of each tracked
    /// array passed as a bare argument to any call inside these expressions.
    fn kill_for_expr(&mut self, e: &Expr) {
        let mut rufe = Vec::new();
        calls_in_expr(e, &mut rufe);
        for r in rufe {
            self.kill_for_call(r);
        }
    }

    fn kill_for_call(&mut self, r: &Ruf) {
        for a in &r.argumente {
            if let Some(n) = crate::rahmenlaenge::bare_name(a) {
                if let Some(p) = self.buffers.get_mut(n) {
                    p.kill();
                }
            }
        }
    }

    /// Process one store to a tracked buffer: `buf[k] = v` with `op`.
    ///
    /// Under `conditional` (a branch, a loop, an error continuation) a store may not run, so
    /// it never proves -- but it may overwrite, so it still kills, except for a
    /// maybe-`0` over any cell, which changes nothing either way.
    fn record_store(
        &mut self,
        basis: &str,
        suffixe: &[OrtSuffix],
        const_val: Option<i128>,
        op: &ZuwOp,
        conditional: bool,
    ) {
        let [OrtSuffix::Index(k)] = suffixe else {
            // A bare rebinding, a field suffix, `->`, several suffixes: the whole
            // object may have moved.
            if let Some(p) = self.buffers.get_mut(basis) {
                p.kill();
            }
            return;
        };
        let kk = self.u.konst_wert(self.modul, k).filter(|n| *n >= 0).map(|n| n as u128);
        let Some(p) = self.buffers.get_mut(basis) else { return };
        let Some(kk) = kk else {
            p.kill();
            return;
        };
        if kk >= p.len {
            // Past the object: another rule's case (`N463` at the bound, `M115`
            // elsewhere), not a cell this discipline reads.
            return;
        }
        if *op != ZuwOp::Setzt {
            // `+=` and kin read the cell and write it back: unknown afterwards.
            p.set_unknown(kk);
            return;
        }
        if conditional {
            if const_val != Some(0) {
                p.set_unknown(kk);
            }
        } else if const_val == Some(0) {
            p.set_zero(kk);
        } else {
            p.set_unknown(kk);
        }
    }

    /// **`N507` -- one call against the NUL obligations of its callee.**
    ///
    /// Three outcomes, and only the third is silent without proof: forwarding under the
    /// caller's own clause passes, a proved buffer passes, a caller parameter pair without
    /// the clause and an unproved buffer fall. A pointer this pass cannot see built keeps
    /// its named `V` obligation and nothing else.
    fn check_call(&mut self, r: &Ruf) {
        let Some(path) = r.path() else { return };
        let Some(sig) = self.u.funktion(self.modul, path) else { return };
        let clauses = nul_clauses(&sig.requires);
        if clauses.is_empty() {
            return;
        }
        let target = r.ziel.text();
        for k in &clauses {
            let pos = |n: &str| sig.parameter.iter().position(|(pn, _)| pn == n);
            let (Some(ix), Some(ip)) = (pos(&k.length), pos(&k.pointer)) else { continue };
            let (Some(al), Some(ap)) = (r.argumente.get(ix), r.argumente.get(ip)) else {
                continue;
            };
            let q = crate::rahmenlaenge::bare_name(ap);
            let y = crate::rahmenlaenge::bare_name(al);
            if let (Some(q), Some(y)) = (q, y) {
                if self.params.contains(q) && self.params.contains(y) {
                    if self.clauses.iter().any(|e| e.pointer == q && e.length == y) {
                        continue;
                    }
                    self.absagen.schiebe(
                        Absage::fehler(
                            "N507",
                            ap.span,
                            format!(
                                "`{}` forwards its parameters `{q}` and `{y}` into `{target}`, \
                                 and its own contract carries no \
                                 `path_nul_terminated({q}, {y})`",
                                self.caller
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
            let Some(p) = self.buffers.get(q) else {
                // Not a caller parameter pair and not a tracked buffer (a lone
                // parameter, a foreign static): the `V` row stays, undecided here.
                continue;
            };
            let reason: Option<String> = match self.u.konst_wert(self.modul, al) {
                Some(l) if l < 1 || (l as u128) > p.len => None,
                Some(l) if p.is_zero((l as u128) - 1) => None,
                Some(l) => Some(format!(
                    "no store `{q}[{}] = 0` dominates this call -- the byte the gate \
                     reads is not proved to be a NUL",
                    (l as u128) - 1
                )),
                None if p.all_zero() => None,
                None => Some(format!(
                    "the length is no single constant and `{q}` is not an untouched \
                     zeroed buffer -- no index is proved to carry the NUL the gate reads"
                )),
            };
            if let Some(reason) = reason {
                self.absagen.schiebe(
                    Absage::fehler(
                        "N507",
                        ap.span,
                        format!(
                            "`{target}` requires `path_nul_terminated({}, {})` -- {reason}",
                            k.pointer, k.length
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

    /// Walk one block. Under `conditional` stores never prove (they may not run) but still
    /// kill (they may overwrite); straight-line stores do both.
    fn walk(&mut self, block: &Block, conditional: bool) {
        for s in &block.anweisungen {
            match &s.art {
                StmtArt::Let(l) => {
                    self.check_calls_in_expr(&l.wert);
                    self.kill_for_expr(&l.wert);
                    self.buffers.remove(&l.name.text);
                    if let Some(q) = crate::rahmenlaenge::bare_name(&l.wert) {
                        if let Some(p) = self.buffers.get(q).cloned() {
                            // A copy carries the bytes: `let ab = buf;` tracks on.
                            self.buffers.insert(l.name.text.clone(), p);
                            continue;
                        }
                    }
                    if let Some(t) = &l.typ {
                        if let Some(p) = buffer_from(self.u, self.modul, t, &l.wert) {
                            self.buffers.insert(l.name.text.clone(), p);
                        }
                    }
                }
                StmtArt::LetSonst(l) => {
                    if let LetQuelle::Ruf(r) = &l.quelle {
                        self.check_call(r);
                        self.kill_for_call(r);
                    }
                    self.walk(&l.sonst, true);
                }
                StmtArt::Zuweisung(z) => {
                    self.check_calls_in_expr(&z.wert);
                    for suffix in &z.ziel.suffixe {
                        if let OrtSuffix::Index(k) = suffix {
                            self.check_calls_in_expr(k);
                            self.kill_for_expr(k);
                        }
                    }
                    self.kill_for_expr(&z.wert);
                    let const_val = self.u.konst_wert(self.modul, &z.wert);
                    self.record_store(&z.ziel.basis.text, &z.ziel.suffixe, const_val, &z.op, conditional);
                }
                StmtArt::Ruf(r) => {
                    self.check_call(r);
                    self.kill_for_call(r);
                }
                StmtArt::Wenn(w) => {
                    for (cond, block) in &w.zweige {
                        self.check_calls_in_expr(cond);
                        self.kill_for_expr(cond);
                        self.walk(block, true);
                    }
                    if let Some(s) = &w.sonst {
                        self.walk(s, true);
                    }
                }
                StmtArt::Match(m) => {
                    self.check_calls_in_expr(&m.gegenstand);
                    self.kill_for_expr(&m.gegenstand);
                    for z in &m.zweige {
                        self.walk(&z.rumpf, true);
                    }
                }
                StmtArt::Schleife(sch) => {
                    for e in crate::eigene_ausdruecke(s) {
                        self.check_calls_in_expr(e);
                        self.kill_for_expr(e);
                    }
                    for b in crate::unterbloecke(s) {
                        self.walk(b, true);
                    }
                }
                StmtArt::Bricht(x) => self.walk(&x.rumpf, conditional),
                StmtArt::Narrow(x) => {
                    self.check_calls_in_place(&x.ort);
                    self.walk(&x.sonst, true);
                }
                StmtArt::Sperrt(x) => self.walk(&x.rumpf, conditional),
                StmtArt::Observiert(x) => self.walk(&x.rumpf, conditional),
                StmtArt::Publish(p) => {
                    self.check_calls_in_expr(&p.wert);
                    self.kill_for_expr(&p.wert);
                    let const_val = self.u.konst_wert(self.modul, &p.wert);
                    self.record_store(
                        &p.ziel.basis.text,
                        &p.ziel.suffixe,
                        const_val,
                        &ZuwOp::Setzt,
                        conditional,
                    );
                }
                StmtArt::AwaitLoad(a) => {
                    self.check_calls_in_place(&a.quelle);
                    self.buffers.remove(&a.name.text);
                }
                StmtArt::Exchange(e) => {
                    self.check_calls_in_place(&e.ort);
                    match &e.form {
                        XForm::Vergleich { wert, .. } => self.check_calls_in_expr(wert),
                        XForm::Update { rumpf, .. } => self.walk(rumpf, conditional),
                    }
                    if let Some(p) = self.buffers.get_mut(e.ort.basis.text.as_str()) {
                        p.kill();
                    }
                }
                StmtArt::Return(e) => {
                    if let Some(e) = e {
                        self.check_calls_in_expr(e);
                    }
                }
                StmtArt::Alloc(a) => {
                    self.check_calls_in_expr(&a.wert);
                    self.kill_for_expr(&a.wert);
                    self.buffers.remove(&a.name.text);
                    self.walk_opt(&a.sonst);
                }
                StmtArt::Grow(g) => {
                    self.check_calls_in_expr(&g.mehr);
                    self.walk(&g.sonst, true);
                }
                StmtArt::Child(b) => self.walk(b, true),
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

    fn walk_opt(&mut self, b: &Option<Block>) {
        if let Some(b) = b {
            self.walk(b, true);
        }
    }
}

/// **`N507` -- the NUL-terminator discipline** (lane 262, OFFEN O23; the rule in full
/// stands in this file's header).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut statics: HashMap<(String, String), NulBuffer> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Statisch(s) = &item.art {
            if let Some(p) = buffer_from(&u, modul, &s.typ, &s.wert) {
                statics.insert((modul.to_string(), s.name.text.clone()), p);
            }
        }
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut buffers = HashMap::new();
        for ((m, n), p) in &statics {
            if m == modul {
                buffers.insert(n.clone(), p.clone());
            }
        }
        let mut g = Walker {
            u: &u,
            modul,
            caller: f.name.text.clone(),
            params: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            clauses: nul_clauses(&f.requires),
            buffers,
            absagen,
        };
        g.walk(b, false);
    });
}
