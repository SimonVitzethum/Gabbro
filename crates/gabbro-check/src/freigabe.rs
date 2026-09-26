//! **O12: the release obligation, STATED in the obligation channels** (`gabbro obligations
//! --g` and `gabbro counterexample`) **and DISCHARGED by the checker** (`N511` in
//! `freigabe_pruef.rs`). One analysis, shared by all three since lane 263 (fix lane F7,
//! review G02 F3, 2026-09-22, had shared it between the two channels); it stood twice until
//! then, byte-for-byte apart from the wording, and every repair had to land twice.
//!
//! At every `locks L { … }` exit the lock invariant of `L` must hold again. The verdict per
//! exit is [`beurteile`]: the invariant FOLLOWS from the invariant at acquire (the frame:
//! what no write in the section may have touched), the section's own direct writes, and
//! what the section's callees PROMISE (their `ensures`), never their bodies -- contracts
//! are the interface. What cannot be shown is refused with `N511`; the rows below state
//! the same verdict per section as Lean comments.
//!
//! ## The reading (SYNTACTIC, one-sided, and since F7 ORDER-AWARE;
//! ## since lane 263 ENTAILMENT-AWARE)
//!
//! It collects the slot cells (`T.slots[i].f`, index included) the invariant reads, splits
//! the invariant at the top-level `&&` into conjuncts, then walks the section in execution
//! order carrying equality facts between cells and constants.
//!
//! * An unconditional direct call of a uniquely declared callee first KILLS every cell of a
//!   table the callee's `effects` write (its `writes`/`consumes`/`publishes`, and all cells when
//!   the callee has no written `effects` or writes through something that is not a declared
//!   carrier), then ADDS the equalities its `ensures` states (`cell == cell`, `cell ==
//!   const`), with callee parameters substituted by constant arguments where they resolve.
//!   Only the call a statement makes last (the statement call, the `let` value, the
//!   right-hand side of an assignment) promises; a call nested in an argument or an
//!   operand only kills.
//! * An unconditional direct write `cell = <const>` (`=`, not `+=` and friends) ESTABLISHES
//!   `cell == <const>`; any other direct write (`publishes`, `exchange`, `alloc`, `reset`,
//!   `grow`, compound assignment) kills without establishing. A LATER promise
//!   re-establishes; nothing else does.
//! * A named `const` reads as its value, and an unconditional `let x = <const>` binds it.
//! * A place through a `ptr` parameter names its carrier: `k.slots[0].x` with
//!   `k : ptr<normal, rw> A` IS `A.slots[0].x`, for kills, promises and facts alike.
//!   (Before lane 263 such a write killed everything and promised nothing countable, so
//!   `beispiele/119` -- whose whole point is re-establishing its bound through `k` -- read
//!   UNPROVED. That was the false positive lane 204 measured.)
//! * Everything under a branch, a loop, a `narrow`, a `let … else`, a `child` or an `exchange`
//!   update is conditional: its calls NEVER promise and its writes never establish (each is
//!   named in the row), while its kills still count.
//! * A `locks` and an `observes` body are brackets, not branches: walked in line.
//! * An exit (`return`, `leave`, `next`) inside the section is a release too: the conjuncts
//!   owed there are checked at that point.
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
//! * `RELEASE HOLDS (syntactic)` -- at every exit each conjunct of the invariant follows
//!   from the acquire frame, the section's direct writes and the callees' `ensures`
//!   equalities, with no uncounted call in the section. This is NOT a proof (inequality
//!   promises beyond constants, arithmetic between promised cells, aliasing beyond declared
//!   carriers and pointer parameters, and transitive promises through more than equality
//!   are all beyond this text), only the absence of a syntactic gap.
//! * `RELEASE UNPROVED` -- the exact gap: conjuncts no callee promises and no write
//!   establishes, cells written after their last promise, early exits, and calls whose
//!   promise cannot be counted.
//!
//! A missed form stays on the obliging side: an unknown expression shape contributes no fact,
//! and every statement shape is walked (`crate::unterbloecke`, exhaustive).

use gabbro_syntax::ast::*;
use gabbro_syntax::span::Span;

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
///
/// `params` maps a `ptr` parameter to its carrier: `k.slots[0].x` with `k : ptr<…> A`
/// names `A.slots[0].x`. Any other bound name (a quantifier variable, a scalar parameter)
/// as the basis names nothing countable.
fn als_schlitz(
    o: &Ort,
    gebunden: &BTreeSet<String>,
    params: &BTreeMap<String, String>,
) -> Option<String> {
    match o.suffixe.as_slice() {
        [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)]
            if slots.text == "slots" =>
        {
            let basis = match params.get(&o.basis.text) {
                Some(t) => t.clone(),
                None if gebunden.contains(&o.basis.text) => return None,
                None => o.basis.text.clone(),
            };
            Some(format!("{}.slots{}.{}", basis, index_text(i, gebunden), f.text))
        }
        _ => None,
    }
}

/// Slot cells read by an expression (no `old`: it promises nothing about the release state).
fn zellen_expr(e: &Expr, gebunden: &BTreeSet<String>, params: &BTreeMap<String, String>, acc: &mut BTreeSet<String>) {
    match &e.art {
        ExprArt::Ort(o) => {
            if let Some(z) = als_schlitz(o, gebunden, params) {
                acc.insert(z);
            }
        }
        ExprArt::Alt(_) => {}
        ExprArt::Klammer(x) => zellen_expr(x, gebunden, params, acc),
        ExprArt::Unaer(_, x) => zellen_expr(x, gebunden, params, acc),
        ExprArt::Binaer(_, a, b) => {
            zellen_expr(a, gebunden, params, acc);
            zellen_expr(b, gebunden, params, acc);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                zellen_expr(a, gebunden, params, acc);
            }
        }
        ExprArt::LibraryCall(r) => {
            for a in &r.args {
                zellen_expr(a, gebunden, params, acc);
            }
        }
        ExprArt::Eingebaut(b) => match &**b {
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                if let Some(z) = als_schlitz(o, gebunden, params) {
                    acc.insert(z);
                }
            }
            Eingebaut::Aligned(a, b) => {
                zellen_expr(a, gebunden, params, acc);
                zellen_expr(b, gebunden, params, acc);
            }
            Eingebaut::Sizeof(TypOderOrt::Typ(_)) | Eingebaut::Lenof(TypOderOrt::Typ(_)) => {}
        },
        ExprArt::Zaehle { variable, rumpf, .. } => {
            let mut innen = gebunden.clone();
            innen.insert(variable.text.clone());
            zellen_pred(rumpf, &innen, params, acc);
        }
        ExprArt::ArrayLit(es) => {
            for x in es {
                zellen_expr(x, gebunden, params, acc);
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
fn zellen_pred(p: &Pred, gebunden: &BTreeSet<String>, params: &BTreeMap<String, String>, acc: &mut BTreeSet<String>) {
    match &p.art {
        PredArt::Vergleich(e) => zellen_expr(e, gebunden, params, acc),
        PredArt::Quantor(q) => {
            let mut innen = gebunden.clone();
            innen.insert(q.variable.text.clone());
            zellen_pred(&q.rumpf, &innen, params, acc);
        }
        PredArt::Element(e, _) => zellen_expr(e, gebunden, params, acc),
        PredArt::Erreicht { von, nach, .. } => {
            for o in [von, nach] {
                if let Some(z) = als_schlitz(o, gebunden, params) {
                    acc.insert(z);
                }
            }
        }
        PredArt::Held { .. } => {}
        PredArt::Klammer(q) => zellen_pred(q, gebunden, params, acc),
        PredArt::Nicht(q) => zellen_pred(q, gebunden, params, acc),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            zellen_pred(a, gebunden, params, acc);
            zellen_pred(b, gebunden, params, acc);
        }
    }
}

/// A value the release reading can name: a constant or a slot cell.
/// Anything else (`old`, a call, a non-constant computation) is `Weg`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Norm {
    Zahl(i128),
    Zelle(String),
    Weg,
}

/// The constant expression `e` denotes, or `Weg`. `params` maps a `ptr` parameter to its
/// carrier, `subst` a callee parameter to the caller's value for it, `lokal` a `let`
/// binding to its constant value, `konstanten` a named `const` to its value.
fn norm_expr(
    e: &Expr,
    gebunden: &BTreeSet<String>,
    params: &BTreeMap<String, String>,
    subst: &BTreeMap<String, Norm>,
    lokal: &BTreeMap<String, i128>,
    konstanten: &BTreeMap<String, i128>,
) -> Norm {
    match &e.art {
        ExprArt::Zahl(n) => Norm::Zahl(*n as i128),
        ExprArt::Klammer(x) => norm_expr(x, gebunden, params, subst, lokal, konstanten),
        ExprArt::Ort(o) => {
            if o.suffixe.is_empty() {
                if let Some(n) = subst.get(&o.basis.text) {
                    return n.clone();
                }
                if let Some(n) = lokal.get(&o.basis.text) {
                    return Norm::Zahl(*n);
                }
                if let Some(n) = konstanten.get(&o.basis.text) {
                    return Norm::Zahl(*n);
                }
                return Norm::Weg;
            }
            match als_schlitz(o, gebunden, params) {
                Some(z) if z.contains(UNZAEHLBAR) => Norm::Weg,
                Some(z) => Norm::Zelle(z),
                None => Norm::Weg,
            }
        }
        ExprArt::Unaer(UnOp::Negativ, x) => {
            match norm_expr(x, gebunden, params, subst, lokal, konstanten) {
                Norm::Zahl(n) => Norm::Zahl(n.saturating_neg()),
                _ => Norm::Weg,
            }
        }
        ExprArt::Binaer(op, a, b) => {
            let l = norm_expr(a, gebunden, params, subst, lokal, konstanten);
            let r = norm_expr(b, gebunden, params, subst, lokal, konstanten);
            match (op, l, r) {
                (BinOp::Plus, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x.saturating_add(y)),
                (BinOp::Minus, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x.saturating_sub(y)),
                (BinOp::Mal, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x.saturating_mul(y)),
                (BinOp::Geteilt, Norm::Zahl(x), Norm::Zahl(y)) if y != 0 => {
                    Norm::Zahl(x.saturating_div(y))
                }
                (BinOp::Rest, Norm::Zahl(x), Norm::Zahl(y)) if y != 0 => Norm::Zahl(x % y),
                (BinOp::SchiebLinks, Norm::Zahl(x), Norm::Zahl(y))
                    if (0..127).contains(&y) =>
                {
                    Norm::Zahl(x.saturating_mul(1i128 << y))
                }
                (BinOp::SchiebRechts, Norm::Zahl(x), Norm::Zahl(y))
                    if (0..127).contains(&y) =>
                {
                    Norm::Zahl(x >> y)
                }
                (BinOp::BitUnd, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x & y),
                (BinOp::BitOder, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x | y),
                (BinOp::BitXor, Norm::Zahl(x), Norm::Zahl(y)) => Norm::Zahl(x ^ y),
                _ => Norm::Weg,
            }
        }
        _ => Norm::Weg,
    }
}

/// The carrier a parameter points at, if it is a pointer at a declared carrier.
fn traeger_von_typ(t: &TypExpr, traeger: &BTreeSet<String>) -> Option<String> {
    match t {
        TypExpr::Zeiger(p) => traeger_von_typ(&p.ziel, traeger),
        TypExpr::Pfad(p) if p.teile.len() == 1 && traeger.contains(&p.teile[0].text) => {
            Some(p.teile[0].text.clone())
        }
        _ => None,
    }
}

/// `ptr` parameters of `f`, mapped to their carriers.
fn param_traeger(f: &FnDecl, traeger: &BTreeSet<String>) -> BTreeMap<String, String> {
    let mut aus = BTreeMap::new();
    for p in &f.parameter {
        if let Some(t) = traeger_von_typ(&p.typ, traeger) {
            aus.insert(p.name.text.clone(), t);
        }
    }
    aus
}

/// One `&&`-conjunct of a lock invariant, with the cells it reads.
struct Konjunkt {
    pred: Pred,
    zellen: BTreeSet<String>,
    traeger: BTreeSet<String>,
    unzaehlbar: bool,
}

fn konjunkte(inv: &Pred) -> Vec<Konjunkt> {
    fn sammle(p: &Pred, acc: &mut Vec<Pred>) {
        match &p.art {
            PredArt::Und(a, b) => {
                sammle(a, acc);
                sammle(b, acc);
            }
            PredArt::Klammer(q) => sammle(q, acc),
            _ => acc.push(p.clone()),
        }
    }
    let leer_params = BTreeMap::new();
    let mut rohe = Vec::new();
    sammle(inv, &mut rohe);
    rohe
        .into_iter()
        .map(|pred| {
            let mut zellen = BTreeSet::new();
            zellen_pred(&pred, &BTreeSet::new(), &leer_params, &mut zellen);
            let unzaehlbar = zellen.iter().any(|z| z.contains(UNZAEHLBAR));
            let traeger = zellen
                .iter()
                .filter(|z| !z.contains(UNZAEHLBAR))
                .filter_map(|z| z.split('.').next().map(|s| s.to_string()))
                .collect();
            Konjunkt { pred, zellen, traeger, unzaehlbar }
        })
        .collect()
}

/// What a write reaches: the cells of named tables, or anything at all.
#[derive(Clone)]
enum Toetet {
    Tabellen(BTreeSet<String>),
    Alles,
}

/// One callee as the rows count it.
#[derive(Clone)]
struct Gerufener {
    /// Promised cells (countable ones only), for the row text.
    verspricht: BTreeSet<String>,
    /// What its declared effects may write.
    toetet: Toetet,
    /// Its `ensures` clauses, for the equality facts.
    ensures: Vec<Pred>,
    /// Its parameter names, in order (for argument substitution).
    parameter: Vec<String>,
    /// Its `ptr` parameters, mapped to their carriers.
    param_traeger: BTreeMap<String, String>,
}

/// The whole-program facts the rows are read against.
struct Welt {
    /// Short name -> callee; `None` when declared twice (ambiguous).
    gerufene: BTreeMap<String, Option<Gerufener>>,
    /// Every declared carrier name (tables, statics, atomics, arenas, …): a write to one of
    /// them reaches that carrier and no other.
    traeger: BTreeSet<String>,
    /// Every named `const` with a plain numeric value.
    konstanten: BTreeMap<String, i128>,
}

/// The table a place writes, or `Alles` when the place is no declared carrier.
/// `params` maps the enclosing function's `ptr` parameters to their carriers.
fn ziel_toetet(o: &Ort, welt: &Welt, params: &BTreeMap<String, String>) -> Toetet {
    let basis = params.get(&o.basis.text).cloned().unwrap_or(o.basis.text.clone());
    if welt.traeger.contains(&basis) {
        Toetet::Tabellen(BTreeSet::from([basis]))
    } else if o.suffixe.is_empty() {
        // A bare local (or parameter) re-bound: it writes no carrier.
        Toetet::Tabellen(BTreeSet::new())
    } else {
        Toetet::Alles
    }
}

/// Whether a place names exactly one cell: every index is a literal.
/// Only such a write establishes (or precisely kills) a fact; anything else
/// may alias and kills at carrier level.
fn ort_exakt(o: &Ort) -> bool {
    fn index_exakt(e: &Expr) -> bool {
        match &e.art {
            ExprArt::Zahl(_) => true,
            ExprArt::Klammer(x) => index_exakt(x),
            _ => false,
        }
    }
    o.suffixe.iter().all(|s| match s {
        OrtSuffix::Index(e) => index_exakt(e),
        _ => true,
    })
}

/// The normalized slot cell a place writes, if it writes exactly one.
fn ziel_zelle(
    o: &Ort,
    gebunden: &BTreeSet<String>,
    params: &BTreeMap<String, String>,
) -> Option<String> {
    match als_schlitz(o, gebunden, params) {
        Some(z) if !z.contains(UNZAEHLBAR) => Some(z),
        _ => None,
    }
}

/// The state of one walk over one section.
struct Lauf<'w> {
    welt: &'w Welt,
    /// The cells the invariant reads.
    braucht: BTreeSet<String>,
    /// The invariant's `&&`-conjuncts, decided one by one.
    konjunkte: Vec<Konjunkt>,
    /// The enclosing function's `ptr` parameters, mapped to their carriers.
    params: BTreeMap<String, String>,
    /// Cells promised at this point (for the row text).
    hat: BTreeSet<String>,
    /// Promised cells killed since their promise, with what killed them.
    getoetet: BTreeMap<String, String>,
    /// Permanent reasons (conditional or uncountable calls, early exits).
    gruende: Vec<String>,
    /// Unconditional promising calls in order, for the row text.
    rufer: Vec<String>,
    /// Equality facts between cells and constants, in walk order.
    fakten: Vec<(Norm, Norm)>,
    /// Carriers the section may have written (directly or through a callee).
    beruehrt_traeger: BTreeSet<String>,
    /// Everything may have been written (indirect, unknown or library call).
    alles_beruehrt: bool,
    /// `let` bindings with a constant value, in scope at this point.
    lokal: BTreeMap<String, i128>,
    /// One verdict per exit, in walk order; the final `release` is appended last.
    ausgaenge: Vec<Ausgang>,
}

/// One exit of a locked section: the release, or an early `return`/`leave`/`next`.
pub(crate) struct Ausgang {
    pub art: String,
    pub span: Span,
    /// Empty when the invariant follows at this exit; otherwise one entry per
    /// conjunct that does not.
    pub fehlt: Vec<String>,
}

/// The shared verdict over one `locks L { … }` section, read by the obligation
/// rows AND by the `N511` refusal -- one analysis, one verdict.
pub(crate) struct AbschnittUrteil {
    pub funktion: String,
    pub sperre: String,
    pub braucht: BTreeSet<String>,
    pub rufer: Vec<String>,
    pub gruende: Vec<String>,
    pub ausgaenge: Vec<Ausgang>,
}

impl AbschnittUrteil {
    pub fn haelt(&self) -> bool {
        self.ausgaenge.iter().all(|a| a.fehlt.is_empty())
    }
}

/// The source-near text of an invariant conjunct, for refusal messages.
/// Best effort over the decidable shapes; anything else names its cells.
fn vergleich_text(p: &Pred, zellen: &BTreeSet<String>) -> String {
    fn ort_text(o: &Ort) -> String {
        let leer = BTreeSet::new();
        let mut s = o.basis.text.clone();
        for suffix in &o.suffixe {
            match suffix {
                OrtSuffix::Feld(i) => {
                    s.push('.');
                    s.push_str(&i.text);
                }
                OrtSuffix::Ueber(i) => {
                    s.push_str("->");
                    s.push_str(&i.text);
                }
                OrtSuffix::Index(e) => s.push_str(&index_text(e, &leer)),
            }
        }
        s
    }
    fn expr_text(e: &Expr) -> Option<String> {
        match &e.art {
            ExprArt::Zahl(n) => Some(format!("{n}")),
            ExprArt::Ort(o) => Some(ort_text(o)),
            ExprArt::Klammer(x) => expr_text(x),
            ExprArt::Binaer(op, a, b) => {
                let m = match op {
                    BinOp::Gleich => "==",
                    BinOp::Ungleich => "!=",
                    BinOp::Kleiner => "<",
                    BinOp::KleinerGleich => "<=",
                    BinOp::Groesser => ">",
                    BinOp::GroesserGleich => ">=",
                    BinOp::Plus => "+",
                    BinOp::Minus => "-",
                    BinOp::Mal => "*",
                    BinOp::Geteilt => "/",
                    BinOp::Rest => "%",
                    _ => return None,
                };
                Some(format!("{} {m} {}", expr_text(a)?, expr_text(b)?))
            }
            _ => None,
        }
    }
    match &p.art {
        PredArt::Vergleich(e) => match expr_text(e) {
            Some(t) => format!("`{t}`"),
            None => format!("the invariant clause over {{{}}}", zellen.iter().cloned().collect::<Vec<_>>().join(", ")),
        },
        _ => format!("the invariant clause over {{{}}}", zellen.iter().cloned().collect::<Vec<_>>().join(", ")),
    }
}

impl Lauf<'_> {
    /// An equality fact both sides name (cells or constants only).
    fn merke_gleich(&mut self, a: Norm, b: Norm) {
        match (&a, &b) {
            (Norm::Zahl(_), Norm::Zahl(_))
            | (Norm::Zahl(_), Norm::Zelle(_))
            | (Norm::Zelle(_), Norm::Zahl(_))
            | (Norm::Zelle(_), Norm::Zelle(_)) => self.fakten.push((a, b)),
            _ => {}
        }
    }

    /// A kill. `exakt` names the one cell a literal-index direct write touches:
    /// only facts about that cell die, while facts about its siblings survive.
    /// Every other kill (callees, computed indices, unknown places) may alias
    /// and kills every fact of the carrier.
    fn toete(&mut self, t: &Toetet, durch: &str, exakt: Option<&str>) {
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
        // The frame and the facts die with the write: a killed cell's equalities
        // no longer hold, and its carrier is no longer covered by the acquire.
        fn trifft(n: &Norm, ts: &BTreeSet<String>) -> bool {
            matches!(n, Norm::Zelle(z) if ts.iter().any(|tab| z.starts_with(&format!("{tab}."))))
        }
        fn trifft_zelle(n: &Norm, zelle: &str) -> bool {
            matches!(n, Norm::Zelle(z) if z == zelle)
        }
        match t {
            Toetet::Alles => {
                self.alles_beruehrt = true;
                self.fakten.clear();
            }
            Toetet::Tabellen(ts) => {
                self.beruehrt_traeger.extend(ts.iter().cloned());
                match exakt {
                    Some(zelle) => {
                        self.fakten.retain(|(a, b)| {
                            !trifft_zelle(a, zelle) && !trifft_zelle(b, zelle)
                        });
                    }
                    None => {
                        self.fakten.retain(|(a, b)| !trifft(a, ts) && !trifft(b, ts));
                    }
                }
            }
        }
    }

    /// The `ensures` equalities a promising call contributes, with its parameters
    /// substituted by the caller's constant arguments where they resolve.
    fn nimm_versprechen(&mut self, g: &Gerufener, r: &Ruf) {
        let mut subst: BTreeMap<String, Norm> = BTreeMap::new();
        let leer_gebunden = BTreeSet::new();
        let leer_subst = BTreeMap::new();
        for (i, pname) in g.parameter.iter().enumerate() {
            if let Some(arg) = r.argumente.get(i) {
                let n = norm_expr(
                    arg,
                    &leer_gebunden,
                    &self.params,
                    &leer_subst,
                    &self.lokal,
                    &self.welt.konstanten,
                );
                if !matches!(n, Norm::Weg) {
                    subst.insert(pname.clone(), n);
                }
            }
        }
        let gebunden: BTreeSet<String> = g.parameter.iter().cloned().collect();
        for e in &g.ensures {
            self.nimm_konjunkt(e, &gebunden, &g.param_traeger, &subst);
        }
    }

    fn nimm_konjunkt(
        &mut self,
        p: &Pred,
        gebunden: &BTreeSet<String>,
        params: &BTreeMap<String, String>,
        subst: &BTreeMap<String, Norm>,
    ) {
        match &p.art {
            PredArt::Und(a, b) => {
                self.nimm_konjunkt(a, gebunden, params, subst);
                self.nimm_konjunkt(b, gebunden, params, subst);
            }
            PredArt::Klammer(q) => self.nimm_konjunkt(q, gebunden, params, subst),
            PredArt::Quantor(q) => {
                let mut innen = gebunden.clone();
                innen.insert(q.variable.text.clone());
                self.nimm_konjunkt(&q.rumpf, &innen, params, subst);
            }
            PredArt::Vergleich(e) => {
                let e = crate::ohne_klammern(e);
                if let ExprArt::Binaer(BinOp::Gleich, a, b) = &e.art {
                    let leer_lokal = BTreeMap::new();
                    let l = norm_expr(a, gebunden, params, subst, &leer_lokal, &self.welt.konstanten);
                    let r = norm_expr(b, gebunden, params, subst, &leer_lokal, &self.welt.konstanten);
                    self.merke_gleich(l, r);
                }
                // Inequality promises (`c <= K`) are beyond this text: they are
                // cells for the row, never facts (see the module head).
            }
            _ => {}
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
                self.toete(&Toetet::Alles, "an indirect call", None);
                return;
            }
        };
        // The callee as this walk counts it; cloned out of the world so the
        // promise facts can be taken while the walk mutates.
        let gerufener = self.welt.gerufene.get(&name).cloned().flatten();
        match gerufener {
            None => {
                let bekannt = self.welt.gerufene.contains_key(&name);
                self.gruende.push(if bekannt {
                    format!("ambiguous callee {name}")
                } else {
                    format!("unknown callee {name}")
                });
                self.toete(
                    &Toetet::Alles,
                    &if bekannt {
                        format!("the ambiguous callee {name}")
                    } else {
                        format!("the unknown callee {name}")
                    },
                    None,
                );
            }
            Some(g) => {
                self.toete(&g.toetet.clone(), &format!("a write of {name}"), None);
                if bedingt {
                    self.gruende.push(format!("conditional call of {name}"));
                } else if verspricht {
                    for z in &g.verspricht {
                        self.hat.insert(z.clone());
                        self.getoetet.remove(z);
                    }
                    self.rufer.push(format!("{name} promises {}", menge_text(&g.verspricht)));
                    self.nimm_versprechen(&g, r);
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
                    self.toete(&Toetet::Alles, "a library call", None);
                }
                _ => {}
            }
        }
    }

    /// Whether conjunct `i` follows at this point: from the acquire frame when
    /// nothing may have touched it, else from the collected equalities.
    fn gilt(&self, i: usize) -> bool {
        let k = &self.konjunkte[i];
        if k.unzaehlbar {
            return false;
        }
        if !self.alles_beruehrt
            && k.traeger.iter().all(|t| !self.beruehrt_traeger.contains(t))
        {
            return true;
        }
        self.folgt(&k.pred)
    }

    /// Whether a predicate follows from the collected equality facts.
    /// Only conjunctions of comparisons over cells and constants are decided;
    /// anything else (disjunction, negation, quantifiers, reachability, `Held`)
    /// cannot be shown and stays on the obliging side.
    fn folgt(&self, p: &Pred) -> bool {
        match &p.art {
            PredArt::Klammer(q) => self.folgt(q),
            PredArt::Und(a, b) => self.folgt(a) && self.folgt(b),
            PredArt::Vergleich(e) => match &e.art {
                ExprArt::Wahr => true,
                ExprArt::Falsch => false,
                ExprArt::Klammer(_) => self.folgt(&Pred {
                    art: PredArt::Vergleich(crate::ohne_klammern(e).clone()),
                    span: e.span,
                }),
                ExprArt::Binaer(op, a, b) if op.ist_vergleich() => self.folgt_cmp(*op, a, b),
                _ => false,
            },
            _ => false,
        }
    }

    /// The canonical form of a value under the collected equalities: a cell with
    /// a known value answers it, a cell in a class answers its root.
    fn kanon(&self, n: &Norm) -> Norm {
        let mut elter: BTreeMap<String, String> = BTreeMap::new();
        let mut wert: BTreeMap<String, i128> = BTreeMap::new();
        fn wurzel(elter: &mut BTreeMap<String, String>, z: &str) -> String {
            let mut w = z.to_string();
            while let Some(v) = elter.get(&w).cloned() {
                if v == w {
                    break;
                }
                w = v;
            }
            w
        }
        for (a, b) in &self.fakten {
            match (a, b) {
                (Norm::Zelle(x), Norm::Zahl(v)) | (Norm::Zahl(v), Norm::Zelle(x)) => {
                    let w = wurzel(&mut elter, x);
                    match wert.get(&w) {
                        // Two different values for one cell: contradictory
                        // promises -- the value is dropped, never guessed.
                        Some(u) if u != v => {
                            wert.remove(&w);
                        }
                        _ => {
                            wert.insert(w, *v);
                        }
                    }
                }
                (Norm::Zelle(x), Norm::Zelle(y)) => {
                    let (wx, wy) = (wurzel(&mut elter, x), wurzel(&mut elter, y));
                    if wx != wy {
                        elter.insert(wx.clone(), wy.clone());
                        if let Some(v) = wert.remove(&wx) {
                            match wert.get(&wy) {
                                Some(u) if u != &v => {
                                    wert.remove(&wy);
                                }
                                _ => {
                                    wert.insert(wy, v);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        match n {
            Norm::Zelle(z) => {
                let w = wurzel(&mut elter, z);
                match wert.get(&w) {
                    Some(v) => Norm::Zahl(*v),
                    None => Norm::Zelle(w),
                }
            }
            _ => n.clone(),
        }
    }

    fn folgt_cmp(&self, op: BinOp, a: &Expr, b: &Expr) -> bool {
        let leer_gebunden: BTreeSet<String> = BTreeSet::new();
        let leer_subst: BTreeMap<String, Norm> = BTreeMap::new();
        let leer_lokal: BTreeMap<String, i128> = BTreeMap::new();
        let l = self.kanon(&norm_expr(
            a,
            &leer_gebunden,
            &self.params,
            &leer_subst,
            &self.lokal,
            &self.welt.konstanten,
        ));
        let r = self.kanon(&norm_expr(
            b,
            &leer_gebunden,
            &self.params,
            &leer_subst,
            &self.lokal,
            &self.welt.konstanten,
        ));
        match (op, &l, &r) {
            (_, Norm::Zahl(x), Norm::Zahl(y)) => match op {
                BinOp::Gleich => x == y,
                BinOp::Ungleich => x != y,
                BinOp::Kleiner => x < y,
                BinOp::KleinerGleich => x <= y,
                BinOp::Groesser => x > y,
                BinOp::GroesserGleich => x >= y,
                _ => false,
            },
            (BinOp::Gleich, Norm::Zelle(x), Norm::Zelle(y)) => x == y,
            (BinOp::KleinerGleich, Norm::Zelle(x), Norm::Zelle(y))
            | (BinOp::GroesserGleich, Norm::Zelle(x), Norm::Zelle(y)) => x == y,
            _ => false,
        }
    }

    fn pruefe_ausgang(&mut self, wie: &str, span: Span) {
        for z in self.braucht.iter() {
            if z.contains(UNZAEHLBAR) || !self.hat.contains(z) {
                let g = format!("early exit (`{wie}`) with {z} not promised");
                if !self.gruende.contains(&g) {
                    self.gruende.push(g);
                }
            }
        }
        let mut fehlt = Vec::new();
        for i in 0..self.konjunkte.len() {
            if !self.gilt(i) {
                let k = &self.konjunkte[i];
                let zellen: Vec<&str> = k.zellen.iter().map(|s| s.as_str()).collect();
                fehlt.push(format!(
                    "{} is not determined at the `{wie}` exit (cells not determined: {})",
                    vergleich_text(&k.pred, &k.zellen),
                    zellen.join(", ")
                ));
            }
        }
        self.ausgaenge.push(Ausgang { art: wie.to_string(), span, fehlt });
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
        // An unconditional `cell = <const>` also ESTABLISHES `cell == <const>`;
        // a re-bound bare local updates its constant binding instead.
        let mut stift: Option<(Norm, Norm)> = None;
        let mut lokal_setzt: Option<(String, Option<i128>)> = None;
        let mut exakt: Option<String> = None;
        let toetet = match &s.art {
            StmtArt::Zuweisung(z) => {
                for e in crate::ausdruecke_im_ort(&z.ziel) {
                    self.ausdruck(e, false, bedingt);
                }
                if !bedingt && z.op == ZuwOp::Setzt {
                    let leer_gebunden = BTreeSet::new();
                    let leer_subst = BTreeMap::new();
                    // Only a literal-index write names exactly one cell; anything
                    // else may alias and establishes nothing.
                    if ort_exakt(&z.ziel) {
                        if let Some(zelle) = ziel_zelle(&z.ziel, &leer_gebunden, &self.params) {
                            exakt = Some(zelle.clone());
                            let w = norm_expr(
                                &z.wert,
                                &leer_gebunden,
                                &self.params,
                                &leer_subst,
                                &self.lokal,
                                &self.welt.konstanten,
                            );
                            if let Norm::Zahl(n) = w {
                                stift = Some((Norm::Zelle(zelle), Norm::Zahl(n)));
                            }
                        }
                    }
                    if exakt.is_none() && z.ziel.suffixe.is_empty() {
                        let w = norm_expr(
                            &z.wert,
                            &leer_gebunden,
                            &self.params,
                            &leer_subst,
                            &self.lokal,
                            &self.welt.konstanten,
                        );
                        lokal_setzt = Some((
                            z.ziel.basis.text.clone(),
                            match w {
                                Norm::Zahl(n) => Some(n),
                                _ => None,
                            },
                        ));
                    }
                } else if !bedingt
                    && z.ziel.suffixe.is_empty()
                    && z.op != ZuwOp::Setzt
                {
                    // A compound assignment may change a local: its binding dies.
                    lokal_setzt = Some((z.ziel.basis.text.clone(), None));
                } else if bedingt && z.ziel.suffixe.is_empty() {
                    lokal_setzt = Some((z.ziel.basis.text.clone(), None));
                }
                Some((
                    ziel_toetet(&z.ziel, self.welt, &self.params),
                    format!("the write to {}", z.ziel.text()),
                ))
            }
            StmtArt::Let(l) => {
                if !bedingt {
                    let leer_gebunden = BTreeSet::new();
                    let leer_subst = BTreeMap::new();
                    let w = norm_expr(
                        &l.wert,
                        &leer_gebunden,
                        &self.params,
                        &leer_subst,
                        &self.lokal,
                        &self.welt.konstanten,
                    );
                    match w {
                        Norm::Zahl(n) => {
                            self.lokal.insert(l.name.text.clone(), n);
                        }
                        _ => {
                            self.lokal.remove(&l.name.text);
                        }
                    }
                }
                None
            }
            StmtArt::Publish(p) => Some((
                ziel_toetet(&p.ziel, self.welt, &self.params),
                format!("the write to {}", p.ziel.text()),
            )),
            StmtArt::Exchange(e) => Some((
                ziel_toetet(&e.ort, self.welt, &self.params),
                format!("the exchange on {}", e.ort.text()),
            )),
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
            StmtArt::LetSonst(_)
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
            self.toete(&t, &durch, exakt.as_deref());
        }
        // The establishment lands after the kill it re-establishes.
        if let Some((a, b)) = stift {
            self.merke_gleich(a, b);
        }
        if let Some((name, wert)) = lokal_setzt {
            match wert {
                Some(n) => {
                    self.lokal.insert(name, n);
                }
                None => {
                    self.lokal.remove(&name);
                }
            }
        }
        // 3. Sub-blocks: brackets in line, everything else conditional.
        let klammer = matches!(&s.art, StmtArt::Sperrt(_) | StmtArt::Observiert(_));
        for k in crate::unterbloecke(s) {
            self.block(k, bedingt || !klammer);
        }
        // 4. An exit releases here.
        match &s.art {
            StmtArt::Return(_) => self.pruefe_ausgang("return", s.span),
            StmtArt::Leave(_) => self.pruefe_ausgang("leave", s.span),
            StmtArt::Next(_) => self.pruefe_ausgang("next", s.span),
            _ => {}
        }
    }
}

/// Every `locks L { … }` section of a body, with its statement for the span --
/// with a nested section getting its own row, through every sub-block
/// (`observes` and `child` included since F7).
fn sperr_abschnitte<'b>(b: &'b Block, acc: &mut Vec<(&'b Stmt, &'b SperrtStmt)>) {
    for s in &b.anweisungen {
        if let StmtArt::Sperrt(sp) = &s.art {
            acc.push((s, sp));
        }
        for k in crate::unterbloecke(s) {
            sperr_abschnitte(k, acc);
        }
    }
}

/// A numeric `const` value, or `None` for any other initializer.
fn konst_wert(e: &Expr) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => Some(*n as i128),
        ExprArt::Klammer(x) => konst_wert(x),
        ExprArt::Unaer(UnOp::Negativ, x) => konst_wert(x).map(|n| n.saturating_neg()),
        _ => None,
    }
}

fn sammle_items<'a>(
    items: &'a [Item],
    fns: &mut Vec<&'a FnDecl>,
    sperren: &mut Vec<&'a LockDecl>,
    traeger: &mut BTreeSet<String>,
    konstanten: &mut BTreeMap<String, i128>,
) {
    for item in items {
        match &item.art {
            ItemArt::Funktion(f) => fns.push(f),
            ItemArt::Lock(l) => sperren.push(l),
            ItemArt::Modul(m) => sammle_items(&m.items, fns, sperren, traeger, konstanten),
            ItemArt::Konst(k) => {
                if let Some(n) = konst_wert(&k.wert) {
                    konstanten.insert(k.name.text.clone(), n);
                }
            }
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

pub(crate) fn menge_text(m: &BTreeSet<String>) -> String {
    if m.is_empty() {
        return "{}".to_string();
    }
    let v: Vec<&str> = m.iter().map(|s| s.as_str()).collect();
    format!("{{{}}}", v.join(", "))
}

/// What a callee's declared effects may write. `params` maps the callee's own
/// `ptr` parameters to their carriers, so `writes k.slots` counts as its carrier.
fn toetet_von(
    f: &FnDecl,
    traeger: &BTreeSet<String>,
    params: &BTreeMap<String, String>,
) -> Toetet {
    let Some(w) = &f.effects else {
        // Derived effects: this text does not see them -- anything.
        return Toetet::Alles;
    };
    let mut ts = BTreeSet::new();
    for e in &w.liste {
        match &e.art {
            WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                let basis =
                    params.get(&o.basis.text).cloned().unwrap_or(o.basis.text.clone());
                if traeger.contains(&basis) {
                    ts.insert(basis);
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

/// The whole-program facts one verdict is read against.
struct ProgrammWelt {
    welt: Welt,
    fns: Vec<FnDecl>,
    sperren: Vec<LockDecl>,
}

fn welt_bauen(tree: &Programm) -> ProgrammWelt {
    let mut fns_ref = Vec::new();
    let mut sperren_ref = Vec::new();
    let mut traeger = BTreeSet::new();
    let mut konstanten = BTreeMap::new();
    sammle_items(&tree.items, &mut fns_ref, &mut sperren_ref, &mut traeger, &mut konstanten);
    // Callees by short name; a short name declared twice promises nothing countable --
    // guessing the body would wed the row to the wrong contract.
    let mut gerufene: BTreeMap<String, Option<Gerufener>> = BTreeMap::new();
    for f in &fns_ref {
        let param_namen: BTreeSet<String> =
            f.parameter.iter().map(|p| p.name.text.clone()).collect();
        let param_traeger = param_traeger(f, &traeger);
        let mut zellen = BTreeSet::new();
        for e in &f.ensures {
            zellen_pred(e, &param_namen, &param_traeger, &mut zellen);
        }
        zellen.retain(|z| !z.contains(UNZAEHLBAR));
        let g = Gerufener {
            verspricht: zellen,
            toetet: toetet_von(f, &traeger, &param_traeger),
            ensures: f.ensures.clone(),
            parameter: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            param_traeger,
        };
        if gerufene.contains_key(&f.name.text) {
            gerufene.insert(f.name.text.clone(), None);
        } else {
            gerufene.insert(f.name.text.clone(), Some(g));
        }
    }
    ProgrammWelt {
        welt: Welt { gerufene, traeger, konstanten },
        fns: fns_ref.into_iter().cloned().collect(),
        sperren: sperren_ref.into_iter().cloned().collect(),
    }
}

/// The verdict over one `locks L { … }` section that carries an invariant.
/// Sections over an unknown lock or without an invariant get no verdict here;
/// the rows name them separately.
fn beurteile_abschnitt(
    welt: &Welt,
    f: &FnDecl,
    _sperre: &LockDecl,
    inv: &Pred,
    stmt_span: Span,
    sp: &SperrtStmt,
) -> AbschnittUrteil {
    let leer_params = BTreeMap::new();
    let mut braucht = BTreeSet::new();
    zellen_pred(inv, &BTreeSet::new(), &leer_params, &mut braucht);
    let konj = konjunkte(inv);
    let mut lauf = Lauf {
        welt,
        braucht: braucht.clone(),
        konjunkte: konj,
        params: param_traeger(f, &welt.traeger),
        hat: BTreeSet::new(),
        getoetet: BTreeMap::new(),
        gruende: Vec::new(),
        rufer: Vec::new(),
        fakten: Vec::new(),
        beruehrt_traeger: BTreeSet::new(),
        alles_beruehrt: false,
        lokal: BTreeMap::new(),
        ausgaenge: Vec::new(),
    };
    lauf.block(&sp.rumpf, false);
    // The release: the invariant is owed at the end of the section.
    let mut fehlt = Vec::new();
    for i in 0..lauf.konjunkte.len() {
        if !lauf.gilt(i) {
            let k = &lauf.konjunkte[i];
            let zellen: Vec<&str> = k.zellen.iter().map(|s| s.as_str()).collect();
            fehlt.push(format!(
                "{} is not determined at the `release` exit (cells not determined: {})",
                vergleich_text(&k.pred, &k.zellen),
                zellen.join(", ")
            ));
        }
    }
    lauf.ausgaenge.push(Ausgang { art: "release".to_string(), span: stmt_span, fehlt });
    // The legacy cell reasons, kept for the row text: cells no callee promises,
    // cells written after their last promise.
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
    for a in &lauf.ausgaenge {
        gruende.extend(a.fehlt.iter().cloned());
    }
    AbschnittUrteil {
        funktion: f.name.text.clone(),
        sperre: String::new(),
        braucht,
        rufer: lauf.rufer,
        gruende,
        ausgaenge: lauf.ausgaenge,
    }
}

/// Every verdict of the unit: one entry per `locks L { … }` section.
/// THE one analysis behind the obligation rows and the `N511` refusal.
pub(crate) enum Abschnitt {
    /// The lock is declared nowhere or ambiguously: nothing countable.
    Unbekannt { funktion: String, sperre: String },
    /// The lock carries no invariant: nothing is owed at this release.
    OhneInvariante { funktion: String, sperre: String },
    /// The invariant mentions no slot cell: nothing countable is owed.
    OhneZellen { funktion: String, sperre: String },
    /// The decided verdict, per exit.
    Urteil(AbschnittUrteil),
}

pub(crate) fn beurteile(tree: &Programm) -> Vec<Abschnitt> {
    let prog = welt_bauen(tree);
    let mut aus = Vec::new();
    for f in &prog.fns {
        let FnRumpf::Block(b) = &f.rumpf else {
            continue;
        };
        let mut abschnitte = Vec::new();
        sperr_abschnitte(b, &mut abschnitte);
        for (stmt, sp) in abschnitte {
            let sperre_name = &sp.sperre.basis.text;
            // Same rule as for callees: a short lock name declared twice resolves to nothing
            // countable.
            let treffer: Vec<&LockDecl> =
                prog.sperren.iter().filter(|l| &l.name.text == sperre_name).collect();
            let [sperre] = treffer.as_slice() else {
                aus.push(Abschnitt::Unbekannt {
                    funktion: f.name.text.clone(),
                    sperre: sperre_name.clone(),
                });
                continue;
            };
            let Some(inv) = &sperre.invariante else {
                aus.push(Abschnitt::OhneInvariante {
                    funktion: f.name.text.clone(),
                    sperre: sperre_name.clone(),
                });
                continue;
            };
            let leer_params = BTreeMap::new();
            let mut braucht = BTreeSet::new();
            zellen_pred(inv, &BTreeSet::new(), &leer_params, &mut braucht);
            if braucht.is_empty() {
                aus.push(Abschnitt::OhneZellen {
                    funktion: f.name.text.clone(),
                    sperre: sperre_name.clone(),
                });
                continue;
            }
            let mut u = beurteile_abschnitt(&prog.welt, f, sperre, inv, stmt.span, sp);
            u.sperre = sperre_name.clone();
            aus.push(Abschnitt::Urteil(u));
        }
    }
    aus
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
    out.push_str("-- (their `ensures`), not from what their bodies happen to do. What does\n");
    out.push_str("-- not follow is refused with `N511` (`freigabe_pruef.rs`); the rows below\n");
    out.push_str("-- state the same verdict per section (`beurteile`).\n");
    out.push_str("-- Each row below is syntactic, one-sided and order-aware (see\n");
    out.push_str("-- `crates/gabbro-check/src/freigabe.rs`): the invariant must follow from\n");
    out.push_str("-- the acquire frame, the section's own writes and what the section's\n");
    out.push_str("-- callees PROMISE (their `ensures`), never their bodies. `RELEASE HOLDS\n");
    out.push_str("-- (syntactic)` is not a proof, while `RELEASE UNPROVED` names the exact gap.");
    out.push_str(zusatz);
    out.push('\n');
    let mut hat_invariante = false;
    crate::fuer_jedes_item(tree, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            if l.invariante.is_some() {
                hat_invariante = true;
            }
        }
    });
    if !hat_invariante {
        out.push_str("-- No lock carries an invariant -- nothing is owed at any release.\n");
        return out;
    }
    let urteile = beurteile(tree);
    if urteile.is_empty() {
        out.push_str("-- No `locks` section in any body -- nothing is owed at any release.\n");
        return out;
    }
    for abschnitt in &urteile {
        match abschnitt {
            Abschnitt::Unbekannt { funktion, sperre } => {
                out.push_str(&format!(
                    "-- * {funktion} locks `{sperre}`: that lock is declared nowhere or ambiguously -- RELEASE UNPROVED (unknown lock).\n"
                ));
            }
            Abschnitt::OhneInvariante { funktion, sperre } => {
                out.push_str(&format!(
                    "-- * {funktion} locks `{sperre}`: no invariant -- nothing is owed at this release.\n"
                ));
            }
            Abschnitt::OhneZellen { funktion, sperre } => {
                out.push_str(&format!(
                    "-- * {funktion} locks `{sperre}`: the invariant mentions no slot cell -- nothing countable is owed at this release.\n"
                ));
            }
            Abschnitt::Urteil(u) => {
                let ruf_text =
                    if u.rufer.is_empty() { "no calls".to_string() } else { u.rufer.join("; ") };
                if u.haelt() {
                    out.push_str(&format!(
                        "-- * {} locks `{}`: invariant over {}; {} -- RELEASE HOLDS (syntactic).\n",
                        u.funktion,
                        u.sperre,
                        menge_text(&u.braucht),
                        ruf_text
                    ));
                } else {
                    out.push_str(&format!(
                        "-- * {} locks `{}`: invariant over {}; {} -- RELEASE UNPROVED: {}.\n",
                        u.funktion,
                        u.sperre,
                        menge_text(&u.braucht),
                        ruf_text,
                        u.gruende.join("; ")
                    ));
                }
            }
        }
    }
    out
}
