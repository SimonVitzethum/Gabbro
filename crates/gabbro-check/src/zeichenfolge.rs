//! Bounded strings: the length discipline (lane 256, fix lane F6), wired as
//! a pass.
//!
//! A bounded string carries its declared maximum the way `u32` carries
//! `in 0 .. N`. `+` on two strings concatenates (maxes add, refused past the
//! target max), `lenof` reads the length, `s[k]` indexes (proven below the
//! LENGTH or refused), and `==`/`<` compare. Unbounded strings have no form
//! and stay refused by name (no constructor here takes no max).
//!
//! The shared type system reads `string max N` as `Unbekannt`
//! (`umgebung.rs`); this pass tracks declared maxes in its own scoped table
//! and decides. The codes are `N453` (concat past the target max), `N454`
//! (index not proven below the length), `N455` (sort: a non-string where a
//! string stands, or the reverse, or a string past a shorter slot) and
//! `N465` (a string where the discipline does not follow it).
//!
//! The pure length arithmetic below mirrors
//! `grammatik/Grammatik/ZeichenfolgeGebunden.lean`
//! (`BString`, `bliteral`, `bconcat`, `bkopie`, `bindex`).
//!
//! ## Where a string may stand (fix lane F6, review G12 F4/F5)
//!
//! Lane 256 fired only on positive knowledge and stayed silent where it
//! could not see -- and it could not see struct fields, `const`/`static`
//! initializers, table slots, contracts or `LetSonst`. Fix lane F6 closes
//! the positions instead of listing them:
//!
//! - **Declarations (`N465`).** A `string max N` stands only as the WHOLE
//!   type of a function parameter, a function result or a `let` annotation.
//!   Anywhere else -- a struct or table field, a `const`/`static`/atomic
//!   type, an arena element, a type alias, an array element, a variant
//!   payload, a pointer target, a function-pointer parameter, a `syscall`
//!   head -- it is refused. The walk is `crate::jeder_typausdruck_im_item`
//!   (exhaustive over `ItemArt` and `TypExpr`), so a new item or type form
//!   cannot slip past. With that, every string VALUE comes from a name the
//!   pass binds, a resolved call with a string result, or a `+` of two:
//!   the pass's knowledge is complete, and "not known as a string" means
//!   "not a string".
//! - **Values (`N455`).** A string value flows only into a known string
//!   slot that fits it: an annotated `let`, an assignment to a string name,
//!   a `return` at a string result, a string parameter (also inside
//!   contracts and `let … else` sources). Everywhere else -- a condition, a
//!   `match` subject, an index, an operand of anything but `+`/comparison,
//!   an array element, an atomic publish, an arena slot, a field target, a
//!   `const`/`static` initializer -- it falls.
//! - **Unresolved callees (`N465`).** A string handed to a callee the pass
//!   cannot resolve (a method call, a library call, an ambiguous name, a
//!   constructor) falls; an ambiguous callee with a string in its head
//!   falls too.
//!
//! ## Indexing is proven against the length (fix lane F6, review G12 F4)
//!
//! `bindex` in Lean refuses `k >= length`, and a `string max 8` may hold
//! zero characters, so `k < max` proves nothing. An index stands only
//! where a flow fact shows it below `lenof(s)`:
//!
//! - a literal `k` where `lenof(s) > k` (or `>= k+1`, `== c` with `c > k`)
//!   is known;
//! - a name `i` of an unsigned integer type where `i < lenof(s)` is known.
//!
//! Facts come from the condition of an `if` branch (`&&` joins, `!` and
//! `||` negate), from the negated condition after an `if` without `else`
//! whose block always ends, and from `requires` at the function head.
//! A fact dies when either name is assigned (anywhere under the statement,
//! and before a loop body when the loop assigns it) or rebound. No fact
//! crosses into the right side of an `&&` inside one expression: a guard
//! and its index stand in two statements.
//!
//! ## Scopes (fix lane F6, review G12 F5)
//!
//! The name table is a stack of block scopes walked in statement order: a
//! `let` binds from the next statement on, an inner block's bindings end
//! with it, and an unannotated `let` the pass cannot type binds the name as
//! a non-string (it shadows, it never keeps a stale max).
//!
//! ## Scope cuts (all end-to-end safe: the emitter stops every string
//! ## program with `C001`, so nothing below can leak into C)
//!
//! - No literals: `"hi"` stays `P011` (a literal needs an `ExprArt` arm,
//!   and `m1::ausdruck_roh` is exhaustive over `ExprArt`).
//! - Lengths are max-bounds for `+` and copies (a sound over-approximation
//!   of `bconcat`/`bkopie`, which check the exact length); only `lenof`
//!   facts are exact, and they feed the index rule alone.
//! - No representation: NUL termination and an upper limit on `max` are
//!   the lowering lane's decisions (`TODO.md`, wave E).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Absage;
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

/// A literal fits exactly when its known length fits the declared max.
pub fn literal_passt(max: usize, len: usize) -> bool {
    len <= max
}

/// The upper limit on `max` (lane 261): the C layout is one length word
/// plus `max` bytes per value (`gabbro_string_N`), so a max above this
/// the unit cannot allocate -- a single local would already exceed any
/// sane stack frame -- and a max of zero holds no character and has no
/// object form (`uint8_t data[0]` is no strict-C11 object).
pub const MAX_OBERGRENZE: u128 = 65535;

/// A declared max stands exactly when it allocates: neither empty nor past
/// the bound.
pub fn max_traegt(max: u128) -> bool {
    1 <= max && max <= MAX_OBERGRENZE
}

/// `concat` fits exactly when the length sum fits the target max.
/// `None` is the refusal (overflow of the sum, or past the max).
pub fn concat_passt(ziel_max: usize, a_len: usize, b_len: usize) -> Option<usize> {
    let summe = a_len.checked_add(b_len)?;
    if summe <= ziel_max {
        Some(summe)
    } else {
        None
    }
}

/// Bounded indexing: in-range or refused.
pub fn index_passt(len: usize, i: usize) -> bool {
    i < len
}

/// What the pass knows about one bound name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Eintrag {
    /// A string of this max.
    Kette(u128),
    /// No string; `natuerlich` when its declared type is an unsigned
    /// integer (only such a name may stand as a proven index).
    Fremd { natuerlich: bool },
}

/// A declared slot: a string max, or a known non-string type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Schlitz {
    Kette(u128),
    Fremd { natuerlich: bool },
}

fn schlitz_von(t: &TypExpr) -> Schlitz {
    match t {
        TypExpr::Zeichenkette { max, .. } => Schlitz::Kette(*max),
        TypExpr::Int(i) => Schlitz::Fremd {
            natuerlich: matches!(crate::umgebung::breite_von(i.wort), Some((_, false))),
        },
        _ => Schlitz::Fremd { natuerlich: false },
    }
}

fn eintrag_von(s: Schlitz) -> Eintrag {
    match s {
        Schlitz::Kette(m) => Eintrag::Kette(m),
        Schlitz::Fremd { natuerlich } => Eintrag::Fremd { natuerlich },
    }
}

/// A callee's string-relevant signature, owned.
#[derive(Debug, Clone)]
struct RumpfSignatur {
    params: Vec<(String, Schlitz)>,
    ergebnis: Option<Schlitz>,
}

impl RumpfSignatur {
    fn traegt_kette(&self) -> bool {
        self.params.iter().any(|(_, s)| matches!(s, Schlitz::Kette(_)))
            || matches!(self.ergebnis, Some(Schlitz::Kette(_)))
    }
}

/// How a call path resolves.
enum Aufloesung {
    Gefunden(RumpfSignatur),
    /// More than one candidate; `true` when any of them has a string in
    /// its head.
    Mehrdeutig(bool),
    Keiner,
}

/// The per-unit context of the walk.
struct Lage<'a> {
    fns: &'a HashMap<String, RumpfSignatur>,
    modul: &'a str,
    ergebnis: Option<Schlitz>,
}

/// The flow state: scoped bindings plus the length facts.
#[derive(Debug, Clone, Default)]
struct Zustand {
    scopes: Vec<HashMap<String, Eintrag>>,
    /// `lenof(s) >= n` is known.
    mindestens: HashMap<String, u128>,
    /// `i < lenof(s)` is known, as `(i, s)`.
    unter: HashSet<(String, String)>,
}

impl Zustand {
    fn neu() -> Zustand {
        Zustand {
            scopes: vec![HashMap::new()],
            ..Zustand::default()
        }
    }

    fn eintrag(&self, name: &str) -> Option<Eintrag> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    fn kette(&self, name: &str) -> Option<u128> {
        match self.eintrag(name) {
            Some(Eintrag::Kette(m)) => Some(m),
            _ => None,
        }
    }

    fn natuerlich(&self, name: &str) -> bool {
        matches!(self.eintrag(name), Some(Eintrag::Fremd { natuerlich: true }))
    }

    fn binde(&mut self, name: &str, e: Eintrag) {
        self.toete(name);
        if let Some(s) = self.scopes.last_mut() {
            s.insert(name.to_string(), e);
        }
    }

    /// Every length fact that mentions `name` dies.
    fn toete(&mut self, name: &str) {
        self.mindestens.remove(name);
        self.unter.retain(|(i, s)| i != name && s != name);
    }

    fn innen(&self) -> Zustand {
        let mut z = self.clone();
        z.scopes.push(HashMap::new());
        z
    }

    fn lerne(&mut self, f: Fakten) {
        for (s, n) in f.mindestens {
            let alt = self.mindestens.entry(s).or_insert(0);
            *alt = (*alt).max(n);
        }
        self.unter.extend(f.unter);
    }
}

/// Facts one condition yields.
#[derive(Default)]
struct Fakten {
    mindestens: Vec<(String, u128)>,
    unter: Vec<(String, String)>,
}

impl Fakten {
    fn und(mut self, b: Fakten) -> Fakten {
        self.mindestens.extend(b.mindestens);
        self.unter.extend(b.unter);
        self
    }
}

/// The pass: bounded-string discipline over declarations, bodies,
/// contracts and item-level values. Same column as M1 (no pass number of
/// its own, like `kontexte::pass`).
pub fn pass(baum: &Programm, absagen: &mut gabbro_syntax::diag::Absagen) {
    let mut fns: HashMap<String, RumpfSignatur> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            fns.insert(
                format!("{modul}::{}", f.name.text),
                RumpfSignatur {
                    params: f
                        .parameter
                        .iter()
                        .map(|p| (p.name.text.clone(), schlitz_von(&p.typ)))
                        .collect(),
                    ergebnis: f.ergebnis.as_ref().map(schlitz_von),
                },
            );
        }
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        deklarationen(item, absagen);
        let lage_ohne = Lage {
            fns: &fns,
            modul,
            ergebnis: None,
        };
        match &item.art {
            ItemArt::Funktion(f) => {
                let lage = Lage {
                    fns: &fns,
                    modul,
                    ergebnis: f.ergebnis.as_ref().map(schlitz_von),
                };
                let mut z = Zustand::neu();
                for p in &f.parameter {
                    z.binde(&p.name.text, eintrag_von(schlitz_von(&p.typ)));
                }
                // `requires` are checked at the head (before their own
                // facts), then hold for the body and the `ensures`.
                for p in &f.requires {
                    praedikat(p, &z, &lage, absagen);
                }
                for p in &f.requires {
                    z.lerne(fakten_pred(p, &z));
                }
                for p in &f.ensures {
                    praedikat(p, &z, &lage, absagen);
                }
                if let Some(c) = &f.costs {
                    ausdruck(c, &z, &lage, absagen);
                }
                match &f.rumpf {
                    FnRumpf::Block(b) => block(b, &z, &lage, absagen),
                    FnRumpf::Pred(p) => praedikat(p, &z, &lage, absagen),
                    FnRumpf::Asm(_) | FnRumpf::Keiner => {}
                }
            }
            ItemArt::Check(c) => {
                let z = Zustand::neu();
                block(&c.can_fail, &z, &lage_ohne, absagen);
                for p in &c.floor {
                    praedikat(p, &z, &lage_ohne, absagen);
                }
            }
            // Item-level values: every slot here holds no string (a string
            // type at the declaration is `N465` above), so a string value
            // falls as `N455`.
            ItemArt::Konst(k) => wert_ohne_kette(&k.wert, &Zustand::neu(), &lage_ohne, absagen),
            ItemArt::Statisch(s) => {
                wert_ohne_kette(&s.wert, &Zustand::neu(), &lage_ohne, absagen)
            }
            ItemArt::Tabelle(t) => {
                let z = Zustand::neu();
                for k in &t.konstanten {
                    wert_ohne_kette(&k.wert, &z, &lage_ohne, absagen);
                }
                if let Some(k) = &t.kapazitaet {
                    wert_ohne_kette(k, &z, &lage_ohne, absagen);
                }
                for p in crate::praedikate_im_item(item) {
                    praedikat(p, &z, &lage_ohne, absagen);
                }
            }
            ItemArt::Arena(a) => {
                let z = Zustand::neu();
                for e in [Some(&a.lo), Some(&a.hi), a.max.as_ref()].into_iter().flatten() {
                    wert_ohne_kette(e, &z, &lage_ohne, absagen);
                }
            }
            // The remaining items carry no value position a string could
            // reach except through their predicates, which are walked here
            // (a string source there is a call, held by the same rules).
            ItemArt::Modul(_)
            | ItemArt::Use(_)
            | ItemArt::Typ(_)
            | ItemArt::Format(_)
            | ItemArt::Reason(_)
            | ItemArt::State(_)
            | ItemArt::Device(_)
            | ItemArt::Assume(_)
            | ItemArt::Axiom(_)
            | ItemArt::Atomic(_)
            | ItemArt::Lock(_)
            | ItemArt::Rcu(_)
            | ItemArt::Gruppe(_)
            | ItemArt::Concurrent(_)
            | ItemArt::Accumulates(_)
            | ItemArt::Walk(_)
            | ItemArt::Entry(_)
            | ItemArt::Entrust(_)
            | ItemArt::Boot(_)
            | ItemArt::Syscall(_)
            | ItemArt::Profil(_)
            | ItemArt::ProfilBedarf(_) => {
                let z = Zustand::neu();
                for p in crate::praedikate_im_item(item) {
                    praedikat(p, &z, &lage_ohne, absagen);
                }
            }
        }
    });
}

// --- Declarations -------------------------------------------------------

/// `N465` at every `string max N` of an item except the whole type of a
/// function parameter or result.
fn deklarationen(item: &Item, absagen: &mut gabbro_syntax::diag::Absagen) {
    let mut erlaubt: Vec<Span> = Vec::new();
    if let ItemArt::Funktion(f) = &item.art {
        for p in &f.parameter {
            if let TypExpr::Zeichenkette { span, .. } = &p.typ {
                erlaubt.push(*span);
            }
        }
        if let Some(TypExpr::Zeichenkette { span, .. }) = &f.ergebnis {
            erlaubt.push(*span);
        }
    }
    let mut stellen: Vec<Span> = Vec::new();
    crate::jeder_typausdruck_im_item(item, &mut |t| {
        if let TypExpr::Zeichenkette { span, .. } = t {
            stellen.push(*span);
        }
    });
    for s in stellen {
        if !erlaubt.contains(&s) {
            ort_ablehnung(
                s,
                "a bounded string stands only as the whole type of a function parameter, \
                 a function result or a `let`: here no length discipline follows it",
                absagen,
            );
        }
    }
    // **Lane 261:** every declared max allocates, wherever it stands -- even
    // a refused position (`N465` above) names a max the lowering would have
    // to allocate, so the bound is held here too, beside the place rule.
    let mut maxima: Vec<(u128, Span)> = Vec::new();
    crate::jeder_typausdruck_im_item(item, &mut |t| {
        if let TypExpr::Zeichenkette { max, span } = t {
            maxima.push((*max, *span));
        }
    });
    for (max, span) in maxima {
        max_regel(max, span, absagen);
    }
}

/// Every `string max N` inside a type expression, with the outermost one
/// flagged -- exhaustive over `TypExpr`.
fn ketten_im_typ(t: &TypExpr, aussen: bool, aus: &mut Vec<(Span, bool)>) {
    match t {
        TypExpr::Zeichenkette { span, .. } => aus.push((*span, aussen)),
        TypExpr::Feld(a) => ketten_im_typ(&a.element, false, aus),
        TypExpr::Zeiger(p) => ketten_im_typ(&p.ziel, false, aus),
        TypExpr::Verbund(felder, _) => {
            for x in felder {
                ketten_im_typ(&x.typ.typ, false, aus);
            }
        }
        TypExpr::Varianten(v, _) => {
            for x in v {
                if let Some(n) = &x.nutzlast {
                    ketten_im_typ(n, false, aus);
                }
            }
        }
        TypExpr::FnZeiger(z) => {
            for p in &z.parameter {
                ketten_im_typ(&p.typ, false, aus);
            }
            if let Some(e) = &z.ergebnis {
                ketten_im_typ(e, false, aus);
            }
        }
        TypExpr::Int(_)
        | TypExpr::Float(_)
        | TypExpr::Bool(_)
        | TypExpr::Never(_)
        | TypExpr::Pfad(_)
        | TypExpr::Index { .. } => {}
    }
}

/// A `let` annotation: the outermost string is allowed, any nested one is
/// `N465`; an `alloc` annotation (an index type) allows none.
/// **Every max named here allocates too** (lane 261): the bound rule runs
/// beside the place rule, on the same walk.
fn typ_annotation(t: &TypExpr, aussen_erlaubt: bool, absagen: &mut gabbro_syntax::diag::Absagen) {
    let mut v = Vec::new();
    ketten_im_typ(t, true, &mut v);
    for (s, aussen) in v {
        if !(aussen && aussen_erlaubt) {
            ort_ablehnung(
                s,
                "a bounded string stands only as the whole type of a function parameter, \
                 a function result or a `let`: here no length discipline follows it",
                absagen,
            );
        }
    }
    let mut maxima: Vec<(u128, Span)> = Vec::new();
    ketten_maxima(t, &mut maxima);
    for (max, span) in maxima {
        max_regel(max, span, absagen);
    }
}

/// Every declared `max` inside a type expression, outermost and nested alike.
fn ketten_maxima(t: &TypExpr, aus: &mut Vec<(u128, Span)>) {
    match t {
        TypExpr::Zeichenkette { max, span } => aus.push((*max, *span)),
        TypExpr::Feld(a) => ketten_maxima(&a.element, aus),
        TypExpr::Zeiger(p) => ketten_maxima(&p.ziel, aus),
        TypExpr::Verbund(felder, _) => {
            for x in felder {
                ketten_maxima(&x.typ.typ, aus);
            }
        }
        TypExpr::Varianten(v, _) => {
            for x in v {
                if let Some(n) = &x.nutzlast {
                    ketten_maxima(n, aus);
                }
            }
        }
        TypExpr::FnZeiger(z) => {
            for p in &z.parameter {
                ketten_maxima(&p.typ, aus);
            }
            if let Some(e) = &z.ergebnis {
                ketten_maxima(e, aus);
            }
        }
        TypExpr::Int(_)
        | TypExpr::Float(_)
        | TypExpr::Bool(_)
        | TypExpr::Never(_)
        | TypExpr::Pfad(_)
        | TypExpr::Index { .. } => {}
    }
}

// --- Resolution and synthesis --------------------------------------------

fn finde_fn(fns: &HashMap<String, RumpfSignatur>, modul: &str, p: &Pfad) -> Aufloesung {
    if let Some(f) = fns.get(&format!("{modul}::{}", p.text())) {
        return Aufloesung::Gefunden(f.clone());
    }
    let letzt = p.teile.last().map(|i| i.text.as_str());
    let treffer: Vec<&RumpfSignatur> = fns
        .iter()
        .filter(|(k, _)| k.rsplit("::").next() == letzt)
        .map(|(_, f)| f)
        .collect();
    match treffer.as_slice() {
        [] => Aufloesung::Keiner,
        [f] => Aufloesung::Gefunden((*f).clone()),
        viele => Aufloesung::Mehrdeutig(viele.iter().any(|f| f.traegt_kette())),
    }
}

/// The string max an expression provably holds, or `None` when it holds
/// no string. `+` of two strings sums (saturating: a sum that overflows
/// `u128` can only refuse harder downstream, never accept).
/// **A literal holds its exact byte length as its bound** (lane 261): a
/// literal of length `L` fits exactly the slots a `string max L` fits, so
/// every fit check below answers for it with no further rule.
fn synth(e: &Expr, z: &Zustand, lage: &Lage) -> Option<u128> {
    match &e.art {
        ExprArt::Klammer(x) => synth(x, z, lage),
        ExprArt::Kette(bytes) => Some(bytes.len() as u128),
        ExprArt::Ort(o) | ExprArt::Alt(o) if o.suffixe.is_empty() => z.kette(&o.basis.text),
        ExprArt::Ergebnis => match lage.ergebnis {
            Some(Schlitz::Kette(m)) => Some(m),
            _ => None,
        },
        ExprArt::Binaer(BinOp::Plus, a, b) => match (synth(a, z, lage), synth(b, z, lage)) {
            (Some(x), Some(y)) => Some(x.saturating_add(y)),
            _ => None,
        },
        ExprArt::Ruf(r) => match &r.ziel {
            CallTarget::Path(p) => match finde_fn(lage.fns, lage.modul, p) {
                Aufloesung::Gefunden(f) => match f.ergebnis {
                    Some(Schlitz::Kette(max)) => Some(max),
                    _ => None,
                },
                // Refused at the call (`N465`); nothing to synthesize.
                Aufloesung::Mehrdeutig(_) | Aufloesung::Keiner => None,
            },
            CallTarget::Place(_) => None,
        },
        _ => None,
    }
}

fn ohne_klammern(mut e: &Expr) -> &Expr {
    while let ExprArt::Klammer(x) = &e.art {
        e = x;
    }
    e
}

/// A provably non-string value: a literal of another sort.
fn ist_fremd_literal(e: &Expr) -> bool {
    matches!(
        &ohne_klammern(e).art,
        ExprArt::Zahl(_) | ExprArt::Gleitkomma { .. } | ExprArt::Wahr | ExprArt::Falsch
    )
}

// --- Facts --------------------------------------------------------------

enum Term {
    Laenge(String),
    Lit(u128),
    Name(String),
    Sonst,
}

fn term(e: &Expr, z: &Zustand) -> Term {
    match &ohne_klammern(e).art {
        ExprArt::Eingebaut(g) => match &**g {
            Eingebaut::Lenof(TypOderOrt::Ort(o))
                if o.suffixe.is_empty() && z.kette(&o.basis.text).is_some() =>
            {
                Term::Laenge(o.basis.text.clone())
            }
            _ => Term::Sonst,
        },
        ExprArt::Zahl(c) => Term::Lit(*c),
        ExprArt::Ort(o) if o.suffixe.is_empty() && z.natuerlich(&o.basis.text) => {
            Term::Name(o.basis.text.clone())
        }
        _ => Term::Sonst,
    }
}

/// `a < b` as facts.
fn kleiner(a: &Term, b: &Term) -> Fakten {
    let mut f = Fakten::default();
    match (a, b) {
        (Term::Lit(c), Term::Laenge(s)) => {
            if let Some(n) = c.checked_add(1) {
                f.mindestens.push((s.clone(), n));
            }
        }
        (Term::Name(i), Term::Laenge(s)) => f.unter.push((i.clone(), s.clone())),
        _ => {}
    }
    f
}

/// `a <= b` as facts.
fn kleiner_gleich(a: &Term, b: &Term) -> Fakten {
    let mut f = Fakten::default();
    if let (Term::Lit(c), Term::Laenge(s)) = (a, b) {
        f.mindestens.push((s.clone(), *c));
    }
    f
}

/// `a == b` as facts.
fn gleich(a: &Term, b: &Term) -> Fakten {
    let mut f = Fakten::default();
    match (a, b) {
        (Term::Lit(c), Term::Laenge(s)) | (Term::Laenge(s), Term::Lit(c)) => {
            f.mindestens.push((s.clone(), *c))
        }
        _ => {}
    }
    f
}

/// What holds when `e` is true (`wahr`) or false (`!wahr`).
fn fakten(e: &Expr, wahr: bool, z: &Zustand) -> Fakten {
    match &ohne_klammern(e).art {
        ExprArt::Binaer(BinOp::Und, a, b) if wahr => fakten(a, true, z).und(fakten(b, true, z)),
        ExprArt::Binaer(BinOp::Oder, a, b) if !wahr => {
            fakten(a, false, z).und(fakten(b, false, z))
        }
        ExprArt::Unaer(UnOp::Nicht, x) => fakten(x, !wahr, z),
        ExprArt::Binaer(op, a, b) => {
            let (ta, tb) = (term(a, z), term(b, z));
            match (op, wahr) {
                (BinOp::Kleiner, true) | (BinOp::GroesserGleich, false) => kleiner(&ta, &tb),
                (BinOp::Groesser, true) | (BinOp::KleinerGleich, false) => kleiner(&tb, &ta),
                (BinOp::KleinerGleich, true) | (BinOp::Groesser, false) => {
                    kleiner_gleich(&ta, &tb)
                }
                (BinOp::GroesserGleich, true) | (BinOp::Kleiner, false) => {
                    kleiner_gleich(&tb, &ta)
                }
                (BinOp::Gleich, true) | (BinOp::Ungleich, false) => gleich(&ta, &tb),
                _ => Fakten::default(),
            }
        }
        _ => Fakten::default(),
    }
}

/// What a `requires` clause makes known.
fn fakten_pred(p: &Pred, z: &Zustand) -> Fakten {
    match &p.art {
        PredArt::Vergleich(e) => fakten(e, true, z),
        PredArt::Klammer(x) => fakten_pred(x, z),
        PredArt::Und(a, b) => fakten_pred(a, z).und(fakten_pred(b, z)),
        _ => Fakten::default(),
    }
}

// --- The walk -------------------------------------------------------------

fn block(b: &Block, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    let mut z = z.innen();
    for s in &b.anweisungen {
        anweisung(s, &mut z, lage, absagen);
    }
}

/// Kill every fact about a name the statement (or anything under it)
/// assigns.
fn toete_schreibziele(s: &Stmt, z: &mut Zustand) {
    let mut ziele = Vec::new();
    crate::schreibziele(s, &mut ziele);
    for o in ziele {
        z.toete(&o.basis.text);
    }
}

fn anweisung(s: &Stmt, z: &mut Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    match &s.art {
        StmtArt::Let(l) => {
            ausdruck(&l.wert, z, lage, absagen);
            let eintrag = match &l.typ {
                Some(t) => {
                    typ_annotation(t, true, absagen);
                    match schlitz_von(t) {
                        Schlitz::Kette(max) => {
                            ziel_regel(&l.wert, max, z, lage, absagen);
                            Eintrag::Kette(max)
                        }
                        Schlitz::Fremd { natuerlich } => {
                            wert_ohne_kette(&l.wert, z, lage, absagen);
                            Eintrag::Fremd { natuerlich }
                        }
                    }
                }
                // Unannotated: a known string initializer fixes the max;
                // anything else binds a non-string (it shadows, it never
                // keeps an outer max).
                None => match synth(&l.wert, z, lage) {
                    Some(m) => Eintrag::Kette(m),
                    None => Eintrag::Fremd { natuerlich: false },
                },
            };
            z.binde(&l.name.text, eintrag);
        }
        StmtArt::LetSonst(x) => {
            let eintrag = match &x.quelle {
                LetQuelle::Ruf(r) => {
                    for a in &r.argumente {
                        ausdruck(a, z, lage, absagen);
                    }
                    ruf_regel(r, z, lage, absagen);
                    match &r.ziel {
                        CallTarget::Path(p) => match finde_fn(lage.fns, lage.modul, p) {
                            Aufloesung::Gefunden(f) => match f.ergebnis {
                                Some(Schlitz::Kette(m)) => Eintrag::Kette(m),
                                _ => Eintrag::Fremd { natuerlich: false },
                            },
                            _ => Eintrag::Fremd { natuerlich: false },
                        },
                        CallTarget::Place(_) => Eintrag::Fremd { natuerlich: false },
                    }
                }
                LetQuelle::Ort(o) => {
                    ort_ausdruecke(o, z, lage, absagen);
                    if o.suffixe.is_empty() && z.kette(&o.basis.text).is_some() {
                        sort_ablehnung(
                            o.span,
                            "a string is no option: `let … else` unpacks nothing here",
                            absagen,
                        );
                    }
                    Eintrag::Fremd { natuerlich: false }
                }
            };
            let mut innen = z.innen();
            innen.binde(&x.fehlername.text, Eintrag::Fremd { natuerlich: false });
            block(&x.sonst, &innen, lage, absagen);
            toete_schreibziele(s, z);
            z.binde(&x.name.text, eintrag);
        }
        StmtArt::Zuweisung(zw) => {
            ort_ausdruecke(&zw.ziel, z, lage, absagen);
            ausdruck(&zw.wert, z, lage, absagen);
            match (zw.ziel.suffixe.is_empty(), z.kette(&zw.ziel.basis.text)) {
                (true, Some(max)) => match zw.op {
                    ZuwOp::Setzt => ziel_regel(&zw.wert, max, z, lage, absagen),
                    // `s += t` is `s = s + t`: the sum of maxes against
                    // `s`'s own max, which only a zero-max `t` fits.
                    ZuwOp::Plus => match synth(&zw.wert, z, lage) {
                        Some(m) if m > 0 => {
                            concat_ablehnung(zw.wert.span, max.saturating_add(m), max, absagen)
                        }
                        Some(_) => {}
                        None => sort_ablehnung(
                            zw.wert.span,
                            "a string and a non-string share one operation",
                            absagen,
                        ),
                    },
                    ZuwOp::Minus | ZuwOp::Und | ZuwOp::Oder => sort_ablehnung(
                        zw.ziel.span,
                        "strings share only `+` and comparisons: this operation is none",
                        absagen,
                    ),
                },
                // A field, an index, a global or a non-string local: no
                // slot there holds a string.
                _ => wert_ohne_kette(&zw.wert, z, lage, absagen),
            }
            toete_schreibziele(s, z);
        }
        StmtArt::Wenn(w) => {
            for (c, b) in &w.zweige {
                ausdruck(c, z, lage, absagen);
                wert_ohne_kette(c, z, lage, absagen);
                let mut innen = z.clone();
                innen.lerne(fakten(c, true, z));
                block(b, &innen, lage, absagen);
            }
            if let Some(b) = &w.sonst {
                block(b, z, lage, absagen);
            }
            let danach = match (w.zweige.as_slice(), &w.sonst) {
                ([(c, b)], None) if crate::endet_immer(b, &[]) => Some(fakten(c, false, z)),
                _ => None,
            };
            toete_schreibziele(s, z);
            if let Some(f) = danach {
                z.lerne(f);
            }
        }
        StmtArt::Match(m) => {
            ausdruck(&m.gegenstand, z, lage, absagen);
            wert_ohne_kette(&m.gegenstand, z, lage, absagen);
            for arm in &m.zweige {
                let mut innen = z.innen();
                if let Some(b) = &arm.binder {
                    innen.binde(&b.text, Eintrag::Fremd { natuerlich: false });
                }
                block(&arm.rumpf, &innen, lage, absagen);
            }
            toete_schreibziele(s, z);
        }
        StmtArt::Schleife(sch) => {
            // What the loop assigns is stale from the second pass on.
            let mut schleife = z.clone();
            toete_schreibziele(s, &mut schleife);
            match sch.as_ref() {
                Schleife::Traverse(t) => {
                    for e in t.gegenstand.iter().chain(t.mass.iter()) {
                        ausdruck(e, z, lage, absagen);
                        wert_ohne_kette(e, z, lage, absagen);
                    }
                    for o in domaene_orte(&t.domaene) {
                        ort_ausdruecke(o, z, lage, absagen);
                    }
                    let mut innen = schleife.innen();
                    innen.binde(&t.variable.text, Eintrag::Fremd { natuerlich: false });
                    if let Some(p) = &t.invariante {
                        praedikat(p, &innen, lage, absagen);
                    }
                    block(&t.rumpf, &innen, lage, absagen);
                }
                Schleife::Retry(r) => {
                    ausdruck(&r.schranke, z, lage, absagen);
                    for p in r.bis.iter().chain(r.invariante.iter()) {
                        praedikat(p, &schleife, lage, absagen);
                    }
                    block(&r.rumpf, &schleife, lage, absagen);
                }
                Schleife::Forever(f) => {
                    ausdruck(&f.je_durchgang, z, lage, absagen);
                    if let Some(p) = &f.invariante {
                        praedikat(p, &schleife, lage, absagen);
                    }
                    block(&f.rumpf, &schleife, lage, absagen);
                }
            }
            toete_schreibziele(s, z);
        }
        StmtArt::Bricht(x) => {
            block(&x.rumpf, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::Narrow(n) => {
            ort_ausdruecke(&n.ort, z, lage, absagen);
            if n.ort.suffixe.is_empty() && z.kette(&n.ort.basis.text).is_some() {
                sort_ablehnung(
                    n.ort.span,
                    "a string has no range to narrow: `narrow` is no string form",
                    absagen,
                );
            }
            if let NarrowZiel::Bereich(b) = &n.ziel {
                for e in [&b.von, &b.bis] {
                    ausdruck(e, z, lage, absagen);
                }
            }
            block(&n.sonst, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::Sperrt(x) => {
            block(&x.rumpf, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::Observiert(x) => {
            block(&x.rumpf, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::Child(b) => {
            block(b, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::Publish(p) => {
            ort_ausdruecke(&p.ziel, z, lage, absagen);
            ausdruck(&p.wert, z, lage, absagen);
            wert_ohne_kette(&p.wert, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        StmtArt::AwaitLoad(a) => {
            ort_ausdruecke(&a.quelle, z, lage, absagen);
            for o in &a.erwartet {
                ort_ausdruecke(o, z, lage, absagen);
            }
            z.binde(&a.name.text, Eintrag::Fremd { natuerlich: false });
        }
        StmtArt::Exchange(e) => {
            ort_ausdruecke(&e.ort, z, lage, absagen);
            match &e.form {
                XForm::Vergleich { wert, bedingung, .. } => {
                    ausdruck(wert, z, lage, absagen);
                    wert_ohne_kette(wert, z, lage, absagen);
                    praedikat(bedingung, z, lage, absagen);
                }
                XForm::Update { rumpf, .. } => block(rumpf, z, lage, absagen),
            }
            toete_schreibziele(s, z);
            z.binde(&e.name.text, Eintrag::Fremd { natuerlich: false });
        }
        StmtArt::Return(e) => {
            if let Some(wert) = e {
                ausdruck(wert, z, lage, absagen);
                match lage.ergebnis {
                    Some(Schlitz::Kette(max)) => ziel_regel(wert, max, z, lage, absagen),
                    _ => wert_ohne_kette(wert, z, lage, absagen),
                }
            }
        }
        StmtArt::Ruf(r) => {
            for a in &r.argumente {
                ausdruck(a, z, lage, absagen);
            }
            ruf_regel(r, z, lage, absagen);
        }
        StmtArt::LibraryCall(r) => {
            for a in &r.args {
                ausdruck(a, z, lage, absagen);
            }
            bibliothek_regel(r, z, lage, absagen);
        }
        StmtArt::Alloc(a) => {
            ausdruck(&a.wert, z, lage, absagen);
            wert_ohne_kette(&a.wert, z, lage, absagen);
            if let Some(t) = &a.typ {
                typ_annotation(t, false, absagen);
            }
            if let Some(b) = &a.sonst {
                block(b, z, lage, absagen);
            }
            toete_schreibziele(s, z);
            z.binde(&a.name.text, Eintrag::Fremd { natuerlich: false });
        }
        StmtArt::Grow(g) => {
            ausdruck(&g.mehr, z, lage, absagen);
            wert_ohne_kette(&g.mehr, z, lage, absagen);
            block(&g.sonst, z, lage, absagen);
            toete_schreibziele(s, z);
        }
        // No block, no expression, no binding.
        StmtArt::Leave(_) | StmtArt::Next(_) | StmtArt::ResetArena(_) | StmtArt::Start(_) => {}
    }
}

fn domaene_orte(d: &Domaene) -> Vec<&Ort> {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o) => vec![o],
        Domaene::KetteIn { ort, .. } => vec![ort],
        Domaene::FelderVon(_) | Domaene::Threads => Vec::new(),
    }
}

/// A predicate, scope-aware: a quantifier binds its variable.
fn praedikat(p: &Pred, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    match &p.art {
        PredArt::Vergleich(e) => ausdruck(e, z, lage, absagen),
        PredArt::Element(e, d) => {
            ausdruck(e, z, lage, absagen);
            for o in domaene_orte(d) {
                ort_ausdruecke(o, z, lage, absagen);
            }
        }
        PredArt::Klammer(x) | PredArt::Nicht(x) => praedikat(x, z, lage, absagen),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            praedikat(a, z, lage, absagen);
            praedikat(b, z, lage, absagen);
        }
        PredArt::Quantor(q) => {
            for o in domaene_orte(&q.domaene) {
                ort_ausdruecke(o, z, lage, absagen);
            }
            let mut innen = z.innen();
            innen.binde(&q.variable.text, Eintrag::Fremd { natuerlich: false });
            praedikat(&q.rumpf, &innen, lage, absagen);
        }
        PredArt::Erreicht { von, nach, .. } => {
            ort_ausdruecke(von, z, lage, absagen);
            ort_ausdruecke(nach, z, lage, absagen);
        }
        PredArt::Held { .. } => {}
    }
}

/// An expression and everything under it, scope-aware (`count` binds).
fn ausdruck(e: &Expr, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    expr_regel(e, z, lage, absagen);
    match &e.art {
        ExprArt::Zaehle {
            variable,
            domaene,
            rumpf,
        } => {
            for o in domaene_orte(domaene) {
                ort_ausdruecke(o, z, lage, absagen);
            }
            let mut innen = z.innen();
            innen.binde(&variable.text, Eintrag::Fremd { natuerlich: false });
            praedikat(rumpf, &innen, lage, absagen);
        }
        _ => {
            for k in crate::unterausdruecke(e) {
                ausdruck(k, z, lage, absagen);
            }
        }
    }
}

/// The index expressions of a place, walked, plus the place rule itself.
fn ort_ausdruecke(o: &Ort, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    ort_regel(o, z, lage, absagen);
    for e in crate::ausdruecke_im_ort(o) {
        ausdruck(e, z, lage, absagen);
    }
}

/// A value at a slot that holds no string.
fn wert_ohne_kette(e: &Expr, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    if synth(e, z, lage).is_some() {
        sort_ablehnung(e.span, "a string value at a slot that holds no string", absagen);
    }
}

/// A value flowing into a slot with max `ziel`: over-max `+` falls as
/// `N453`, any other over-max string as `N455`, a non-string literal as
/// `N455`.
fn ziel_regel(
    wert: &Expr,
    ziel: u128,
    z: &Zustand,
    lage: &Lage,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let Some(m) = synth(wert, z, lage) else {
        if ist_fremd_literal(wert) {
            sort_ablehnung(wert.span, "a non-string value where a string stands", absagen);
        }
        return;
    };
    if m <= ziel {
        return;
    }
    if matches!(&ohne_klammern(wert).art, ExprArt::Binaer(BinOp::Plus, _, _)) {
        concat_ablehnung(wert.span, m, ziel, absagen);
    } else {
        sort_ablehnung(
            wert.span,
            "a string past its slot: it holds more than the slot fits",
            absagen,
        );
    }
}

/// The rule at ONE expression node (its children are walked by
/// `ausdruck`).
fn expr_regel(x: &Expr, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    match &x.art {
        // The place rule runs at the node; `unterausdruecke` then yields
        // the index expressions for the walk.
        ExprArt::Ort(o) | ExprArt::Alt(o) => ort_regel(o, z, lage, absagen),
        ExprArt::Binaer(op, a, b) => match (synth(a, z, lage), synth(b, z, lage)) {
            (Some(_), Some(_)) if *op == BinOp::Plus || op.ist_vergleich() => {}
            (Some(_), Some(_)) => sort_ablehnung(
                x.span,
                "strings share only `+` and comparisons: this operation is none",
                absagen,
            ),
            (Some(_), None) | (None, Some(_)) => sort_ablehnung(
                x.span,
                "a string and a non-string share one operation",
                absagen,
            ),
            (None, None) => {}
        },
        ExprArt::Unaer(_, a) => {
            if synth(a, z, lage).is_some() {
                sort_ablehnung(
                    x.span,
                    "strings share only `+` and comparisons: this operation is none",
                    absagen,
                );
            }
        }
        ExprArt::ArrayLit(es) => {
            for e in es {
                wert_ohne_kette(e, z, lage, absagen);
            }
        }
        ExprArt::Eingebaut(g) => match &**g {
            Eingebaut::Lenof(_) => {}
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) => {
                if o.suffixe.is_empty() && z.kette(&o.basis.text).is_some() {
                    ort_ablehnung(
                        o.span,
                        "a bounded string has no layout yet: `sizeof` has nothing to measure",
                        absagen,
                    );
                }
            }
            Eingebaut::Sizeof(TypOderOrt::Typ(t)) => typ_annotation(t, false, absagen),
            Eingebaut::Aligned(a, b) => {
                wert_ohne_kette(a, z, lage, absagen);
                wert_ohne_kette(b, z, lage, absagen);
            }
        },
        ExprArt::Ruf(r) => ruf_regel(r, z, lage, absagen),
        ExprArt::LibraryCall(r) => bibliothek_regel(r, z, lage, absagen),
        ExprArt::Zahl(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::Wahr
        | ExprArt::Falsch
        | ExprArt::FnWert(_)
        | ExprArt::Klammer(_)
        // **Lane 261:** a string literal draws no refusal at its own node --
        // its byte length is held against the target max at the slot
        // (`ziel_regel`), and everywhere else it is a string value like any
        // other (`wert_ohne_kette`, the `Binaer` arms above).
        | ExprArt::Kette(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. }
        | ExprArt::Zaehle { .. } => {}
    }
}

/// A known string place: a plain read is fine, one index is the bounded
/// index rule, anything else (fields, chains) is no string form. An index
/// expression that is itself a string falls.
fn ort_regel(o: &Ort, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    for suf in &o.suffixe {
        if let OrtSuffix::Index(ix) = suf {
            if synth(ix, z, lage).is_some() {
                sort_ablehnung(ix.span, "a string value where an index stands", absagen);
            }
        }
    }
    let Some(max) = z.kette(&o.basis.text) else {
        return;
    };
    match o.suffixe.as_slice() {
        [] => {}
        [OrtSuffix::Index(ix)] => index_regel(ix, &o.basis.text, max, o.span, z, absagen),
        _ => sort_ablehnung(
            o.span,
            "a string carries no fields: one index reads a character, and that is all",
            absagen,
        ),
    }
}

/// Call arguments: at a string parameter a known string past the
/// parameter max falls (`N455`); at a non-string parameter any string
/// falls (`N455`); at a callee the pass cannot resolve, a string falls
/// (`N465`), and so does an ambiguous callee with a string in its head.
fn ruf_regel(r: &Ruf, z: &Zustand, lage: &Lage, absagen: &mut gabbro_syntax::diag::Absagen) {
    let unaufgeloest = |absagen: &mut gabbro_syntax::diag::Absagen| {
        for a in &r.argumente {
            if synth(a, z, lage).is_some() {
                ort_ablehnung(
                    a.span,
                    "a string value reaches a callee the length discipline cannot resolve",
                    absagen,
                );
            }
        }
    };
    let CallTarget::Path(p) = &r.ziel else {
        unaufgeloest(absagen);
        return;
    };
    if crate::ist_praedikatswort(r) {
        return;
    }
    let f = match finde_fn(lage.fns, lage.modul, p) {
        Aufloesung::Gefunden(f) => f,
        Aufloesung::Mehrdeutig(kette) => {
            if kette {
                ort_ablehnung(
                    r.span,
                    "the callee is ambiguous and one candidate carries a string: the length \
                     discipline cannot tell which max holds",
                    absagen,
                );
            }
            unaufgeloest(absagen);
            return;
        }
        Aufloesung::Keiner => {
            unaufgeloest(absagen);
            return;
        }
    };
    for (arg, (_, ptyp)) in r.argumente.iter().zip(f.params.iter()) {
        match ptyp {
            Schlitz::Kette(slot) => {
                if let Some(m) = synth(arg, z, lage) {
                    if m > *slot {
                        sort_ablehnung(
                            arg.span,
                            "a string past its slot: the argument holds more than the parameter fits",
                            absagen,
                        );
                    }
                } else if ist_fremd_literal(arg) {
                    sort_ablehnung(arg.span, "a non-string value where a string stands", absagen);
                }
            }
            Schlitz::Fremd { .. } => {
                if synth(arg, z, lage).is_some() {
                    sort_ablehnung(
                        arg.span,
                        "a string value at a parameter that holds no string",
                        absagen,
                    );
                }
            }
        }
    }
}

fn bibliothek_regel(
    r: &LibraryCall,
    z: &Zustand,
    lage: &Lage,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    for a in &r.args {
        if synth(a, z, lage).is_some() {
            ort_ablehnung(
                a.span,
                "a string value reaches a callee the length discipline cannot resolve",
                absagen,
            );
        }
    }
}

// --- The refusals. Every sentence below has its `Satz` in `saetze.rs`.

fn concat_ablehnung(span: Span, summe: u128, ziel: u128, absagen: &mut gabbro_syntax::diag::Absagen) {
    absagen.schiebe(
        Absage::fehler(
            "N453",
            span,
            format!(
                "the concatenation holds up to {summe} characters, but the slot fits at most {ziel}"
            ),
        )
        .mit_notiz(
            "lengths add like `u32` bounds: `string max A + string max B` holds up to \
             A+B, and a slot that fits fewer refuses the sum -- split the target or \
             narrow the sources",
        ),
    );
}

/// The index rule: a literal at or past the max is out of range on every
/// value; below the max it still needs a length fact; a name needs the
/// fact `i < lenof(s)`; anything else proves nothing.
fn index_regel(
    ix: &Expr,
    s: &str,
    max: u128,
    span: Span,
    z: &Zustand,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let geschuetzt_notiz = "a bounded string holds anywhere from zero to its max characters, so \
                            the max proves no index; guard the read with its length: \
                            `if lenof(s) > k { … s[k] … }` for a literal, `if i < lenof(s)` \
                            for an unsigned name, or `requires` the same at the head";
    match &ohne_klammern(ix).art {
        ExprArt::Zahl(k) if *k >= max => absagen.schiebe(
            Absage::fehler(
                "N454",
                span,
                format!("index {k} is past the string: it holds at most {max} characters"),
            )
            .mit_notiz(
                "a bounded string holds anywhere from zero to its max characters; an \
                 index the max itself cannot hold is out of range on every value",
            ),
        ),
        ExprArt::Zahl(k) => {
            if z.mindestens.get(s).is_some_and(|n| k < n) {
                return;
            }
            absagen.schiebe(
                Absage::fehler(
                    "N454",
                    span,
                    format!(
                        "index {k} is not shown below the length: the string may hold fewer \
                         than {} characters",
                        k.saturating_add(1)
                    ),
                )
                .mit_notiz(geschuetzt_notiz),
            );
        }
        ExprArt::Ort(o)
            if o.suffixe.is_empty()
                && z.unter.contains(&(o.basis.text.clone(), s.to_string())) => {}
        _ => absagen.schiebe(
            Absage::fehler(
                "N454",
                span,
                "the index proves nothing: no fact shows it stands below the length",
            )
            .mit_notiz(geschuetzt_notiz),
        ),
    }
}

fn sort_ablehnung(span: Span, satz: &str, absagen: &mut gabbro_syntax::diag::Absagen) {
    absagen.schiebe(
        Absage::fehler("N455", span, satz.to_string()).mit_notiz(
            "strings are their own sort: a string flows only into a `string max N` \
             slot that fits it, shares only `+` and comparisons with strings, and \
             carries no fields",
        ),
    );
}

fn ort_ablehnung(span: Span, satz: &str, absagen: &mut gabbro_syntax::diag::Absagen) {
    absagen.schiebe(
        Absage::fehler("N465", span, satz.to_string()).mit_notiz(
            "a bounded string lives in parameters, results and locals only: that is \
             where its length is followed; a field, a constant, a table slot, a \
             nested type or an unresolved callee would carry it past every check",
        ),
    );
}

/// The max bound (lane 261, `N486`): a max of zero holds nothing and has no
/// object form, and a max past `MAX_OBERGRENZE` (65535) the unit cannot
/// allocate -- one length word plus `max` bytes per value.
fn max_regel(max: u128, span: Span, absagen: &mut gabbro_syntax::diag::Absagen) {
    if max_traegt(max) {
        return;
    }
    absagen.schiebe(
        Absage::fehler(
            "N486",
            span,
            if max == 0 {
                "a `string max 0` holds no character and has no object form".to_string()
            } else {
                format!(
                    "a `string max {max}` the unit cannot allocate: one length word plus \
                     {max} bytes per value past the bound of {MAX_OBERGRENZE}"
                )
            },
        )
        .mit_notiz(
            "a bounded string is a length word plus its max in bytes, allocated \
             where it stands; a larger max is a larger stack frame or static, \
             and zero holds nothing at all",
        ),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_in_max_wird_angenommen() {
        assert!(literal_passt(8, 2));
        assert!(literal_passt(8, 8));
    }

    #[test]
    fn literal_ueber_max_wird_verweigert() {
        assert!(!literal_passt(8, 9));
    }

    #[test]
    fn max_schranke_traegt_1_bis_65535() {
        assert!(max_traegt(1));
        assert!(max_traegt(8));
        assert!(max_traegt(MAX_OBERGRENZE));
        assert_eq!(MAX_OBERGRENZE, 65535);
    }

    #[test]
    fn max_schranke_verweigert_null_und_ueber() {
        assert!(!max_traegt(0));
        assert!(!max_traegt(65536));
        assert!(!max_traegt(u128::MAX));
    }

    #[test]
    fn concat_in_max_meldet_summe() {
        assert_eq!(concat_passt(8, 2, 1), Some(3));
        assert_eq!(concat_passt(8, 4, 4), Some(8));
    }

    #[test]
    fn concat_ueber_max_wird_verweigert() {
        assert_eq!(concat_passt(8, 5, 4), None);
        assert_eq!(concat_passt(2, 2, 1), None);
    }

    #[test]
    fn concat_summenueberlauf_wird_verweigert() {
        assert_eq!(concat_passt(usize::MAX, usize::MAX, 1), None);
    }

    #[test]
    fn index_innen_wird_angenommen_aussen_verweigert() {
        assert!(index_passt(3, 0));
        assert!(index_passt(3, 2));
        assert!(!index_passt(3, 3));
        assert!(!index_passt(0, 0));
    }
}
