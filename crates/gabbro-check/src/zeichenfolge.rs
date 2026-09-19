//! Bounded strings: the length discipline (lane 256), wired as a pass.
//!
//! A bounded string carries its declared maximum the way `u32` carries
//! `in 0 .. N`. Lengths are tracked like M101-family bounds: `+` on two
//! strings concatenates (lengths add, refused past the target max),
//! `lenof` reads the length, `s[k]` indexes (in-range or refused), and
//! `==`/`<` compare. Unbounded strings have no form and stay refused by
//! name (no constructor here takes no max).
//!
//! The shared type system reads `string max N` as `Unbekannt`
//! (`umgebung.rs`); this pass tracks declared maxes in its own table and
//! decides. It fires ONLY on positive string knowledge (a name declared
//! `string max N`, a `+` of two known strings, a provable literal) and
//! stays silent on ignorance -- so it cannot false-fire where it cannot
//! see. The three codes are `N453` (concat past the target max), `N454`
//! (index not provably in range) and `N455` (sort: a non-string where a
//! string stands, or the reverse).
//!
//! The pure length arithmetic below mirrors
//! `grammatik/Grammatik/ZeichenfolgeGebunden.lean`
//! (`BString`, `bliteral`, `bconcat`, `bindex`).
//!
//! ## Scope cuts (all end-to-end safe: the emitter stops every string
//! ## program with `C001`, so nothing below can leak into C)
//!
//! - No literals: `"hi"` stays `P011` (a literal needs an `ExprArt` arm,
//!   and `m1::ausdruck_roh` is exhaustive over `ExprArt` in a file this
//!   lane must not touch). String sources are parameters, `extern` returns
//!   and inferred `let`s.
//! - Lengths are max-bounds, never exact: with no literals no exact length
//!   ever arises. `s[k]` with `k` below the max is accepted the M103 way,
//!   and the lowering lane owes the exact-length side (a runtime length
//!   check or exactness tracking) before it lowers any index.
//! - A non-literal index is refused (unprovable against an unknown exact
//!   length), and flow-narrowed indices (`if i < lenof(s)`) are refused
//!   with it: this pass cannot see m1's narrowing facts.
//! - Call arguments at string parameters are held (`N455` past the max);
//!   anything else about calls (arity, unknown callees) stays m1's.
//! - Contracts (`requires`/`ensures`), `const`/`static` initializers,
//!   table slots and `LetSonst` sources are not string-checked: without
//!   literals no honest constant string exists, and ghost positions need
//!   the lowering lane's value model first.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Absage;
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// A literal fits exactly when its known length fits the declared max.
pub fn literal_passt(max: usize, len: usize) -> bool {
    len <= max
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

/// What the pass knows about one bound name: a string with this max, or a
/// name known to hold no string. Absence means ignorance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Eintrag {
    Kette(u128),
    Fremd,
}

/// A declared slot: a string max, or a known non-string type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Schlitz {
    Kette(u128),
    Fremd,
}

fn schlitz_von(t: &TypExpr) -> Schlitz {
    match t {
        TypExpr::Zeichenkette { max, .. } => Schlitz::Kette(*max),
        _ => Schlitz::Fremd,
    }
}

/// A callee's string-relevant signature, owned (the AST borrows do not
/// outlive the item walk).
#[derive(Debug, Clone)]
struct RumpfSignatur {
    params: Vec<(String, Schlitz)>,
    ergebnis: Option<Schlitz>,
}

/// The pass: bounded-string length discipline over function and `check`
/// bodies. Same column as M1 (no pass number of its own, like
/// `kontexte::pass`): the lengths rhyme with the M101 family, and the
/// shared passes step aside over `Unbekannt`.
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
        match &item.art {
            ItemArt::Funktion(f) => {
                if let FnRumpf::Block(b) = &f.rumpf {
                    let params: Vec<(String, Schlitz)> = f
                        .parameter
                        .iter()
                        .map(|p| (p.name.text.clone(), schlitz_von(&p.typ)))
                        .collect();
                    let ergebnis = f.ergebnis.as_ref().map(schlitz_von);
                    pruefe_rumpf(b, &params, &ergebnis, &fns, modul, absagen);
                }
            }
            ItemArt::Check(c) => {
                pruefe_rumpf(&c.can_fail, &[], &None, &fns, modul, absagen);
            }
            _ => {}
        }
    });
}

/// Jennings' resolver, deliberately small: exact `modul::pfad` first, then
/// a last-segment match that must be unique in the unit. Method calls
/// (`CallTarget::Place`) never resolve here.
fn finde_fn(
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    p: &Pfad,
) -> Option<RumpfSignatur> {
    if let Some(f) = fns.get(&format!("{modul}::{}", p.text())) {
        return Some(f.clone());
    }
    let mut treffer: Option<RumpfSignatur> = None;
    for (k, f) in fns {
        if k.rsplit("::").next() == p.teile.last().map(|i| i.text.as_str()) {
            if treffer.is_some() {
                return None;
            }
            treffer = Some(f.clone());
        }
    }
    treffer
}

fn trage_ein(scope: &mut HashMap<String, Option<Eintrag>>, name: &str, neu: Eintrag) {
    match scope.get(name) {
        None => {
            scope.insert(name.to_string(), Some(neu));
        }
        Some(Some(alt)) if alt == &neu => {}
        // Shadowed or re-bound incompatibly: stop deciding this name.
        // A miss, never a false fire.
        _ => {
            scope.insert(name.to_string(), None);
        }
    }
}

/// A bound name's string entry, if it holds exactly one.
fn kette_von(scope: &HashMap<String, Option<Eintrag>>, name: &str) -> Option<u128> {
    match scope.get(name) {
        Some(Some(Eintrag::Kette(m))) => Some(*m),
        _ => None,
    }
}

/// A bound name known to hold no string.
fn ist_fremd(scope: &HashMap<String, Option<Eintrag>>, name: &str) -> bool {
    matches!(scope.get(name), Some(Some(Eintrag::Fremd)))
}

/// The string max an expression provably holds, or `None` on ignorance.
/// `+` of two known strings sums (saturating: a sum that overflows `u128`
/// can only refuse harder downstream, never accept).
fn synth(
    e: &Expr,
    scope: &HashMap<String, Option<Eintrag>>,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
) -> Option<u128> {
    match &e.art {
        ExprArt::Klammer(x) => synth(x, scope, fns, modul),
        ExprArt::Ort(o) if o.suffixe.is_empty() => kette_von(scope, &o.basis.text),
        ExprArt::Binaer(BinOp::Plus, a, b) => match (synth(a, scope, fns, modul), synth(b, scope, fns, modul)) {
            (Some(x), Some(y)) => Some(x.saturating_add(y)),
            _ => None,
        },
        ExprArt::Ruf(r) => match &r.ziel {
            CallTarget::Path(p) => match finde_fn(fns, modul, p).and_then(|f| f.ergebnis) {
                Some(Schlitz::Kette(max)) => Some(max),
                _ => None,
            },
            CallTarget::Place(_) => None,
        },
        _ => None,
    }
}

/// Without brackets: `(x)` is `x`, however deep.
fn ohne_klammern<'a>(mut e: &'a Expr) -> &'a Expr {
    while let ExprArt::Klammer(x) = &e.art {
        e = x;
    }
    e
}

/// A provably non-string value: a literal of another sort. Anything else
/// may be anything (calls, places of unknown type), and stays silent.
fn ist_fremd_literal(e: &Expr) -> bool {
    matches!(
        &ohne_klammern(e).art,
        ExprArt::Zahl(_)
            | ExprArt::Gleitkomma { .. }
            | ExprArt::Wahr
            | ExprArt::Falsch
    )
}

fn sammle_lets(
    b: &Block,
    scope: &mut HashMap<String, Option<Eintrag>>,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
) {
    for s in &b.anweisungen {
        if let StmtArt::Let(l) = &s.art {
            match &l.typ {
                Some(t) => trage_ein(
                    scope,
                    &l.name.text,
                    match schlitz_von(t) {
                        Schlitz::Kette(m) => Eintrag::Kette(m),
                        Schlitz::Fremd => Eintrag::Fremd,
                    },
                ),
                // Unannotated: infer from a known-string initializer, and
                // only then. Anything else stays unknown, never `Fremd`.
                None => {
                    if let Some(m) = synth(&l.wert, scope, fns, modul) {
                        trage_ein(scope, &l.name.text, Eintrag::Kette(m));
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_lets(k, scope, fns, modul);
        }
    }
}

fn pruefe_rumpf(
    b: &Block,
    params: &[(String, Schlitz)],
    ergebnis: &Option<Schlitz>,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let mut scope: HashMap<String, Option<Eintrag>> = HashMap::new();
    for (n, s) in params {
        trage_ein(
            &mut scope,
            n,
            match s {
                Schlitz::Kette(m) => Eintrag::Kette(*m),
                Schlitz::Fremd => Eintrag::Fremd,
            },
        );
    }
    sammle_lets(b, &mut scope, fns, modul);
    let lage = Lage {
        scope,
        ergebnis: *ergebnis,
    };
    gehe_block(b, &lage, fns, modul, absagen);
}

struct Lage {
    scope: HashMap<String, Option<Eintrag>>,
    ergebnis: Option<Schlitz>,
}

fn gehe_block(
    b: &Block,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    for s in &b.anweisungen {
        stmt_regel(s, lage, fns, modul, absagen);
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                expr_regel(x, lage, fns, modul, absagen);
            }
        }
        for k in crate::unterbloecke(s) {
            gehe_block(k, lage, fns, modul, absagen);
        }
    }
}

/// Statement positions with a declared string target: annotated `let`,
/// assignment to a known string place, `return` at a string result.
fn stmt_regel(
    s: &Stmt,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    match &s.art {
        StmtArt::Let(l) => {
            if let Some(TypExpr::Zeichenkette { max, .. }) = &l.typ {
                ziel_regel(&l.wert, *max, lage, fns, modul, absagen);
            }
            if let Some(t) = &l.typ {
                if !matches!(t, TypExpr::Zeichenkette { .. })
                    && synth(&l.wert, &lage.scope, fns, modul).is_some()
                {
                    sort_ablehnung(
                        l.wert.span,
                        "a string value at a slot that holds no string",
                        lage,
                        absagen,
                    );
                }
            }
        }
        StmtArt::Zuweisung(z) => {
            // The target place itself: an index there still reads.
            ort_regel(&z.ziel, lage, fns, modul, absagen);
            if z.ziel.suffixe.is_empty() {
                if let Some(max) = kette_von(&lage.scope, &z.ziel.basis.text) {
                    ziel_regel(&z.wert, max, lage, fns, modul, absagen);
                }
                if ist_fremd(&lage.scope, &z.ziel.basis.text)
                    && synth(&z.wert, &lage.scope, fns, modul).is_some()
                {
                    sort_ablehnung(
                        z.wert.span,
                        "a string value at a slot that holds no string",
                        lage,
                        absagen,
                    );
                }
            }
        }
        StmtArt::Ruf(r) => {
            ruf_regel(r, lage, fns, modul, absagen);
            for a in &r.argumente {
                for x in crate::alle_ausdruecke(a) {
                    expr_regel(x, lage, fns, modul, absagen);
                }
            }
        }
        StmtArt::Return(e) => {
            if let (Some(wert), Some(Schlitz::Kette(max))) = (e.as_ref(), lage.ergebnis) {
                ziel_regel(wert, max, lage, fns, modul, absagen);
            }
            if let (Some(wert), Some(Schlitz::Fremd)) = (e.as_ref(), lage.ergebnis) {
                if synth(wert, &lage.scope, fns, modul).is_some() {
                    sort_ablehnung(
                        wert.span,
                        "a string value where the result holds no string",
                        lage,
                        absagen,
                    );
                }
            }
        }
        _ => {}
    }
}

/// A known-string value flowing into a slot with max `ziel`: over-max
/// `+` falls as `N453`, any other over-max string as `N455`.
fn ziel_regel(
    wert: &Expr,
    ziel: u128,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let Some(m) = synth(wert, &lage.scope, fns, modul) else {
        if ist_fremd_literal(wert) {
            sort_ablehnung(
                wert.span,
                "a non-string value where a string stands",
                lage,
                absagen,
            );
        }
        return;
    };
    if m <= ziel {
        return;
    }
    if matches!(&ohne_klammern(wert).art, ExprArt::Binaer(BinOp::Plus, _, _)) {
        concat_ablehnung(wert.span, m, ziel, lage, absagen);
    } else {
        sort_ablehnung(
            wert.span,
            "a string past its slot: it holds more than the slot fits",
            lage,
            absagen,
        );
    }
}

fn expr_regel(
    x: &Expr,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    match &x.art {
        ExprArt::Ort(o) => ort_regel(o, lage, fns, modul, absagen),
        ExprArt::Binaer(op, a, b) => {
            let (sa, sb) = (
                synth(a, &lage.scope, fns, modul),
                synth(b, &lage.scope, fns, modul),
            );
            match (sa, sb) {
                // `+` of two strings is concat (the target rule decides);
                // comparisons of two strings order them. Anything else with
                // two strings, and any operation with exactly one string
                // side, is no string form.
                (Some(_), Some(_)) if *op == BinOp::Plus || op.ist_vergleich() => {}
                (Some(_), Some(_)) => sort_ablehnung(
                    x.span,
                    "strings share only `+` and comparisons: this operation is none",
                    lage,
                    absagen,
                ),
                (Some(_), None) | (None, Some(_)) => sort_ablehnung(
                    x.span,
                    "a string and a non-string share one operation",
                    lage,
                    absagen,
                ),
                (None, None) => {}
            }
        }
        ExprArt::Eingebaut(g) => match &**g {
            Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                ort_regel(o, lage, fns, modul, absagen);
            }
            _ => {}
        },
        ExprArt::Ruf(r) => ruf_regel(r, lage, fns, modul, absagen),
        _ => {}
    }
}

/// A known string place: a plain read is fine, one index is the bounded
/// index rule, anything else (fields, chains) is no string form.
fn ort_regel(
    o: &Ort,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let Some(max) = kette_von(&lage.scope, &o.basis.text) else {
        return;
    };
    match o.suffixe.as_slice() {
        [] => {}
        [OrtSuffix::Index(ix)] => index_regel(ix, max, o.span, lage, fns, modul, absagen),
        _ => sort_ablehnung(
            o.span,
            "a string carries no fields: one index reads a character, and that is all",
            lage,
            absagen,
        ),
    }
}

/// Call arguments at string parameters: a known string past the
/// parameter max falls; anything unknown stays silent.
fn ruf_regel(
    r: &Ruf,
    lage: &Lage,
    fns: &HashMap<String, RumpfSignatur>,
    modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    let CallTarget::Path(p) = &r.ziel else {
        return;
    };
    let Some(f) = finde_fn(fns, modul, p) else {
        return;
    };
    for (arg, (_, ptyp)) in r.argumente.iter().zip(f.params.iter()) {
        match ptyp {
            Schlitz::Kette(slot) => {
                if let Some(m) = synth(arg, &lage.scope, fns, modul) {
                    if m > *slot {
                        sort_ablehnung(
                            arg.span,
                            "a string past its slot: the argument holds more than the parameter fits",
                            lage,
                            absagen,
                        );
                    }
                }
            }
            Schlitz::Fremd => {
                if synth(arg, &lage.scope, fns, modul).is_some() {
                    sort_ablehnung(
                        arg.span,
                        "a string value at a parameter that holds no string",
                        lage,
                        absagen,
                    );
                }
            }
        }
    }
}

// --- The three refusals. Each fires once per fault; every sentence below
// --- has its `Satz` in `saetze.rs` in the same commit.

fn concat_ablehnung(
    span: Span,
    summe: u128,
    ziel: u128,
    _lage: &Lage,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
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

fn index_regel(
    ix: &Expr,
    max: u128,
    span: Span,
    _lage: &Lage,
    _fns: &HashMap<String, RumpfSignatur>,
    _modul: &str,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    // Lengths are max-bounds, never exact: a literal below the max is
    // accepted the M103 way (the lowering lane owes the exact-length
    // side), a literal at or past the max is statically out of range,
    // and a computed index proves nothing against an unknown exact
    // length.
    match &ohne_klammern(ix).art {
        ExprArt::Zahl(k) if *k >= max => absagen.schiebe(
            Absage::fehler(
                "N454",
                span,
                format!(
                    "index {k} is past the string: it holds at most {max} characters"
                ),
            )
            .mit_notiz(
                "a bounded string holds anywhere from zero to its max characters; an \
                 index the max itself cannot hold is out of range on every value",
            ),
        ),
        ExprArt::Zahl(_) => {}
        _ => absagen.schiebe(
            Absage::fehler(
                "N454",
                span,
                "the index proves nothing: a computed index cannot show it stands below the length",
            )
            .mit_notiz(
                "lengths are max-bounds, not exact counts -- only a literal below the max \
                 is statically in range; narrow the index to a literal first",
            ),
        ),
    }
}

fn sort_ablehnung(
    span: Span,
    satz: &str,
    _lage: &Lage,
    absagen: &mut gabbro_syntax::diag::Absagen,
) {
    absagen.schiebe(
        Absage::fehler("N455", span, satz.to_string()).mit_notiz(
            "strings are their own sort: a string flows only into a `string max N` \
             slot that fits it, shares only `+` and comparisons with strings, and \
             carries no fields",
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
