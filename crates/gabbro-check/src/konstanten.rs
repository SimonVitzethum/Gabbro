//! Lane 111 -- compile-time constants, first cut (PLAN-BITS.md section 6).
//!
//! The checker evaluates total, effect-free `const` initializers and const
//! tables element-wise and prints the values as a Lean certificate (encoding
//! N of the certificate measurement). This pass holds the fragment the
//! small interpreter (`Umgebung::konst_wert`) actually computes:
//!
//! | code | what falls |
//! |---|---|
//! | `K190` | a `const` initializer, or a table element, outside the evaluable fragment |
//! | `K191` | a table literal whose length differs from the declared count |
//! | `K192` | a `const` calling, directly or through `const fn`, a function that is not `pure` |
//! | `K193` | unbounded recursion in const evaluation: a reference cycle through a `const` |
//! | `K194` | a table element evaluating outside the declared element range |
//!
//! ## What this pass does NOT do (booked, not forgotten)
//!
//! * Scalar `const` ranges stay `M101`'s: `m1` types every scalar initializer,
//!   so a second range check here would refuse one fault twice. Table literals
//!   are `Unbekannt` at `m1` by construction, hence `K194` owns their range.
//! * Function-only recursion stays `K008`/`K009`/`H022`'s: a cycle with no
//!   `const` in it is refused where it stands, and this pass stays silent on
//!   it -- including the `K190` it would otherwise owe for the unfoldable
//!   call. Only a cycle through a `const` is unbounded *as const
//!   evaluation*, because a `const` carries no `decreases` by grammar shape.
//! * Non-recursive callees without `decreases` are accepted: the bound is
//!   owed where unboundedness lives, which is the same line `K008` draws.
//!   A `const fn` that calls itself WITH `decreases` still exceeds the
//!   single-unfolding folder and falls at `K190`, honestly named.
//! * Float `const` stay silent: the fragment is integers (`Gleitkomma` never
//!   folds, and neither does a use of a float `const` -- a bare `Ort` is not
//!   a foreign node, so float chains pass through untouched).
//! * `~` stays the emitter's (`C001`, gift 445): every `~` shape is refused
//!   elsewhere already (`M137` over literals), so a second refusal here
//!   would be the worse-than-one this tree forbids.
//! * Division by zero stays `M102`'s: the denominator range always contains
//!   zero there, so `K190` skips null denominators the same way.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

use crate::umgebung::{Umgebung, qualifiziere};

/// Purity of a declared function: exactly `effects { pure }`.
fn ist_rein(decl: &FnDecl) -> bool {
    match &decl.effects {
        Some(w) => w.liste.len() == 1 && matches!(w.liste[0].art, WirkungArt::Rein),
        None => false,
    }
}

/// The single return expression of a `const fn`, if it has that shape.
fn konst_rumpf(decl: &FnDecl) -> Option<&Expr> {
    if !matches!(decl.klasse, Some(FnKlasse::Konst)) {
        return None;
    }
    match &decl.rumpf {
        FnRumpf::Block(b) => match &b.anweisungen[..] {
            [s] => match &s.art {
                StmtArt::Return(Some(w)) => Some(w),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// The declaration index this pass reads: functions and consts by qualified
/// name. Owned clones: the module walk lends items to the closure body only,
/// so borrowed references cannot outlive it.
struct Karte {
    funktionen: HashMap<String, (String, FnDecl)>,
    konstanten: HashMap<String, (String, KonstDecl)>,
}

impl Karte {
    fn von(baum: &Programm) -> Karte {
        let mut k = Karte {
            funktionen: HashMap::new(),
            konstanten: HashMap::new(),
        };
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
            ItemArt::Funktion(f) => {
                k.funktionen.insert(
                    qualifiziere(modul, &f.name.text),
                    (modul.to_string(), f.clone()),
                );
            }
            ItemArt::Konst(c) => {
                k.konstanten
                    .insert(qualifiziere(modul, &c.name.text), (modul.to_string(), c.clone()));
            }
            _ => {}
        });
        k
    }

    /// Resolve a call path the way the folder does: module chain, first hit.
    fn funktion(&self, u: &Umgebung, von: &str, pfad: &str) -> Option<(&String, &FnDecl)> {
        let treffer = u
            .kandidaten_aufloesbar(von, pfad)
            .into_iter()
            .find(|k| self.funktionen.contains_key(k))?;
        self.funktionen.get(&treffer).map(|(m, f)| (m, f))
    }

    /// Resolve a bare name to a `const`, if it names one.
    fn konstante(&self, u: &Umgebung, von: &str, name: &str) -> Option<&(String, KonstDecl)> {
        let treffer = u
            .kandidaten_aufloesbar(von, name)
            .into_iter()
            .find(|k| self.konstanten.contains_key(k))?;
        self.konstanten.get(&treffer)
    }
}

/// Nodes of the const-evaluation graph: consts and transparent `const fn`s.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Knoten {
    Konst(String),
    Funk(String),
}

/// The outcome of the hull walk for one `const`: which refusals it owes.
#[derive(Default)]
struct Huelle {
    unrein: Vec<Span>,
    kreis_durch_konst: Vec<Span>,
    kreis_ohne_konst: bool,
}

/// Walk every `Ruf` and every bare-`const` `Ort` under `e`. `params` holds the
/// bound parameter names of the enclosing `const fn`, which shadow consts.
fn huelle_expr(
    u: &Umgebung,
    karte: &Karte,
    von: &str,
    e: &Expr,
    params: &HashSet<String>,
    besucht: &mut HashSet<Knoten>,
    stapel: &mut Vec<Knoten>,
    out: &mut Huelle,
) {
    for x in crate::alle_ausdruecke(e) {
        match &x.art {
            ExprArt::Ruf(r) => {
                let Some(pfad) = r.path() else { continue };
                let Some((fmod, decl)) = karte.funktion(u, von, &pfad.text()) else {
                    continue;
                };
                if !ist_rein(decl) {
                    out.unrein.push(r.span);
                    continue;
                }
                if konst_rumpf(decl).is_none() {
                    continue;
                }
                let schluessel = qualifiziere(fmod, &decl.name.text);
                huelle_funk(u, karte, &schluessel, besucht, stapel, out);
            }
            ExprArt::Ort(o) => {
                if !o.suffixe.is_empty() || params.contains(&o.basis.text) {
                    continue;
                }
                let Some((cmod, _)) = karte.konstante(u, von, &o.basis.text) else {
                    continue;
                };
                let schluessel = qualifiziere(cmod, &o.basis.text);
                huelle_konst(u, karte, &schluessel, besucht, stapel, out);
            }
            _ => {}
        }
    }
}

fn huelle_konst(
    u: &Umgebung,
    karte: &Karte,
    name: &str,
    besucht: &mut HashSet<Knoten>,
    stapel: &mut Vec<Knoten>,
    out: &mut Huelle,
) {
    let knoten = Knoten::Konst(name.to_string());
    if stapel.contains(&knoten) {
        out.kreis_durch_konst.push(knoten_span(karte, &knoten));
        return;
    }
    if !besucht.insert(knoten.clone()) {
        return;
    }
    stapel.push(knoten);
    if let Some((cmod, decl)) = karte.konstanten.get(name) {
        let params = HashSet::new();
        huelle_expr(u, karte, cmod, &decl.wert, &params, besucht, stapel, out);
    }
    stapel.pop();
}

fn huelle_funk(
    u: &Umgebung,
    karte: &Karte,
    name: &str,
    besucht: &mut HashSet<Knoten>,
    stapel: &mut Vec<Knoten>,
    out: &mut Huelle,
) {
    let knoten = Knoten::Funk(name.to_string());
    if stapel.contains(&knoten) {
        if stapel.iter().any(|k| matches!(k, Knoten::Konst(_))) {
            out.kreis_durch_konst.push(knoten_span(karte, &knoten));
        } else {
            out.kreis_ohne_konst = true;
        }
        return;
    }
    if !besucht.insert(knoten.clone()) {
        return;
    }
    stapel.push(knoten);
    if let Some((fmod, decl)) = karte.funktionen.get(name) {
        if let Some(rumpf) = konst_rumpf(decl) {
            let params: HashSet<String> = decl
                .parameter
                .iter()
                .map(|p| p.name.text.clone())
                .collect();
            huelle_expr(u, karte, fmod, rumpf, &params, besucht, stapel, out);
        }
    }
    stapel.pop();
}

fn knoten_span(karte: &Karte, knoten: &Knoten) -> Span {
    match knoten {
        Knoten::Konst(n) => karte.konstanten.get(n).map(|(_, c)| c.name.span),
        Knoten::Funk(n) => karte.funktionen.get(n).map(|(_, f)| f.name.span),
    }
    .unwrap_or(Span { von: 0, bis: 0 })
}

/// Nodes the folder never handles: calls, carrier reads, layout queries,
/// quantified counts, entry/return values, reason values, function values,
/// indirect calls. Literals, bare const uses, parentheses, `!`/`-` and the
/// binary operators are native to it.
fn ist_fremd(e: &Expr) -> bool {
    crate::alle_ausdruecke(e).iter().any(|x| match &x.art {
        ExprArt::Ruf(_)
        | ExprArt::LibraryCall(_)
        | ExprArt::Zaehle { .. }
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. }
        | ExprArt::FnWert(_) => true,
        ExprArt::Ort(o) => !o.suffixe.is_empty(),
        _ => false,
    })
}

/// A `~` anywhere inside: the emitter's shape (`C001`, `M137` over literals).
fn hat_bitnicht(e: &Expr) -> bool {
    crate::alle_ausdruecke(e)
        .iter()
        .any(|x| matches!(&x.art, ExprArt::Unaer(UnOp::BitNicht, _)))
}

/// A float literal anywhere inside: the fragment is integers.
fn hat_gleitkomma(e: &Expr) -> bool {
    crate::alle_ausdruecke(e)
        .iter()
        .any(|x| matches!(&x.art, ExprArt::Gleitkomma { .. }))
}

/// Division or remainder with a denominator folding to zero: `M102` owns it.
fn hat_nullnenner(u: &Umgebung, von: &str, e: &Expr) -> bool {
    crate::alle_ausdruecke(e).iter().any(|x| match &x.art {
        ExprArt::Binaer(BinOp::Geteilt, _, nenner)
        | ExprArt::Binaer(BinOp::Rest, _, nenner) => {
            u.konst_wert(von, nenner) == Some(0)
        }
        _ => false,
    })
}

fn k190(span: Span, name: &str) -> Absage {
    Absage::fehler(
        "K190",
        span,
        format!(
            "`{name}` is not a compile-time constant of the evaluable fragment \
             (integer literals, other consts, arithmetic and bit operators, calls \
             of `pure` single-return `const fn`): table reads, layout queries, \
             indirect calls and block-bodied calls do not fold"
        ),
    )
    .mit_notiz("PLAN-BITS.md section 6: the checker evaluates the total, effect-free fragment")
}

/// Hold one scalar `const` against the fragment. Silent unless the initializer
/// is an integer shape the folder should have folded.
fn pruefe_skalar(
    u: &Umgebung,
    karte: &Karte,
    _modul: &str,
    _name: &str,
    init_modul: &str,
    init: &Expr,
    ziel_span: Span,
    absagen: &mut Absagen,
) {
    if hat_gleitkomma(init) || hat_bitnicht(init) {
        return;
    }
    let mut besucht = HashSet::new();
    let mut stapel = Vec::new();
    let mut h = Huelle::default();
    let params = HashSet::new();
    huelle_expr(u, karte, init_modul, init, &params, &mut besucht, &mut stapel, &mut h);
    if !h.kreis_durch_konst.is_empty() {
        for sp in h.kreis_durch_konst {
            absagen.schiebe(
                Absage::fehler(
                    "K193",
                    sp,
                    "unbounded recursion in const evaluation: the reference cycle \
                     passes through a `const`, and a `const` carries no `decreases`",
                )
                .mit_notiz("a cycle of functions alone is K008/K009/H022 where it stands"),
            );
        }
        return;
    }
    if !h.unrein.is_empty() {
        for sp in h.unrein {
            absagen.schiebe(
                Absage::fehler(
                    "K192",
                    sp,
                    "a `const` calls a function that is not `pure` -- `pure` means it \
                     touches nothing, not even by reading",
                )
                .mit_notiz("the evaluable fragment calls only `effects { pure }` functions"),
            );
        }
        return;
    }
    if h.kreis_ohne_konst {
        return;
    }
    if u.konst_wert(init_modul, init).is_some() {
        return;
    }
    if !ist_fremd(init) || hat_nullnenner(u, init_modul, init) {
        return;
    }
    absagen.schiebe(k190(ziel_span, _name));
}

/// Hold one const-table initializer against its declared array type.
fn pruefe_tabelle(
    u: &Umgebung,
    karte: &Karte,
    name: &str,
    init_modul: &str,
    elemente: &[Expr],
    element_typ: &crate::typen::Typ,
    laenge: Option<u128>,
    ziel_span: Span,
    absagen: &mut Absagen,
) {
    let mut besucht = HashSet::new();
    let mut stapel = Vec::new();
    let mut h = Huelle::default();
    let params = HashSet::new();
    for e in elemente {
        if hat_gleitkomma(e) || hat_bitnicht(e) {
            continue;
        }
        huelle_expr(u, karte, init_modul, e, &params, &mut besucht, &mut stapel, &mut h);
    }
    if !h.kreis_durch_konst.is_empty() {
        for sp in h.kreis_durch_konst {
            absagen.schiebe(
                Absage::fehler(
                    "K193",
                    sp,
                    "unbounded recursion in const evaluation: the reference cycle \
                     passes through a `const`, and a `const` carries no `decreases`",
                )
                .mit_notiz("a cycle of functions alone is K008/K009/H022 where it stands"),
            );
        }
        return;
    }
    if !h.unrein.is_empty() {
        for sp in h.unrein {
            absagen.schiebe(
                Absage::fehler(
                    "K192",
                    sp,
                    "a const-table element calls a function that is not `pure` -- \
                     `pure` means it touches nothing, not even by reading",
                )
                .mit_notiz("the evaluable fragment calls only `effects { pure }` functions"),
            );
        }
        return;
    }
    if h.kreis_ohne_konst {
        return;
    }
    if let Some(n) = laenge {
        if elemente.len() as u128 != n {
            absagen.schiebe(
                Absage::fehler(
                    "K191",
                    ziel_span,
                    format!(
                        "const-table `{name}` declares [{n}] but the literal holds {} \
                         entries -- the literal is element-wise, nothing is filled in",
                        elemente.len()
                    ),
                )
                .mit_notiz("the length is the declared count, not a separate annotation"),
            );
            return;
        }
    }
    let bereich = element_typ.bereich();
    for e in elemente {
        if hat_gleitkomma(e) || hat_bitnicht(e) {
            continue;
        }
        let Some(w) = u.konst_wert(init_modul, e) else {
            if ist_fremd(e) && !hat_nullnenner(u, init_modul, e) {
                absagen.schiebe(k190(e.span, name));
            }
            continue;
        };
        if let Some(b) = &bereich {
            if w < b.min || w > b.max {
                absagen.schiebe(
                    Absage::fehler(
                        "K194",
                        e.span,
                        format!(
                            "const-table element {w} lies outside the declared element \
                             range `{} .. {}`",
                            b.min, b.max
                        ),
                    )
                    .mit_notiz("each element is held against the element type, not the table"),
                );
            }
        }
    }
}

/// The pass: every `const` in every module, scalars and tables.
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = Umgebung::sammle(baum);
    let karte = Karte::von(baum);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Konst(k) = &item.art else {
            return;
        };
        if let ExprArt::ArrayLit(elemente) = &k.wert.art {
            let t = u.typ_von_ausdruck_decl(modul, &k.typ);
            let (element, laenge) = match t.durchgreifen() {
                crate::typen::Typ::Feld { element, laenge } => {
                    ((**element).clone(), *laenge)
                }
                _ => {
                    absagen.schiebe(k190(k.name.span, &k.name.text));
                    return;
                }
            };
            pruefe_tabelle(
                &u,
                &karte,
                &k.name.text,
                modul,
                elemente,
                &element,
                laenge,
                k.name.span,
                absagen,
            );
            return;
        }
        pruefe_skalar(
            &u,
            &karte,
            modul,
            &k.name.text,
            modul,
            &k.wert,
            k.name.span,
            absagen,
        );
    });
}

/// Print the evaluated values of a const table as a Lean certificate file:
/// a `List Nat` literal plus the defining equation as a `List.all`
/// predicate over `zipIdx` (encoding N of the certificate measurement),
/// closed by `decide`. `gleichung` is the equation body over the pair `p`
/// (`p.1` the value, `p.2` the index), e.g. `p.1 == p.2 * p.2`.
pub fn zertifikat(name: &str, werte: &[u64], gleichung: &str) -> String {
    use std::fmt::Write;
    let mut aus = String::new();
    let _ = writeln!(
        aus,
        "-- Compile-time certificate printed by gabbro-check (lane 111):"
    );
    let _ = writeln!(
        aus,
        "-- the evaluated values of const-table `{name}` and their defining"
    );
    let _ = writeln!(aus, "-- equation as a `List.all` predicate (encoding N).");
    let _ = writeln!(aus, "def {name}Vals : List Nat :=");
    let _ = write!(aus, "  [");
    for (i, w) in werte.iter().enumerate() {
        if i > 0 {
            let _ = write!(aus, ", ");
        }
        let _ = write!(aus, "{w}");
    }
    let _ = writeln!(aus, "]");
    let _ = writeln!(
        aus,
        "def {name}Ok : Bool := ({name}Vals.zipIdx).all (fun p => {gleichung})"
    );
    let _ = writeln!(aus, "theorem {name}_zert : {name}Ok = true := by decide");
    aus
}
