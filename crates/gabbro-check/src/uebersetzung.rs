//! Lane E5 -- the translation stage, first cut (PLAN-ERWEITUNG.md section 6).
//!
//! A checked library call `@lib#f ( args ) { region }` is a run-time call
//! whose region the reader captures as raw tokens (lane E1). The library's
//! declared translator turns the region into a payload at translation time
//! (PLAN-ERWEITUNG.md section 0b); the translator is not trusted -- a wrong
//! translator produces a payload this stage refuses -- and the emitter
//! passes an accepted payload as a `static const` table argument.
//!
//! ## The first-cut region value
//!
//! The region's raw tokens become a value of the payload table when every
//! token parses as an integer literal: token `i` fills row `i` of the
//! table's single integer field. Anything else -- a word like `dispatch`,
//! a hex literal, a brace -- is outside this cut, and the call keeps the
//! translation refusal (`N069`): the region is captured, not interpreted,
//! exactly as before. A token table the translator walks in Gabbro code
//! (PLAN-ERWEITUNG.md section 2) needs translation-time value
//! construction -- building a fresh table value without a run-time effect
//! -- which the checker has no syntax for (`M140` is nominal, a carrier
//! read under `pure` is `E010`); until that syntax exists the walk lives
//! here, in Rust, bounded by the payload count.
//!
//! ## The runnable translator fragment
//!
//! Only the identity shape runs: `return <region>;`, the region parameter
//! already standing in payload form. Every other body is refused by name
//! (`N231`); a translator between two different tables has no checkable
//! body today (SYNTAX.md section 7.2 books the same gap), so refusing it
//! loudly is the honest answer, not a silent acceptance.
//!
//! ## Where the payload goes
//!
//! The region fills the library function's LAST parameter, which must be
//! a pointer at the payload table (`N233` where it is not, or where the
//! call passes it explicitly -- that would bypass the translation). The
//! ordinary arguments are checked against the remaining parameters like
//! any call's (`m1` trims the filled slot through `fuell_index`); the
//! contract must not name the filled parameter (`N234`), because no source
//! value could ever discharge it. Arity against the payload count is
//! `N230`, the field range is `N232` -- both reported through the region
//! span map (lane E7), at the offending token, never at the call.
//!
//! ## What this stage does NOT do (booked, not forgotten)
//!
//! * Non-integer regions stay `N069`: the region is unreadable to this
//!   cut, and the refusal that says so already exists.
//! * A payload table with anything but one integer field and a constant
//!   count is `N233`: tree payloads and multi-field tables are the
//!   declared direction, not this cut.
//! * The Lean program-logic channel (`lean.rs`) still maps every library
//!   call to `CallStatement`: the certificate below checks the payload's
//!   TYPING, not the call's Hoare triple.
//! * The certificate is printed, never shipped: like lanes 111/121 the
//!   printer below is pinned by tests against the Lean mirror
//!   (`grammatik/Grammatik/Uebersetzung.lean`), and no production path
//!   writes it anywhere.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Absage;
use gabbro_syntax::span::Span;
use std::collections::HashSet;

use crate::regionkarte::RegionKarte;
use crate::umgebung::{Umgebung, kurzname, qualifiziere};

/// A translator declaration as the translation stage reads it: the lane-E3
/// linkage and signature (effects, `decreases`, result) plus the two things
/// only the running stage needs -- the region parameter's name and the
/// body. Collected once here (`diener_sammeln`) and read by the name pass
/// and the emitter alike, so the two can never disagree on who serves a
/// library function.
#[derive(Clone)]
pub struct Diener {
    pub qual: String,
    pub modul: String,
    pub ziel: String,
    pub span: Span,
    pub effects: Option<Wirkungen>,
    pub decreases: Option<Expr>,
    pub ergebnis: Option<TypExpr>,
    /// The region parameter's name: exactly one by grammar shape
    /// (`translatordecl` reads one `ident : typeexpr`), so the empty
    /// string where none stands -- and then no body can return it.
    pub param: String,
    pub rumpf: FnRumpf,
}

/// Collect every translator declaration of the unit, in tree order: the
/// first declaration by position serves its function (lane E3,
/// `N200`/`N201`), and both readers take the same first.
pub fn diener_sammeln(baum: &Programm) -> Vec<Diener> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |i, modul| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let Some(fuer) = &f.translator_fuer else { return };
        aus.push(Diener {
            qual: qualifiziere(modul, &f.name.text),
            modul: modul.to_string(),
            ziel: fuer.text.clone(),
            span: f.span,
            effects: f.effects.clone(),
            decreases: f.decreases.clone(),
            ergebnis: f.ergebnis.clone(),
            param: f
                .parameter
                .first()
                .map(|p| p.name.text.clone())
                .unwrap_or_default(),
            rumpf: f.rumpf.clone(),
        });
    });
    aus
}

/// The payload of one accepted call: the qualified payload table, its
/// single field, and the region values row by row.
#[derive(Debug, Clone)]
pub struct Nutzlast {
    pub tabelle: String,
    pub feld: String,
    pub werte: Vec<i128>,
}

/// The verdict over one resolved library call. `NichtZustaendig` leaves
/// the call to the older rules (`N069` where the region is no integer
/// row, `M143` where the ordinary arity is off); `Still` names a
/// declaration defect an earlier call already reported, so it is not
/// reported twice.
pub enum Ausgang {
    NichtZustaendig,
    Angenommen(Nutzlast),
    Abgelehnt(Absage),
    Still,
}

/// The region as integers, row by row -- `None` where any token is no
/// integer literal. First cut reads `i128`-sized decimal literals; a word
/// like `dispatch` is not one, and neither is a literal past `i128`.
pub fn region_werte(r: &LibraryCall) -> Option<Vec<i128>> {
    r.region
        .iter()
        .map(|t| t.text.parse::<i128>().ok())
        .collect()
}

/// The payload table behind a library function: the `payload` clause
/// resolved from the declaring module to a declared table. `None` where
/// the clause names no table (`N060` beside it owns that defect).
fn nutzlast_tabelle(u: &Umgebung, modul: &str, qual: &str) -> Option<(String, String, Span)> {
    let (_, nutzlast, span) = u.nutzlasten.get(qual)?.clone();
    let tabelle = u
        .kandidaten_aufloesbar(modul, &nutzlast)
        .into_iter()
        .find(|k| u.tabellen.contains_key(k))?;
    Some((tabelle, nutzlast, span))
}

/// The single integer field of a payload table with its range and the
/// table's constant count -- the first-cut payload shape. `qual` is the
/// qualified table name, resolved from the declaring module outward, and
/// the name says so: the resolution guard (`pruefe-aufloesung.py`, Fach 2)
/// reads the key, not the proof, so a computed key carries a computed
/// name. `None` where the table carries anything else.
fn nutzlast_gestalt(u: &Umgebung, tabelle: &str) -> Option<(String, crate::typen::IntBereich, u128)> {
    let qual = tabelle;
    let felder = u.tabellen.get(qual)?;
    let [(name, typ)] = felder.as_slice() else {
        return None;
    };
    let bereich = typ.bereich()?;
    if !matches!(
        typ.durchgreifen(),
        crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
    ) {
        return None;
    }
    let anzahl = *u.kapazitaeten.get(qual)?;
    Some((name.clone(), bereich, anzahl))
}

/// The payload parameter the region fills: the library function's last
/// parameter, a pointer at the payload table. The name and the qualified
/// table, or `None` where the declaration names none.
fn nutzlast_param(u: &Umgebung, qual: &str, tabelle: &str) -> Option<String> {
    let sig = u.funktionen.get(qual)?;
    let (name, typ) = sig.parameter.last()?;
    let crate::typen::Typ::Zeiger(ziel) = typ else {
        return None;
    };
    let crate::typen::Typ::Tabelle(t) = ziel.durchgreifen() else {
        return None;
    };
    if t != tabelle {
        return None;
    }
    Some(name.clone())
}

/// The filled slot for `m1`: `Some(n - 1)` where the region fills the
/// library function's last parameter -- a payload pointer, one ordinary
/// argument short, an integer region to fill it with -- or where the call
/// passes that parameter explicitly beside an integer region (the bypass
/// the stage refuses as `N233`, held against the shortened signature so
/// the bypassed slot draws no second diagnostic). `None` everywhere else,
/// and then the call is checked against its full signature.
pub fn fuell_index(u: &Umgebung, modul: &str, r: &LibraryCall) -> Option<usize> {
    let z = u.bibliothek(modul, &r.library.text, &r.function.text)?;
    let (tabelle, _, _) = nutzlast_tabelle(u, &z.modul, &z.name)?;
    nutzlast_param(u, &z.name, &tabelle)?;
    let qual = &z.name;
    let sig = u.funktionen.get(qual)?;
    if sig.parameter.is_empty() {
        return None;
    }
    if r.args.len() + 1 != sig.parameter.len() && r.args.len() != sig.parameter.len() {
        return None;
    }
    region_werte(r)?;
    Some(sig.parameter.len() - 1)
}

/// Whether a contract predicate reads the payload parameter: no source
/// value could ever discharge it, so the first cut refuses it (`N234`)
/// instead of checking around it.
fn vertrag_nennt_param(sig: &crate::umgebung::Signatur, param: &str) -> Option<Span> {
    for p in sig.requires.iter().chain(sig.ensures.iter()) {
        for e in crate::ausdruecke_im_praedikat(p) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ort(o) = &x.art {
                    if o.basis.text == param {
                        return Some(p.span);
                    }
                }
            }
        }
    }
    None
}

/// Whether a translator body is the runnable shape: `return <param>;`,
/// parentheses aside. A table value has no pure constructor (`M140` is
/// nominal), so only the identity can ever run.
fn ist_identitaet(rumpf: &FnRumpf, param: &str) -> bool {
    let FnRumpf::Block(b) = rumpf else {
        return false;
    };
    let [s] = b.anweisungen.as_slice() else {
        return false;
    };
    let StmtArt::Return(Some(w)) = &s.art else {
        return false;
    };
    match &crate::ohne_klammern(w).art {
        ExprArt::Ort(o) => o.suffixe.is_empty() && o.basis.text == param,
        _ => false,
    }
}

/// Run the verdict over one resolved library call: parse the region,
/// hold the translator's shape, hold the arity against the payload
/// count, hold every value against the field range. All premises are
/// read, none is discarded: the payload table, its shape, the filled
/// parameter, the contract, the translator and the region each refuse
/// in their own code.
pub fn versuch(
    r: &LibraryCall,
    modul: &str,
    u: &Umgebung,
    diener: Option<&Diener>,
    done: &mut HashSet<(String, String)>,
) -> Ausgang {
    let Some(z) = u.bibliothek(modul, &r.library.text, &r.function.text) else {
        return Ausgang::NichtZustaendig;
    };
    let Some(werte) = region_werte(r) else {
        return Ausgang::NichtZustaendig;
    };
    let karte = RegionKarte::vom_ruf(r);
    // The declaration defects below fire once per library function: a
    // second call with an integer region names the same translator, not
    // a second defect.
    let mut einmal = |code: &str, qual: &str, absage: Absage| -> Ausgang {
        if done.insert((code.to_string(), qual.to_string())) {
            Ausgang::Abgelehnt(absage)
        } else {
            Ausgang::Still
        }
    };
    let Some((tabelle, _, nutzlast_span)) = nutzlast_tabelle(u, &z.modul, &z.name) else {
        return Ausgang::NichtZustaendig;
    };
    let Some((feld, bereich, anzahl)) = nutzlast_gestalt(u, &tabelle) else {
        let absage = Absage::fehler(
            "N233",
            nutzlast_span,
            format!(
                "`payload` of `library fn {}` is not a single-integer-field table with a \
                 constant count -- the first cut fills one integer field row by row",
                z.name
            ),
        )
        .mit_notiz(
            "tree payloads and multi-field tables are the declared direction \
             (PLAN-ERWEITUNG.md section 2), not this cut: the region fills one \
             field, and anything else has no row to fill",
        );
        return einmal("N233", &z.name, absage);
    };
    let qual = &z.name;
    let Some(sig) = u.funktionen.get(qual).cloned() else {
        return Ausgang::NichtZustaendig;
    };
    let Some(param) = nutzlast_param(u, &z.name, &tabelle) else {
        let absage = Absage::fehler(
            "N233",
            sig.span,
            format!(
                "`library fn {}` carries no payload parameter -- the region fills the \
                 last parameter, a pointer at the payload table, and here it names none",
                z.name
            ),
        )
        .mit_notiz(
            "the payload reaches the function as a `static const` table argument \
             (PLAN-ERWEITUNG.md section 0b); without a parameter to carry it the \
             translation has nowhere to go, and dropping it would be fail-open",
        );
        return einmal("N233", &z.name, absage);
    };
    if r.args.len() == sig.parameter.len() {
        let span = r.args.last().map(|a| a.span).unwrap_or(r.span);
        let absage = Absage::fehler(
            "N233",
            span,
            format!(
                "`@{}` passes the payload parameter `{param}` itself -- the region fills \
                 it at translation time, so an explicit argument bypasses the translation",
                format!("{}#{}", r.library.text, r.function.text),
            ),
        )
        .mit_notiz(
            "a direct value for the payload would silently win over the region -- \
             the call passes one argument short, and the region fills the rest",
        );
        return einmal("N233", &z.name, absage);
    }
    if r.args.len() + 1 != sig.parameter.len() {
        return Ausgang::NichtZustaendig;
    }
    if let Some(span) = vertrag_nennt_param(&sig, &param) {
        let absage = Absage::fehler(
            "N234",
            span,
            format!(
                "the contract of `library fn {}` names the payload parameter `{param}` -- \
                 the first cut cannot evaluate it at translation time",
                z.name
            ),
        )
        .mit_notiz(
            "no source value ever stands for the payload at the call, so a precondition \
             over it is uncheckable and a postcondition over it unprovable -- keep the \
             contract over the ordinary parameters and the result",
        );
        return einmal("N234", &z.name, absage);
    }
    let Some(d) = diener else {
        return Ausgang::NichtZustaendig;
    };
    if !ist_identitaet(&d.rumpf, &d.param) {
        let pname = d.param.clone();
        let absage = Absage::fehler(
            "N231",
            d.span,
            format!(
                "`translator {}` does not return its region parameter -- the first cut \
                 runs only `return {pname};` and refuses every other body by name",
                d.qual
            ),
        )
        .mit_notiz(
            "a table value has no pure constructor (`M140` is nominal, a carrier read \
             under `pure` is `E010`): only the identity shape, the region already \
             standing in payload form, can ever run",
        );
        return einmal("N231", &z.name, absage);
    }
    if werte.len() as u128 != anzahl {
        let span = if (werte.len() as u128) > anzahl {
            karte.fuer(anzahl as usize).unwrap_or(r.span)
        } else {
            karte.ruf_span(r)
        };
        let absage = Absage::fehler(
            "N230",
            span,
            format!(
                "`@{}` passes {} integer(s) for a payload of {anzahl} -- the region fills \
                 the payload row by row, so a short or long region leaves rows unfilled \
                 or homeless",
                format!("{}#{}", r.library.text, r.function.text),
                werte.len(),
            ),
        )
        .mit_notiz(
            "the first cut reads exact-length integer regions: one token per row, no \
             padding, no truncation -- the span above is the first homeless token, or \
             the region itself where rows stay empty",
        );
        return Ausgang::Abgelehnt(absage);
    }
    for (i, v) in werte.iter().enumerate() {
        if *v < bereich.min || *v > bereich.max {
            let absage = Absage::fehler(
                "N232",
                karte.fuer(i).unwrap_or(r.span),
                format!(
                    "payload entry {v} lies outside the field range `{} .. {}`",
                    bereich.min, bereich.max
                ),
            )
            .mit_notiz(
                "the payload is checked against the payload type (PLAN-ERWEITUNG.md \
                 section 0b): a well-typed value of that table type, every entry in \
                 its field range -- the span above is the offending region token, \
                 carried back through the region span map (lane E7)",
            );
            return Ausgang::Abgelehnt(absage);
        }
    }
    Ausgang::Angenommen(Nutzlast {
        tabelle,
        feld,
        werte,
    })
}

/// One accepted call site for the emitter: where the call stands, which C
/// names it needs, and the payload values. Collected over the tree in
/// order, so two runs over one tree emit the same C byte for byte.
pub struct Einsatz {
    pub von: u32,
    pub bis: u32,
    pub funktion: String,
    pub tabelle: String,
    pub feld: String,
    pub werte: Vec<i128>,
}

/// Every accepted call of the unit: the full verdict per call site, run
/// over the parsed tree. The emitter trusts the checker (W6) and
/// re-derives nothing beyond this list; a call the checker refused is
/// not in it, and the lowering arms keep their refusal for it.
pub fn einsaetze(baum: &Programm) -> Vec<Einsatz> {
    let u = Umgebung::sammle(baum);
    let diener = diener_sammeln(baum);
    let mut done = HashSet::new();
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        Einsatz::im_block(b, modul, &u, &diener, &mut done, &mut aus);
    });
    aus
}

impl Einsatz {
    fn im_block(
        b: &Block,
        modul: &str,
        u: &Umgebung,
        diener: &[Diener],
        done: &mut HashSet<(String, String)>,
        aus: &mut Vec<Einsatz>,
    ) {
        for s in &b.anweisungen {
            if let StmtArt::LibraryCall(r) = &s.art {
                Einsatz::am_ruf(r, modul, u, diener, done, aus);
            }
            for e in crate::eigene_ausdruecke(s) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::LibraryCall(r) = &x.art {
                        Einsatz::am_ruf(r, modul, u, diener, done, aus);
                    }
                }
            }
            for k in crate::unterbloecke(s) {
                Einsatz::im_block(k, modul, u, diener, done, aus);
            }
        }
    }

    fn am_ruf(
        r: &LibraryCall,
        modul: &str,
        u: &Umgebung,
        diener: &[Diener],
        done: &mut HashSet<(String, String)>,
        aus: &mut Vec<Einsatz>,
    ) {
        let ziel = u.bibliothek(modul, &r.library.text, &r.function.text);
        let d = ziel.as_ref().and_then(|z| {
            diener
                .iter()
                .find(|t| t.modul == z.modul && t.ziel == kurzname(&z.name))
        });
        if let Ausgang::Angenommen(n) = versuch(r, modul, u, d, done) {
            aus.push(Einsatz {
                von: r.span.von,
                bis: r.span.bis,
                funktion: r.function.text.clone(),
                tabelle: kurzname(&n.tabelle)
                    .rsplit("::")
                    .next()
                    .unwrap_or(&n.tabelle)
                    .to_string(),
                feld: n.feld,
                werte: n.werte,
            });
        }
    }
}

/// Print the payload of one accepted call as a Lean certificate: the
/// values as a `List Nat` literal applied to the `nutzlastZert` predicate
/// of `grammatik/Grammatik/Uebersetzung.lean` (encoding N of the
/// certificate measurement), closed by `decide` -- so Lean checks the
/// payload's TYPING, every entry in its field range, without ever seeing
/// the translator. The three definition lines stand verbatim in that
/// file; `tests/uebersetzung.rs` holds the two against each other, and a
/// drift breaks the test.
pub fn payload_certificate(name: &str, values: &[i128], lo: i128, hi: i128) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "-- Payload certificate printed by gabbro-check (lane 129):"
    );
    let _ = writeln!(
        out,
        "-- the payload values of `{name}` for `Uebersetzung.nutzlastZert`."
    );
    let werte: Vec<String> = values.iter().map(|v| format!("{v}")).collect();
    let _ = writeln!(out, "def {name}Vals : List Nat := [{}]", werte.join(", "));
    let _ = writeln!(
        out,
        "def {name}Ok : Bool := nutzlastZert {name}Vals {lo} {hi}"
    );
    let _ = writeln!(out, "theorem {name}_zert : {name}Ok = true := by decide");
    out
}
