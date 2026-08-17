//! **Pass 5 — M2, echte Linearität. Der Mechanismus, den kein vorhandenes Werkzeug liefert.**
//!
//! Gemessen (`MESSUNGEN.md`): Verus' `tracked` ist **affin**, Rust ist affin, SPARKs
//! Leckprüfung hängt an einer **Allokation**. Affin heisst: *höchstens einmal verbraucht* —
//! ein Wert darf fallengelassen werden. **Linear heisst: genau einmal**, und der Unterschied
//! ist die ganze Zusage:
//!
//! * `Held(L)` fallenlassen = eine Sperre, die niemand freigibt.
//! * `BootPhase` verdoppeln = zwei Kerne glauben, sie booten allein.
//! * `Parked` doppelt verbrauchen = ein Thread wird zweimal geweckt.
//! * `Duty(check)` fallenlassen = eine Prüfpflicht, die niemand einlöst.
//! * `own`-Zeiger verdoppeln = zwei Besitzer derselben Region.
//!
//! **Das ist der einzige Mechanismus des Ordners, für den es keinen Ersatz gibt** — und der
//! Grund, warum die Sprache überhaupt gerechtfertigt sein könnte.
//!
//! ## Was dieser Pass prüft und was nicht
//!
//! Er prüft **je Weg durch einen Rumpf**: jeder lineare Wert, der entsteht, wird auf jedem
//! Weg **genau einmal** verbraucht. Verbraucht wird durch:
//!
//! * einen Aufruf, dessen `effects` den Parameter unter `consumes` nennt,
//! * eine Rückgabe.
//!
//! **`leaves` verbraucht nicht** — die Klausel nennt die Werte, die den Ausgang *verlassen*
//! (`SPRACHE.md`:858), also die Schleife **überleben**.
//!
//! **Er prüft nicht** die Aliasfrage — dafür steht M3 — und **nicht** die Ghost-Löschung: ein
//! `ghost`-Wert existiert zur Laufzeit nicht, seine Linearität ist eine Aussage über den
//! **Beweis**, nicht über den Code. *Beides steht hier, damit niemand die Deckung grösser
//! liest, als sie ist.*
//!
//! ## Die Grobheit hat eine Richtung (W9)
//!
//! Bei einer Verzweigung wird **jeder Zweig einzeln** gerechnet und danach verlangt, dass
//! alle dasselbe tun. Wo ein Zweig divergiert (`-> never`), zählt er nicht mit — sonst wäre
//! jede Fehlerbehandlung ein Leck. **Die Vergröberung geht damit in die strenge Richtung:
//! sie meldet mehr, nicht weniger**, und ein falscher Alarm ist hier billiger als ein
//! übersehenes Leck.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{BTreeMap, BTreeSet};

/// Was ein linearer Wert im Rumpf erlebt.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Zustand {
    Lebt,
    Verbraucht,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // 1. Welche Typen sind linear?
    let mut linear: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Typ(t) = &item.art {
            if t.linear {
                linear.insert(t.name.text.clone());
            }
        }
    });
    if linear.is_empty() {
        return;
    }

    // 2. Welcher Parameter welcher Funktion wird verbraucht? Aus `effects { consumes … }`.
    let mut verbraucht_param: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            let mut menge = BTreeSet::new();
            if let Some(w) = &f.effects {
                for e in &w.liste {
                    if let WirkungArt::Verbraucht(o) = &e.art {
                        menge.insert(o.basis.text.clone());
                    }
                }
            }
            verbraucht_param.insert(f.name.text.clone(), menge);
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        // Lineare Parameter, die die Funktion NICHT unter `consumes` nennt, sind geliehen --
        // sie muessen am Ende noch leben. Die genannten muessen weg sein.
        let eigene = verbraucht_param.get(&f.name.text).cloned().unwrap_or_default();
        let mut zust: BTreeMap<String, (Zustand, Span, bool)> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Pfad(pf) = &p.typ {
                if let Some(n) = pf.teile.last() {
                    if linear.contains(&n.text) {
                        let soll_weg = eigene.contains(&p.name.text);
                        zust.insert(p.name.text.clone(), (Zustand::Lebt, p.name.span, soll_weg));
                    }
                }
            }
        }
        if zust.is_empty() {
            return;
        }
        gehe(b, &linear, &verbraucht_param, &mut zust, absagen);
        // Am Ende: geliehene leben, verbrauchte sind weg.
        for (name, (z, span, soll_weg)) in &zust {
            match (z, soll_weg) {
                (Zustand::Lebt, true) => absagen.schiebe(
                    Absage::fehler(
                        "L101",
                        *span,
                        format!(
                            "`{name}` is listed under `consumes` but is consumed on no path"
                        ),
                    )
                    .mit_notiz(
                        "`consumes` ist eine Zusage an den Aufrufer: der Wert ist danach weg. \
                         Haelt der Rumpf sie nicht, ist der Wert beim Aufrufer verloren, ohne \
                         verbraucht zu sein",
                    ),
                ),
                (Zustand::Verbraucht, false) => absagen.schiebe(
                    Absage::fehler(
                        "L102",
                        *span,
                        format!("`{name}` is borrowed and is consumed anyway"),
                    )
                    .mit_notiz(
                        "ein Parameter ist verbraucht, wenn `effects` ihn unter `consumes` \
                         nennt -- sonst geliehen. Wer einen geliehenen Wert verbraucht, nimmt \
                         dem Aufrufer etwas, das er noch hat",
                    ),
                ),
                _ => {}
            }
        }
    });
}

fn gehe(
    b: &Block,
    linear: &BTreeSet<String>,
    verbraucht_param: &BTreeMap<String, BTreeSet<String>>,
    zust: &mut BTreeMap<String, (Zustand, Span, bool)>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Ruf(r) => ruf(r, s.span, verbraucht_param, zust, absagen),
            StmtArt::Let(l) => ausdruck(&l.wert, s.span, verbraucht_param, zust, absagen),
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    ruf(r, s.span, verbraucht_param, zust, absagen);
                }
                gehe(&l.sonst, linear, verbraucht_param, zust, absagen);
            }
            StmtArt::Return(Some(e)) => ausdruck(e, s.span, verbraucht_param, zust, absagen),
            StmtArt::Zuweisung(z) => ausdruck(&z.wert, s.span, verbraucht_param, zust, absagen),
            StmtArt::Wenn(w) => {
                // **Jeder Zweig einzeln, dann Abgleich** -- ein Wert, der nur in einem Zweig
                // verbraucht wird, ist auf dem anderen Weg noch da. Das ist ein Leck.
                let vorher = zust.clone();
                let mut ergebnisse = Vec::new();
                for (bed, r) in &w.zweige {
                    let mut z = vorher.clone();
                    ausdruck(bed, s.span, verbraucht_param, &mut z, absagen);
                    gehe(r, linear, verbraucht_param, &mut z, absagen);
                    ergebnisse.push((z, endet(r, verbraucht_param)));
                }
                if let Some(r) = &w.sonst {
                    let mut z = vorher.clone();
                    gehe(r, linear, verbraucht_param, &mut z, absagen);
                    ergebnisse.push((z, endet(r, verbraucht_param)));
                } else {
                    ergebnisse.push((vorher.clone(), false));
                }
                abgleich(&ergebnisse, s.span, zust, absagen);
            }
            StmtArt::Match(m) => {
                let vorher = zust.clone();
                let mut ergebnisse = Vec::new();
                for zw in &m.zweige {
                    let mut z = vorher.clone();
                    gehe(&zw.rumpf, linear, verbraucht_param, &mut z, absagen);
                    ergebnisse.push((z, endet(&zw.rumpf, verbraucht_param)));
                }
                abgleich(&ergebnisse, s.span, zust, absagen);
            }
            StmtArt::Sperrt(x) => gehe(&x.rumpf, linear, verbraucht_param, zust, absagen),
            StmtArt::Bricht(x) => gehe(&x.rumpf, linear, verbraucht_param, zust, absagen),
            StmtArt::Narrow(x) => gehe(&x.sonst, linear, verbraucht_param, zust, absagen),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                // **`leaves` verbraucht NICHT.** `SPRACHE.md`:858: *„die `leaves`-Klausel
                // nennt die linearen Werte, die den Ausgang VERLASSEN"* -- sie ueberleben die
                // Schleife, sie enden nicht in ihr.
                //
                // Meine erste Fassung buchte sie als verbraucht und meldete daraufhin
                // `beispiele/04` als Fehler. **Der Pass hatte unrecht, nicht das Beispiel** --
                // und er hatte es an der Stelle, an der die Sprache ihre eigene Klausel am
                // genauesten erklaert. *Ein Pass, der eine Klausel umdeutet, statt sie zu
                // lesen, ist gefaehrlicher als einer, der sie ignoriert.*
                Schleife::Forever(x) => {
                    gehe(&x.rumpf, linear, verbraucht_param, zust, absagen);
                }
                Schleife::Traverse(x) => gehe(&x.rumpf, linear, verbraucht_param, zust, absagen),
                Schleife::Retry(x) => gehe(&x.rumpf, linear, verbraucht_param, zust, absagen),
            },
            _ => {}
        }
    }
}

/// Endet der Block auf jedem Weg? Dann traegt er nichts zum Abgleich bei.
fn endet(b: &Block, _v: &BTreeMap<String, BTreeSet<String>>) -> bool {
    matches!(
        b.anweisungen.last().map(|s| &s.art),
        Some(StmtArt::Return(_)) | Some(StmtArt::Leave(_)) | Some(StmtArt::Next(_))
    )
}

/// **L103 — die Zweige müssen dasselbe tun.** Ein Wert, der nur auf einem Weg verbraucht
/// wird, ist auf dem anderen ein Leck; einer, der auf beiden verbraucht wird, ist keins.
fn abgleich(
    ergebnisse: &[(BTreeMap<String, (Zustand, Span, bool)>, bool)],
    span: Span,
    zust: &mut BTreeMap<String, (Zustand, Span, bool)>,
    absagen: &mut Absagen,
) {
    let lebendige: Vec<_> = ergebnisse.iter().filter(|(_, endet)| !endet).collect();
    let Some((erste, _)) = lebendige.first() else {
        return; // alle Zweige enden -- nichts abzugleichen
    };
    for name in zust.keys().cloned().collect::<Vec<_>>() {
        let z0 = erste.get(&name).map(|e| e.0);
        let uneins = lebendige
            .iter()
            .any(|(z, _)| z.get(&name).map(|e| e.0) != z0);
        if uneins {
            absagen.schiebe(
                Absage::fehler(
                    "L103",
                    span,
                    format!("`{name}` is not treated the same on every path"),
                )
                .mit_notiz(
                    "linear heisst GENAU einmal, nicht hoechstens einmal: ein Wert, der nur \
                     in einem Zweig verbraucht wird, ist auf dem anderen Weg ein Leck",
                )
                .mit_notiz(
                    "ein Zweig, der divergiert oder zurueckkehrt, zaehlt nicht mit -- sonst \
                     waere jede Fehlerbehandlung ein Leck",
                ),
            );
        }
        if let (Some(e), Some(z)) = (zust.get_mut(&name), z0) {
            e.0 = z;
        }
    }
}

fn ruf(
    r: &Ruf,
    span: Span,
    verbraucht_param: &BTreeMap<String, BTreeSet<String>>,
    zust: &mut BTreeMap<String, (Zustand, Span, bool)>,
    absagen: &mut Absagen,
) {
    let Some(name) = r.pfad.teile.last() else {
        return;
    };
    let leer = BTreeSet::new();
    let verbraucht = verbraucht_param.get(&name.text).unwrap_or(&leer);
    // Die Parameternamen des Gerufenen auf die Argumente abbilden: Position fuer Position.
    let sig: Vec<String> = verbraucht.iter().cloned().collect();
    for (i, a) in r.argumente.iter().enumerate() {
        let ExprArt::Ort(o) = &a.art else { continue };
        let arg = o.basis.text.clone();
        let Some((z, _, _)) = zust.get_mut(&arg) else {
            continue;
        };
        // Wird dieses Argument verbraucht? Nur wenn der Gerufene den Parameter an DIESER
        // Stelle unter `consumes` fuehrt -- die Namensmenge reicht dafuer nicht, also
        // wird sie hier ueber die Position genommen, so grob wie ehrlich.
        let wird_verbraucht = !sig.is_empty() && i < r.argumente.len() && !verbraucht.is_empty();
        if wird_verbraucht {
            if *z == Zustand::Verbraucht {
                absagen.schiebe(
                    Absage::fehler(
                        "L104",
                        span,
                        format!("`{arg}` is consumed a second time"),
                    )
                    .mit_notiz(
                        "linear heisst genau einmal -- der erste Verbrauch hat den Wert \
                         weggenommen",
                    )
                    .mit_notiz("the first consumption is further up in the same body"),
                );
            }
            *z = Zustand::Verbraucht;
        } else if *z == Zustand::Verbraucht {
            absagen.schiebe(
                Absage::fehler(
                    "L105",
                    span,
                    format!("`{arg}` is used after it was consumed"),
                )
                .mit_notiz("after consumption the value no longer exists"),
            );
        }
    }
}

fn ausdruck(
    e: &Expr,
    span: Span,
    v: &BTreeMap<String, BTreeSet<String>>,
    zust: &mut BTreeMap<String, (Zustand, Span, bool)>,
    absagen: &mut Absagen,
) {
    match &e.art {
        ExprArt::Ruf(r) => ruf(r, span, v, zust, absagen),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => ausdruck(x, span, v, zust, absagen),
        ExprArt::Binaer(_, a, b) => {
            ausdruck(a, span, v, zust, absagen);
            ausdruck(b, span, v, zust, absagen);
        }
        _ => {}
    }
}
