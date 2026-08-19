//! **Pass 7 — die Paarung. Zwei hängende Klassen warten auf ihn.**
//!
//! Die Neuerhebung der Klempnerei-Klassen (`MESSUNGEN.md`, `N_neu = 5`) buchte **Rennen**
//! (2 276 Atomzugriffe) und **Publikation** (824 Stores an Geteiltes) als hängend — mit
//! demselben Grund: *der Paarungspass ist nicht gebaut.* Zwei Klassen, eine Lücke.
//!
//! ## Was gepaart wird
//!
//! `SPRACHE.md` Teil II §1: **Ordering wird gepaart, nicht deklariert.** Ein `release`-Store
//! nennt seine Nutzlast (`publishes { … }`), ein `acquire`-Load nennt, was er erwartet
//! (`awaits { … }`). Die Frage, die kein Mensch von Hand beantwortet:
//!
//! > **Gibt es zu jeder erwarteten Nutzlast eine, die sie veröffentlicht — und umgekehrt?**
//!
//! Eine verwaiste Hälfte ist der Fehler, den man nicht sieht: ein `awaits`, dem niemand
//! liefert, liest gültigen Müll; ein `publishes`, das niemand erwartet, ist eine Barriere
//! ohne Grund — teuer und irreführend.
//!
//! ## Die Namensgleichheit geht über die Indexsubstitution
//!
//! `c.slots[s].daten` und `c.slots[i].daten` sind **dieselbe** Nutzlast — der Index ist die
//! Laufvariable der jeweiligen Seite. Verglichen wird deshalb die Form mit `[…]` statt des
//! Indexausdrucks. *Das ist grob, und die Richtung stimmt* (W9): es paart **mehr** als
//! streng gleich, also meldet es **weniger** verwaiste Hälften — die Absage bleibt damit auf
//! der sicheren Seite, denn sie ist eine Behauptung über eine Lücke.
//!
//! ## Der dritte Zustand gilt auch hier (W10)
//!
//! Die Paarung läuft über die **transitive** Menge: eine Zwischenfunktion, die selbst weder
//! publiziert noch erwartet, darf die zwei Hälften nicht trennen. Wo der Aufrufgraph
//! unvollständig ist (Zyklus, unbekannter Gerufener), ist die Menge eine **untere Schranke** —
//! und aus einer Untergrenze wird **weder abgesagt noch bestätigt**.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeSet;

/// Eine Nutzlast, auf ihre **Form** gebracht: `c.slots[s].d` und `c.slots[i].d` werden gleich.
fn form(o: &str) -> String {
    let mut aus = String::new();
    let mut in_klammer = false;
    for z in o.chars() {
        match z {
            '[' => {
                in_klammer = true;
                aus.push_str("[…]");
            }
            ']' => in_klammer = false,
            _ if in_klammer => {}
            _ => aus.push(z),
        }
    }
    aus
}

#[derive(Default)]
struct Haelften {
    /// Was veröffentlicht wird — Form, Fundstelle.
    publiziert: Vec<(String, Span)>,
    /// Was erwartet wird.
    erwartet: Vec<(String, Span)>,
    /// Ein `relaxed`-Store mit Nutzlast: die Ordnung trägt sie nicht. Das `bool` sagt, ob
    /// `relaxed` **dastand** -- die schweigende Fassung ist die gefährlichere.
    relaxed_mit_last: Vec<(String, Span, bool)>,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let mut ordnungen: Vec<(String, Option<Ordnung>)> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Atomic(a) = &item.art {
            ordnungen.push((a.name.text.clone(), a.ordnung));
        }
    });

    // **Erst die eigenen Hälften je Funktion, dann die transitive Vereinigung.**
    let mut je_funktion: Vec<(String, Haelften, bool)> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut h = Haelften::default();
        sammle(b, &ordnungen, &mut h);
        let unvollstaendig = g
            .huelle(&g.schluessel_von(modul, &f.name.text))
            .unvollstaendig
            .is_some();
        je_funktion.push((f.name.text.clone(), h, unvollstaendig));
    });

    // Die vereinigte Menge über den ganzen Baum -- die Paarung ist eine Aussage über das
    // PROGRAMM, nicht über eine Funktion: wer publiziert und wer erwartet, sind fast nie
    // dieselbe Funktion.
    let alle_publiziert: BTreeSet<String> = je_funktion
        .iter()
        .flat_map(|(_, h, _)| h.publiziert.iter().map(|(o, _)| o.clone()))
        .collect();
    let alle_erwartet: BTreeSet<String> = je_funktion
        .iter()
        .flat_map(|(_, h, _)| h.erwartet.iter().map(|(o, _)| o.clone()))
        .collect();

    for (name, h, unvollstaendig) in &je_funktion {
        // **W10:** aus einer unteren Schranke wird weder abgesagt noch bestätigt.
        if *unvollstaendig && !h.publiziert.is_empty() {
            absagen.schiebe(
                Absage::hinweis(
                    "V003",
                    h.publiziert[0].1,
                    format!("the pairing in `{name}` is undecidable: the call graph is incomplete here"),
                )
                .mit_notiz(
                    "the payload sets are only a LOWER bound -- no completeness follows \
                        from them",
                ),
            );
            continue;
        }
        for (o, span) in &h.publiziert {
            if !alle_erwartet.contains(o) {
                absagen.schiebe(
                    Absage::fehler(
                        "V001",
                        *span,
                        format!("`publishes {o}` in `{name}` -- nothing awaits this payload"),
                    )
                    .mit_notiz(
                        "SPRACHE.md part II §1: ordering is PAIRED, not declared -- a \
                            publication without a counterpart orders nothing",
                    )
                    .mit_notiz("`publishes nothing` says expressly that there is none"),
                );
            }
        }
        for (o, span) in &h.erwartet {
            if !alle_publiziert.contains(o) {
                absagen.schiebe(
                    Absage::fehler(
                        "V002",
                        *span,
                        format!("`awaits {o}` in `{name}` -- nothing publishes this payload"),
                    )
                    .mit_notiz(
                        "the dangerous half: an `awaits` without a counterpart reads a \
                            value whose visibility nobody establishes",
                    ),
                );
            }
        }
        for (o, span, erklaert) in &h.relaxed_mit_last {
            let absage = if *erklaert {
                Absage::fehler(
                    "V004",
                    *span,
                    format!("`{o}` is `relaxed` and carries a payload anyway"),
                )
            } else {
                Absage::fehler(
                    "V005",
                    *span,
                    format!("`{o}` declares no ordering and carries a payload anyway"),
                )
                .mit_notiz(
                    "an `atomic` without an ordering word becomes \
                        `memory_order_relaxed` in C -- on BOTH sides",
                )
                .mit_notiz(
                    "`release` at the declaration is what makes the payload visible; \
                        without it the pairing promises what the machine does not do",
                )
            };
            absagen.schiebe(absage.mit_notiz(
                "`relaxed` orders nothing -- a payload on it is a promise without a \
                    mechanism",
            ));
        }
    }
}

fn sammle(b: &Block, ordnungen: &[(String, Option<Ordnung>)], h: &mut Haelften) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Publish(p) => {
                let ziel = p.ziel.text();
                // **Ein fehlendes Ordnungswort IST `relaxed`** -- und zwar im Erzeugnis,
                // nicht nur im Modell. Gemessen am 2026-08-19: `atomic FERTIG : bool;` mit
                // `publishes`/`awaits` ging mit **0 Fehlern** durch, und im C standen auf
                // BEIDEN Seiten `memory_order_relaxed`. *Die Publikation, die die Klasse
                // trägt, verdampfte ohne eine einzige Meldung.*
                //
                // `matches!(o, Some(Ordnung::Relaxed))` prüfte das geschriebene Wort und
                // liess das ungeschriebene durch -- die Vorgabe ist dieselbe Ordnung und war
                // die einzige, über die niemand sprach.
                let stille = ordnungen.iter().find_map(|(n, o)| {
                    (ziel.split(['.', '[']).next() == Some(n.as_str())
                        && matches!(o, Some(Ordnung::Relaxed) | None))
                    .then_some(o.is_some())
                });
                if let Nutzlast::Orte(liste) = &p.nutzlast {
                    for o in liste {
                        match stille {
                            Some(erklaert) => {
                                h.relaxed_mit_last.push((ziel.clone(), s.span, erklaert))
                            }
                            None => h.publiziert.push((form(&o.text()), s.span)),
                        }
                    }
                }
            }
            StmtArt::AwaitLoad(a) => {
                for o in &a.erwartet {
                    h.erwartet.push((form(&o.text()), s.span));
                }
            }
            StmtArt::Exchange(e) => {
                if let Some(Nutzlast::Orte(liste)) = &e.nutzlast {
                    for o in liste {
                        h.publiziert.push((form(&o.text()), s.span));
                    }
                }
                for o in e.erwartet.iter().flatten() {
                    h.erwartet.push((form(&o.text()), s.span));
                }
            }
            _ => {}
        }
        // **Der Abstieg geht über `crate::unterbloecke`** — erschöpfend über `StmtArt`.
        // Vorher fehlte `observes`: eine Paarungshälfte in einem RCU-Leseblock war für
        // diesen Pass nicht da, und die Gegenseite galt als unbeantwortet.
        for k in crate::unterbloecke(s) {
            sammle(k, ordnungen, h);
        }
    }
}
