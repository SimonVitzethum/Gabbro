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
    publiziert: Vec<(String, String, Span)>,
    /// Was erwartet wird — ebenfalls `(Atomic, Nutzlast)`.
    erwartet: Vec<(String, String, Span)>,
    /// Ein `relaxed`-Store mit Nutzlast: die Ordnung trägt sie nicht. Das `bool` sagt, ob
    /// `relaxed` **dastand** -- die schweigende Fassung ist die gefährlichere.
    relaxed_mit_last: Vec<(String, Span, bool)>,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let mut ordnungen: Vec<(String, Option<Ordnung>)> = Vec::new();
    // **Die erklärte Obermenge der Nutzlast** (`SPRACHE.md` §11.3) — bis 2026-08-19 eine
    // Zeile ohne Leser. Sie stand als ZUSAGE in `pruefe-klauseln.py`: *„eine
    // Enthaltensaussage, die niemand nachrechnet."*
    let mut obermengen: Vec<(String, Vec<String>)> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Atomic(a) = &item.art {
            ordnungen.push((a.name.text.clone(), a.ordnung));
            if let Some(Nutzlast::Orte(liste)) = &a.obermenge {
                obermengen.push((
                    a.name.text.clone(),
                    liste.iter().map(|o| form(&o.text())).collect(),
                ));
            }
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
        // «K5.1» -- die Reihenfolge INNERHALB des Rumpfes.
        reihenfolge(b, &[], &[], &[], &f.name.text, absagen);
        let unvollstaendig = g
            .huelle(&g.schluessel_von(modul, &f.name.text))
            .unvollstaendig
            .is_some();
        je_funktion.push((f.name.text.clone(), h, unvollstaendig));
    });

    // Die vereinigte Menge über den ganzen Baum -- die Paarung ist eine Aussage über das
    // PROGRAMM, nicht über eine Funktion: wer publiziert und wer erwartet, sind fast nie
    // dieselbe Funktion.
    let alle_publiziert: BTreeSet<(String, String)> = je_funktion
        .iter()
        .flat_map(|(_, h, _)| h.publiziert.iter().map(|(a, o, _)| (a.clone(), o.clone())))
        .collect();
    let alle_erwartet: BTreeSet<(String, String)> = je_funktion
        .iter()
        .flat_map(|(_, h, _)| h.erwartet.iter().map(|(a, o, _)| (a.clone(), o.clone())))
        .collect();

    for (name, h, unvollstaendig) in &je_funktion {
        // **W10:** aus einer unteren Schranke wird weder abgesagt noch bestätigt.
        if *unvollstaendig && !h.publiziert.is_empty() {
            absagen.schiebe(
                Absage::hinweis(
                    "V003",
                    h.publiziert[0].2,
                    format!("the pairing in `{name}` is undecidable: the call graph is incomplete here"),
                )
                .mit_notiz(
                    "the payload sets are only a LOWER bound -- no completeness follows \
                        from them",
                ),
            );
            continue;
        }
        // **`V008` — was gespeichert wird, steht in der erklärten Obermenge.**
        //
        // Die Obermenge ist freiwillig; steht sie da, ist sie eine **Zusage über das ganze
        // Programm**: *mehr als DAS wird über dieses Atomic nie veröffentlicht.* Ein Leser
        // darf sich darauf verlassen, ohne jede Schreibstelle zu kennen — und darum ist eine
        // Zeile, die niemand nachrechnet, hier gefährlicher als keine.
        for (at, o, span) in &h.publiziert {
            let Some((_, erlaubt)) = obermengen.iter().find(|(n, _)| n == at) else {
                continue;
            };
            if !erlaubt.contains(o) {
                absagen.schiebe(
                    Absage::fehler(
                        "V008",
                        *span,
                        format!(
                            "`{at}` publishes `{o}` here, and its declared superset does not \
                             contain it"
                        ),
                    )
                    .mit_notiz(format!("declared at the `atomic`: {{ {} }}", erlaubt.join(", ")))
                    .mit_notiz(
                        "the superset is voluntary -- but where it stands it is a promise \
                         about the WHOLE program: a reader relies on it without knowing \
                         every store",
                    ),
                );
            }
        }
        for (at, o, span) in &h.publiziert {
            if !alle_erwartet.contains(&(at.clone(), o.clone())) {
                absagen.schiebe(
                    Absage::fehler(
                        "V001",
                        *span,
                        format!(
                            "`publishes {o}` on `{at}` in `{name}` -- nothing awaits this \
                             payload ON THIS ATOMIC"
                        ),
                    )
                    .mit_notiz(
                        "the pair is (atomic, payload): a counterpart on a DIFFERENT atomic \
                         establishes nothing here",
                    )
                    .mit_notiz(
                        "SPRACHE.md part II §1: ordering is PAIRED, not declared -- a \
                            publication without a counterpart orders nothing",
                    )
                    .mit_notiz("`publishes nothing` says expressly that there is none"),
                );
            }
        }
        for (at, o, span) in &h.erwartet {
            if !alle_publiziert.contains(&(at.clone(), o.clone())) {
                absagen.schiebe(
                    Absage::fehler(
                        "V002",
                        *span,
                        format!(
                            "`awaits {o}` on `{at}` in `{name}` -- nothing publishes this \
                             payload ON THIS ATOMIC"
                        ),
                    )
                    .mit_notiz(
                        "the pair is (atomic, payload): a publication on a DIFFERENT atomic \
                         establishes nothing here",
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
                            None => h.publiziert.push((ziel.clone(), form(&o.text()), s.span)),
                        }
                    }
                }
            }
            StmtArt::AwaitLoad(a) => {
                let quelle = a.quelle.text();
                for o in &a.erwartet {
                    h.erwartet.push((quelle.clone(), form(&o.text()), s.span));
                }
            }
            StmtArt::Exchange(e) => {
                let ort = e.ort.text();
                if let Some(Nutzlast::Orte(liste)) = &e.nutzlast {
                    for o in liste {
                        h.publiziert.push((ort.clone(), form(&o.text()), s.span));
                    }
                }
                for o in e.erwartet.iter().flatten() {
                    h.erwartet.push((ort.clone(), form(&o.text()), s.span));
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

/// **«K5.1» — die Reihenfolge, in der die Ordnung entsteht** (`V006`/`V007`).
///
/// Die Paarung prüft seit dem 2026-08-19 `(Atomic, Nutzlast)` über das ganze Programm. Was
/// sie **nicht** prüfte, ist die Stelle, an der die Ordnung überhaupt entsteht:
///
/// ```gabbro
/// F = true publishes { n };   -- das release-Speichern
/// n = v;                      -- ... und die Nutzlast DANACH
/// ```
///
/// **Ein release-Speichern veröffentlicht, was VOR ihm geschah.** Was danach geschrieben
/// wird, sieht der Leser nicht — die Zeile `publishes { n }` ist dann eine Zusage über eine
/// Schreibung, die es zum Zeitpunkt der Zusage nicht gibt. Gemessen: **still.**
///
/// Spiegelbildlich auf der Leseseite (`V007`): ein `let vorher = n;` **vor** dem `awaits`
/// liest an der Erwerbung vorbei.
///
/// ## Warum das keine Aussage über das Speichermodell ist
///
/// **A10** (`release_stellt_sichtbarkeit_her`) sagt, *dass* release/acquire die Sichtbarkeit
/// herstellen. Diese beiden Regeln sagen, dass das Programm die **Form** hat, für die A10
/// überhaupt gilt. *Das Axiom trug eine Voraussetzung, und niemand prüfte, ob sie erfüllt
/// ist.*
///
/// ## Und was ausdrücklich NICHT fällt
///
/// Eine Nutzlast, die im Rumpf **gar nicht** geschrieben wird, ist kein Fehler — sie kann von
/// einem Gerufenen kommen. Gemeldet wird nur die Umkehrung: geschrieben, aber **danach**.
/// `spaeter_aussen`: was der UMGEBENDE Block nach diesem Unterblock noch schreibt.
///
/// **Ohne das war `V006` einen `if` weit umgehbar** (Rezension 2026-08-20):
///
/// ```gabbro
/// if v > 0 { F = true publishes { n }; }
/// n = v;                                    -- 0 Fehler
/// ```
///
/// Innerhalb des Zweiges ist `b.anweisungen[i + 1..]` leer, und was danach im umgebenden
/// Block steht, sah niemand. *Die Sichtbarkeitsordnung endet aber nicht an einer Klammer* --
/// der Leser sieht `n` nach dem release-Speichern genauso wenig, wenn das Speichern in einem
/// Zweig stand.
fn reihenfolge(
    b: &Block,
    vorher_geschrieben: &[String],
    vorher_gelesen: &[String],
    spaeter_aussen: &[String],
    wo: &str,
    absagen: &mut Absagen,
) {
    let mut geschrieben: Vec<String> = vorher_geschrieben.to_vec();
    let mut gelesen: Vec<String> = vorher_gelesen.to_vec();
    for (i, s) in b.anweisungen.iter().enumerate() {
        match &s.art {
            StmtArt::Publish(p) => {
                // Was schreibt der REST dieses Blocks -- einschliesslich seiner Unterblöcke?
                let mut danach: Vec<Ort> = Vec::new();
                for spaeter in &b.anweisungen[i + 1..] {
                    crate::schreibziele(spaeter, &mut danach);
                }
                let mut danach_namen: Vec<String> =
                    danach.iter().map(|z| grundname(&z.text())).collect();
                danach_namen.extend(spaeter_aussen.iter().cloned());
                if let Nutzlast::Orte(liste) = &p.nutzlast {
                    for o in liste {
                        let name = grundname(&o.text());
                        if geschrieben.contains(&name) {
                            continue;
                        }
                        if !danach_namen.contains(&name) {
                            continue;
                        }
                        absagen.schiebe(
                            Absage::fehler(
                                "V006",
                                s.span,
                                format!(
                                    "`{}` publishes `{name}` in `{wo}`, and `{name}` is \
                                     written AFTERWARDS",
                                    p.ziel.text()
                                ),
                            )
                            .mit_notiz(
                                "a release store publishes what happened BEFORE it -- a \
                                 write after it is invisible to the reader",
                            )
                            .mit_notiz(
                                "A10 (`release_stellt_sichtbarkeit_her`) says THAT \
                                 release/acquire establish visibility; this rule says the \
                                 program has the shape the axiom needs",
                            ),
                        );
                    }
                }
            }
            StmtArt::AwaitLoad(a) => {
                for o in &a.erwartet {
                    let name = grundname(&o.text());
                    if !gelesen.contains(&name) {
                        continue;
                    }
                    absagen.schiebe(
                        Absage::fehler(
                            "V007",
                            s.span,
                            format!(
                                "`{wo}` reads `{name}` BEFORE the `awaits` on `{}`",
                                a.quelle.text()
                            ),
                        )
                        .mit_notiz(
                            "an acquire load makes the payload visible from that point on \
                             -- a read before it sees the old value",
                        ),
                    );
                }
            }
            _ => {}
        }
        // Diese Anweisung SELBST trägt zu beidem bei -- erst danach, damit sie sich nicht
        // selbst deckt.
        let mut z: Vec<Ort> = Vec::new();
        crate::schreibziele(s, &mut z);
        geschrieben.extend(z.iter().map(|o| grundname(&o.text())));
        for e in crate::eigene_ausdruecke(s) {
            orte_gelesen(e, &mut gelesen);
        }
        if let StmtArt::AwaitLoad(a) = &s.art {
            gelesen.extend(a.erwartet.iter().map(|o| grundname(&o.text())));
        }
        // Was der umgebende Block NACH dieser Anweisung noch schreibt -- plus das, was
        // schon von weiter aussen mitgereicht wurde.
        let mut spaeter: Vec<String> = spaeter_aussen.to_vec();
        for nach in &b.anweisungen[i + 1..] {
            let mut z: Vec<Ort> = Vec::new();
            crate::schreibziele(nach, &mut z);
            spaeter.extend(z.iter().map(|o| grundname(&o.text())));
        }
        for k in crate::unterbloecke(s) {
            reihenfolge(k, &geschrieben, &gelesen, &spaeter, wo, absagen);
        }
    }
}

/// `s.bytes[i].x` -> `s`.
fn grundname(k: &str) -> String {
    k.split(['.', '[']).next().unwrap_or(k).to_string()
}

/// Ueber `crate::alle_orte` -- der Handlaeufer hier hatte `_ => {}` und stieg nicht in
/// einen `OrtSuffix::Index` ab (2026-08-20).
fn orte_gelesen(e: &Expr, aus: &mut Vec<String>) {
    aus.extend(crate::alle_orte(e).into_iter().map(|o| grundname(&o.text())));
}
