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
    /// **Every atomic that carries a payload ANYWHERE** -- published, awaited or exchanged,
    /// no matter which ordering word stands at it.
    ///
    /// This is not `publiziert` with the sites dropped: a `relaxed` store with a payload
    /// goes into `relaxed_mit_last` and never reaches `publiziert`, and for the question
    /// *"is this atomic declared payload-free?"* it must count all the same. Without that
    /// line `V009` would treat exactly the atomics `V004` already complains about as
    /// payload-free and complain a second time.
    traegt_last: BTreeSet<String>,
}

/// **What `V009` needs to know about the program** -- gathered once, read per function.
struct Torlage<'a> {
    /// Atomics that carry no payload anywhere: nothing publishes on them, nothing awaits
    /// them, no superset is declared, and no `observed by` puts the counterpart in silicon.
    lastfrei: &'a BTreeSet<String>,
    /// **Module-level shared and MUTABLE names** -- `static mut`, `atomic`, `accumulates`,
    /// and the tables. A parameter is deliberately not one: two functions name their
    /// pointer `b` without meaning the same memory (`beispiele/14`).
    geteilte: &'a BTreeSet<String>,
    /// What THIS function writes itself. A place this body writes is this core's own value,
    /// not a foreign payload -- `beispiele/42`:310 is that case and must not fall.
    eigene: BTreeSet<String>,
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

    // **The module-level shared and mutable names, and who writes them.**
    //
    // Both sets exist for the two rules the ordering sample forced (`ORDNUNGSFINDER.md`):
    // `V009` needs to know what counts as a foreign place, `V010` needs to know which
    // function wrote the payload.
    let mut geteilte: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Statisch(s) if s.veraenderlich => {
            geteilte.insert(s.name.text.clone());
        }
        ItemArt::Atomic(a) => {
            geteilte.insert(a.name.text.clone());
        }
        ItemArt::Accumulates(a) => {
            geteilte.insert(a.name.text.clone());
        }
        ItemArt::Tabelle(t) => {
            geteilte.insert(t.name.text.clone());
        }
        _ => {}
    });
    let mut schreiber: std::collections::BTreeMap<String, BTreeSet<String>> = Default::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let k = g.schluessel_von(modul, &f.name.text);
        let mut z: Vec<Ort> = Vec::new();
        for s in &b.anweisungen {
            crate::schreibziele(s, &mut z);
        }
        for o in &z {
            schreiber
                .entry(grundname(&o.text()))
                .or_default()
                .insert(k.clone());
        }
    });

    // **Erst die eigenen Hälften je Funktion, dann die transitive Vereinigung.**
    let mut je_funktion: Vec<(String, Haelften, bool, Option<String>)> = Vec::new();
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
        let schluessel = g.schluessel_von(modul, &f.name.text);
        let unvollstaendig = g.huelle(&schluessel).unvollstaendig.is_some();
        je_funktion.push((f.name.text.clone(), h, unvollstaendig, Some(schluessel)));
    });
    // **Und der `can_fail`-Rumpf einer Probe** (2026-08-20).
    //
    // Gefunden beim Schreiben eines virtio-net-Treibers: die Gegenseite einer
    // Veroeffentlichung an ein GERAET wollte als Probe geschrieben werden -- der richtige
    // Ort, denn eine falsifizierbare Aussage ueber Hardware IST eine Probe. `V001` fiel
    // trotzdem, weil dieser Pass ueber `ItemArt::Funktion` laeuft und sonst nichts.
    //
    // > **Dieselbe Klasse fiel am selben Tag bei M1**, das ueber `beispiele/06` meldete
    // > *„this file has no function body"*, waehrend im `can_fail` gerechnet wurde. Ein
    // > Rumpf, den kein Pass liest, ist ein Rumpf ohne Leser -- und ein `check` ist der eine
    // > Ort, an dem eine Zusage ueber die Maschine steht.
    //
    // *Die Vollstaendigkeit der Rufhuelle steht hier nicht zur Verfuegung* -- eine Probe hat
    // keinen Eintrag im Rufgraphen. Sie zaehlt darum als vollstaendig: was sie erwartet,
    // erwartet sie, und was sie veroeffentlicht, wuerde `N027` ohnehin ablehnen.
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Check(c) = &item.art else { return };
        let mut h = Haelften::default();
        sammle(&c.can_fail, &ordnungen, &mut h);
        reihenfolge(&c.can_fail, &[], &[], &[], &c.name.text, absagen);
        je_funktion.push((c.name.text.clone(), h, false, None));
    });

    // Die vereinigte Menge über den ganzen Baum -- die Paarung ist eine Aussage über das
    // PROGRAMM, nicht über eine Funktion: wer publiziert und wer erwartet, sind fast nie
    // dieselbe Funktion.
    // **«V9»: welche Atomics haben ihre Gegenseite AUSSERHALB dieser Einheit?**
    let mut beobachtet: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Atomic(a) = &item.art {
            if a.beobachtet.is_some() {
                beobachtet.insert(a.name.text.clone());
            }
        }
    });
    let alle_publiziert: BTreeSet<(String, String)> = je_funktion
        .iter()
        .flat_map(|(_, h, _, _)| h.publiziert.iter().map(|(a, o, _)| (a.clone(), o.clone())))
        .collect();
    let alle_erwartet: BTreeSet<(String, String)> = je_funktion
        .iter()
        .flat_map(|(_, h, _, _)| h.erwartet.iter().map(|(a, o, _)| (a.clone(), o.clone())))
        .collect();

    // **`V009`: which atomics are declared PAYLOAD-FREE over the whole program?**
    //
    // Not "which say `publishes nothing` here" -- that is a statement about one store. The
    // question is the categorial one from `SPRACHE.md` part II §1: an atomic on which
    // nothing publishes, which nothing awaits, which declares no superset and whose
    // counterpart is not in silicon (`observed by`) is the "payload-free" case of the three.
    let mut lastfrei: BTreeSet<String> = BTreeSet::new();
    {
        let mut traegt: BTreeSet<String> = je_funktion
            .iter()
            .flat_map(|(_, h, _, _)| h.traegt_last.iter().cloned())
            .collect();
        traegt.extend(obermengen.iter().map(|(n, _)| n.clone()));
        traegt.extend(beobachtet.iter().cloned());
        for (n, _) in &ordnungen {
            if !traegt.contains(n) {
                lastfrei.insert(n.clone());
            }
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut z: Vec<Ort> = Vec::new();
        for s in &b.anweisungen {
            crate::schreibziele(s, &mut z);
        }
        let lage = Torlage {
            lastfrei: &lastfrei,
            geteilte: &geteilte,
            eigene: z.iter().map(|o| grundname(&o.text())).collect(),
        };
        tore(b, &lage, &mut Vec::new(), &f.name.text, absagen);
    });

    for (name, h, unvollstaendig, schluessel) in &je_funktion {
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
        // **`V010` -- the publication comes from a DIFFERENT writer than the payload.**
        //
        // `ORDNUNGSSTICHPROBE-BEFUND.md` no. 34 writes the case out: one could put
        // `CWG_SEALED = true publishes { CWG_MAX }` there, and the static name comparison of
        // §1 would let it through. *It would be wrong all the same: the `release` of core 0
        // publishes THE WRITES OF CORE 0, not the `fetch_max` of core 5.*
        //
        // > **A pairing that type-checks and does not carry is worse than none** -- it looks
        // > like a promise and is a claim, the same class as the `protects` clause of
        // > `beispiele/05` that `H007` took away.
        //
        // The reachable hull is the right question and not the body: `V006` already drew
        // that line (*"a payload that is not written in the body at all is no error -- it
        // can come from a callee"*), and two rules with two answers to one question are one
        // answer too many.
        for (at, o, span) in &h.publiziert {
            let Some(k) = schluessel else { continue };
            let basis = grundname(o);
            // A parameter is not a shared name: `b.daten` in two functions is two `b`.
            if !geteilte.contains(&basis) {
                continue;
            }
            let Some(wer) = schreiber.get(&basis) else {
                continue;
            };
            // Nobody writes it in this unit -- then the writer is outside, and an outside
            // writer is what `observed by` and the assumption layer are for, not this rule.
            if wer.is_empty() {
                continue;
            }
            let erreichbar = ruf_huelle(&g, k);
            if wer.iter().any(|w| erreichbar.contains(w)) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "V010",
                    *span,
                    format!(
                        "`{at}` publishes `{basis}` in `{name}`, and `{basis}` is written by \
                         a writer this one never reaches"
                    ),
                )
                .mit_notiz(format!(
                    "written in: {}",
                    wer.iter().cloned().collect::<Vec<_>>().join(", ")
                ))
                .mit_notiz(
                    "a release store publishes THE WRITES OF ITS OWN THREAD -- a write by \
                     another core is not made visible by it",
                )
                .mit_notiz(
                    "the pairing compares names; this compares the writer -- and a pairing \
                     that type-checks and does not carry is worse than none",
                ),
            );
        }
        for (at, o, span) in &h.publiziert {
            // **«V9»: die Gegenseite steht in SILIZIUM, und das sagt die Deklaration.**
            //
            // `observed by <assume>` nennt, WER liest -- und das ist kein zweites Programm.
            // *Die Regel wird nicht gelockert, sondern ihre Praemisse wird sichtbar:* sie
            // gilt zwischen zwei Stuecken Software, und hier ist nur eines davon Software.
            //
            // Was die Zusage traegt, ist damit die Annahmenschicht und nicht dieser Pass --
            // `gabbro annahmen` zaehlt sie, `N031` verlangt einen Falsifikator dafuer.
            if beobachtet.contains(at) {
                continue;
            }
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
            // **«V9» gilt in BEIDE Richtungen, und die erste Fassung nahm nur eine**
            // (2026-08-20, am selben Tag korrigiert).
            //
            // `observed by` stand nur in der Veroeffentlichungsschleife. Damit war ein
            // `atomic X : u32 acquire observed by <assume>` -- genau die Form, die
            // `messung/treiber/virtio-net.gab` fuer `USED_IDX` deklariert -- **nie lesbar**:
            // jedes `awaits` darauf fiel an `V002`.
            //
            // > *Und im Korpus fiel es nicht auf, weil `USED_IDX` dort deklariert und von
            // > NIEMANDEM gelesen wird.* Ein Geraet, das SCHREIBT, war damit nicht
            // > abfragbar -- die Haelfte des Konstrukts, die den Empfangspfad traegt.
            //
            // Die Sache ist symmetrisch: bei `AVAIL_IDX` steht der Leser in Silizium, bei
            // `USED_IDX` der Schreiber. **Eine Klausel, die nur eine Richtung kennt, kennt
            // die Sache nicht.**
            if beobachtet.contains(at) {
                continue;
            }
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
                    if !liste.is_empty() {
                        h.traegt_last.insert(grundname(&ziel));
                    }
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
                if !a.erwartet.is_empty() {
                    h.traegt_last.insert(grundname(&quelle));
                }
                for o in &a.erwartet {
                    h.erwartet.push((quelle.clone(), form(&o.text()), s.span));
                }
            }
            StmtArt::Exchange(e) => {
                let ort = e.ort.text();
                if let Some(Nutzlast::Orte(liste)) = &e.nutzlast {
                    if !liste.is_empty() {
                        h.traegt_last.insert(grundname(&ort));
                    }
                    for o in liste {
                        h.publiziert.push((ort.clone(), form(&o.text()), s.span));
                    }
                }
                for o in e.erwartet.iter().flatten() {
                    h.traegt_last.insert(grundname(&ort));
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

/// **The functions reachable from `start`, itself included.**
///
/// `Graph::huelle` answers with EFFECTS; the question `V010` asks is *which function*, and
/// an effect name cannot answer it. The walk is the same one, over `Knoten::ruft`.
fn ruf_huelle(g: &crate::aufrufgraph::Graph, start: &str) -> BTreeSet<String> {
    let mut aus: BTreeSet<String> = BTreeSet::new();
    let mut offen = vec![start.to_string()];
    while let Some(n) = offen.pop() {
        if !aus.insert(n.clone()) {
            continue;
        }
        if let Some(k) = g.knoten.get(&n) {
            offen.extend(k.ruft.iter().cloned());
        }
    }
    aus
}

/// **`V009` -- the gate whose pairing nobody wrote.**
///
/// `SPRACHE.md` part II §1 has three type rules, and all three CHECK a pairing that somebody
/// wrote down. None of them notices that one is MISSING -- `ORDNUNGSSTICHPROBE-BEFUND.md`
/// §5.1 states it as the gap:
///
/// > *"They check pairings; a site that declares `publishes nothing`/`relaxed` passes.
/// > Whoever declares this field payload-free gets no error -- he gets a compiler that keeps
/// > silent."*
///
/// **A form that keeps silent says yes for years.** The shape this rule looks for is the one
/// the finding wrote out twice (`aarch64/mmu.rs`:800 and `loader.rs`:682):
///
/// ```gabbro
/// let sealed = SEALED;             -- a plain load of a payload-free atomic
/// if sealed { return granule; }    -- its value gates, and behind the gate a FOREIGN
/// ```                              --   shared place is read
///
/// ## What it deliberately does not take
///
/// * an `exchange` result is not a gate. An RMW is the THIRD form of the pairing and carries
///   its own `publishes`/`awaits` slot; §1's rules already reach it. Counting it would make
///   `beispiele/42`:310 fall, and that one is right.
/// * a place this body writes itself is not a foreign payload -- it is this core's value.
/// * a read under `locks`/`observes` is ordered by the lock (K1 of the sampling protocol).
///
/// **The way out is never silence.** Name the payload (`publishes { P }` + `awaits { P }`),
/// take the lock, or declare `observed by` -- three sentences, and each of them is checked.
fn tore(
    b: &Block,
    l: &Torlage,
    gebunden: &mut Vec<(String, String)>,
    wo: &str,
    absagen: &mut Absagen,
) {
    for (i, s) in b.anweisungen.iter().enumerate() {
        // **A plain load, and nothing else counts as one.** `awaits` and `exchange` are
        // their own statement kinds, so a `Let` can never be either.
        if let StmtArt::Let(le) = &s.art {
            if let ExprArt::Ort(o) = &le.wert.art {
                if o.suffixe.is_empty() && l.lastfrei.contains(&o.basis.text) {
                    gebunden.push((le.name.text.clone(), o.basis.text.clone()));
                }
            }
        }
        let mut melde = |at: &str, hinter: &[Stmt]| {
            let Some((platz, _)) = fremde_lesung(hinter, at, l) else {
                return false;
            };
            absagen.schiebe(
                Absage::fehler(
                    "V009",
                    s.span,
                    format!(
                        "`{at}` carries no payload and gates a branch in `{wo}` behind which \
                         `{platz}` is read"
                    ),
                )
                .mit_notiz(format!(
                    "nothing publishes on `{at}` and nothing awaits it -- so it is the \
                     payload-free case of SPRACHE.md part II §1, and `{platz}` says it is not"
                ))
                .mit_notiz(
                    "a value that decides whether a foreign place may be read IS a payload \
                     -- name it, take a lock, or declare `observed by`",
                )
                .mit_notiz(
                    "the three rules of §1 check a pairing that is written down; this one \
                     asks whether one is MISSING",
                ),
            );
            true
        };
        match &s.art {
            StmtArt::Wenn(w) => {
                let mut gesagt = false;
                for (bed, zweig) in &w.zweige {
                    if gesagt {
                        break;
                    }
                    let Some(at) = tor(bed, gebunden, l) else {
                        continue;
                    };
                    gesagt = melde(&at, &zweig.anweisungen);
                    if !gesagt {
                        if let Some(sonst) = &w.sonst {
                            gesagt = melde(&at, &sonst.anweisungen);
                        }
                    }
                    // **And what stands AFTER the `if`, when the branch ends the flow.**
                    // `if !sealed { return default; }` puts the payload behind the gate
                    // without a block around it -- the literal shape of finding no. 34.
                    // `&[]` for the divergent names is the safe direction: fewer ends
                    // recognised means fewer refusals.
                    if !gesagt && crate::endet_immer(zweig, &[]) {
                        gesagt = melde(&at, &b.anweisungen[i + 1..]);
                    }
                }
            }
            StmtArt::Match(m) => {
                if let Some(at) = tor(&m.gegenstand, gebunden, l) {
                    for z in &m.zweige {
                        if melde(&at, &z.rumpf.anweisungen) {
                            break;
                        }
                    }
                }
            }
            StmtArt::Narrow(n) => {
                let name = n.ort.basis.text.clone();
                let at = gebunden
                    .iter()
                    .find(|(lok, _)| *lok == name)
                    .map(|(_, a)| a.clone())
                    .or_else(|| {
                        (n.ort.suffixe.is_empty() && l.lastfrei.contains(&name)).then_some(name)
                    });
                if let Some(at) = at {
                    if !melde(&at, &n.sonst.anweisungen) {
                        melde(&at, &b.anweisungen[i + 1..]);
                    }
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            tore(k, l, &mut gebunden.clone(), wo, absagen);
        }
    }
}

/// **Does this expression gate on a payload-free atomic?** -- the name of that atomic.
fn tor(e: &Expr, gebunden: &[(String, String)], l: &Torlage) -> Option<String> {
    for o in crate::alle_orte(e) {
        let n = &o.basis.text;
        if let Some((_, at)) = gebunden.iter().find(|(lok, _)| lok == n) {
            return Some(at.clone());
        }
        if o.suffixe.is_empty() && l.lastfrei.contains(n) {
            return Some(n.clone());
        }
    }
    None
}

/// **The first read of a FOREIGN shared place behind the gate.**
///
/// Foreign means three things at once, and all three are needed: module-level shared and
/// mutable, not the gating atomic itself, and not written by this body.
fn fremde_lesung(stmts: &[Stmt], at: &str, l: &Torlage) -> Option<(String, Span)> {
    for s in stmts {
        // **A lock orders what stands under it** -- K1 of the sampling protocol. In Gabbro
        // the atomic would fall away entirely there.
        if matches!(s.art, StmtArt::Sperrt(_) | StmtArt::Observiert(_)) {
            continue;
        }
        for e in crate::eigene_ausdruecke(s) {
            for o in crate::alle_orte(e) {
                let basis = grundname(&o.text());
                if basis == at || !l.geteilte.contains(&basis) || l.eigene.contains(&basis) {
                    continue;
                }
                return Some((o.text(), o.span));
            }
        }
        for k in crate::unterbloecke(s) {
            if let Some(t) = fremde_lesung(&k.anweisungen, at, l) {
                return Some(t);
            }
        }
    }
    None
}
