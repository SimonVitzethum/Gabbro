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
use std::collections::BTreeMap;

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
        // **V011 -- a clean awaited load expires on a publish to the same carrier.**
        stale_gebrauch(b, &ordnungen, &f.name.text, absagen);
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
        stale_gebrauch(&c.can_fail, &ordnungen, &c.name.text, absagen);
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
    let alle_publiziert: BTreeSet<(String, String)>;
    let alle_erwartet: BTreeSet<(String, String)>;
    // **Halves behind an incomplete hull stand beside the global sets, not in them.**
    //
    // An incomplete hull yields only a LOWER bound (W10): a half it names neither
    // redeems a complete orphan nor confirms one. Before this split the undecidable
    // halves sat inside `alle_publiziert` / `alle_erwartet`, so an incomplete
    // function silently redeemed a complete function's orphan (and vice versa) --
    // the doubt never propagated. The complete sets below hold the decidable
    // halves only; a complete half whose SOLE counterpart is undecidable gets the
    // `V003` hint at its own `V001`/`V002` site instead of the refusal -- and
    // instead of silence. From a lower bound nothing is refused and nothing is
    // confirmed, and a hint is neither.
    let mut unsicher_publiziert: BTreeSet<(String, String)> = BTreeSet::new();
    let mut unsicher_erwartet: BTreeSet<(String, String)> = BTreeSet::new();
    {
        let mut voll_p: BTreeSet<(String, String)> = BTreeSet::new();
        let mut voll_e: BTreeSet<(String, String)> = BTreeSet::new();
        for (_, h, unvollstaendig, _) in &je_funktion {
            let (zp, ze) = if *unvollstaendig {
                (&mut unsicher_publiziert, &mut unsicher_erwartet)
            } else {
                (&mut voll_p, &mut voll_e)
            };
            zp.extend(
                h.publiziert
                    .iter()
                    .map(|(a, o, _)| (a.clone(), o.clone())),
            );
            ze.extend(
                h.erwartet.iter().map(|(a, o, _)| (a.clone(), o.clone())),
            );
        }
        alle_publiziert = voll_p;
        alle_erwartet = voll_e;
    }

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
    // **And the `can_fail` body of a probe, for the same reason V001 got it in 2026-08-20:**
    // a falsifiable statement about the machine IS a probe, and a body no pass reads is a
    // body without a reader.
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                tore_im_rumpf(b, &f.name.text, &lastfrei, &geteilte, absagen);
            }
        }
        ItemArt::Check(c) => {
            tore_im_rumpf(&c.can_fail, &c.name.text, &lastfrei, &geteilte, absagen)
        }
        _ => {}
    });
    // **V012 -- the unguarded user-copy handoff, below.**
    benutzer_handoff(baum, &u, &g, absagen);

    for (name, h, unvollstaendig, schluessel) in &je_funktion {
        // **W10:** aus einer unteren Schranke wird weder abgesagt noch bestätigt.
        //
        // The trigger is ANY half, publish or await: an incomplete hull that only
        // awaits got no hint before (the publish set was the whole trigger) and
        // its `V002` ran against a lower-bound global set -- a refusal drawn from
        // what the graph cannot see. A `relaxed`-only half takes the other road
        // on purpose: it never reaches `publiziert`/`erwartet`, so no `V003`
        // fires for it and `V004`/`V005` speak normally. Ordering strength is a
        // property of the declared atomic, not of the hull.
        if *unvollstaendig && (!h.publiziert.is_empty() || !h.erwartet.is_empty()) {
            let span = h
                .publiziert
                .first()
                .map(|(_, _, s)| *s)
                .or_else(|| h.erwartet.first().map(|(_, _, s)| *s))
                .expect("one half is non-empty: the condition just checked it");
            absagen.schiebe(
                Absage::hinweis(
                    "V003",
                    span,
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
                // **The counterpart exists, but only behind an incomplete hull.**
                // Refusing here would draw completeness from a lower bound; staying
                // silent would confirm what the graph cannot see. W10 leaves one
                // answer: the `V003` hint, at the complete function's own site.
                if unsicher_erwartet.contains(&(at.clone(), o.clone())) {
                    absagen.schiebe(
                        Absage::hinweis(
                            "V003",
                            *span,
                            format!(
                                "`publishes {o}` on `{at}` in `{name}` -- the only \
                                 counterpart stands in a function whose call hull is \
                                 incomplete"
                            ),
                        )
                        .mit_notiz(
                            "the payload sets of an incomplete hull are only a LOWER \
                             bound -- no completeness follows from them",
                        ),
                    );
                    continue;
                }
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
                // **Same doubt, await side:** the only publisher stands behind an
                // incomplete hull. Hint, not refusal and not silence (see above).
                if unsicher_publiziert.contains(&(at.clone(), o.clone())) {
                    absagen.schiebe(
                        Absage::hinweis(
                            "V003",
                            *span,
                            format!(
                                "`awaits {o}` on `{at}` in `{name}` -- the only \
                                 counterpart stands in a function whose call hull is \
                                 incomplete"
                            ),
                        )
                        .mit_notiz(
                            "the payload sets of an incomplete hull are only a LOWER \
                             bound -- no completeness follows from them",
                        ),
                    );
                    continue;
                }
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
                // **The await side carries the same ordering promise.** Until now only
                // the publish side checked it: an `awaits` on a `relaxed` atomic -- or
                // on one without any ordering word, which the emitter lowers to
                // `memory_order_relaxed` on BOTH sides -- loads without acquire, so the
                // payload it names is a promise without a mechanism. Same question as
                // `V004`/`V005` at the store, same answer here: the pair goes to
                // `relaxed_mit_last` and never reaches `erwartet`, so no `V002` fires
                // beside it.
                let stille = ordnungen.iter().find_map(|(n, o)| {
                    (quelle.split(['.', '[']).next() == Some(n.as_str())
                        && matches!(o, Some(Ordnung::Relaxed) | None))
                    .then_some(o.is_some())
                });
                for o in &a.erwartet {
                    match stille {
                        Some(erklaert) => {
                            h.relaxed_mit_last.push((quelle.clone(), s.span, erklaert))
                        }
                        None => h.erwartet.push((quelle.clone(), form(&o.text()), s.span)),
                    }
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
        // selbst deckt. Die Lesung steigt dabei in Unterblöcke ab (`leseziele`): ein
        // Lesen in einem FRÜHEREN Zweig steht sonst nicht in `gelesen`, wenn ein
        // späteres `awaits` geprüft wird -- und `V007` bliebe der Spiegel, der nichts
        // zeigt (`gift/722`). Die Schreibung tat das seit jeher (`schreibziele`
        // steigt ab); zwei Antworten auf eine Frage wären eine zuviel.
        //
        // Der Abstieg in die EIGENEN Unterblöcke läuft mit dem Stand VOR dieser
        // Anweisung: was darin steht -- hintere Lesungen, das `awaits` selbst --
        // ist für die Prüfung darin noch nicht geschehen. Mit dem Stand danach
        // sähe ein `awaits` im Schleifenrumpf die Lesungen hinter ihm und fiele
        // über sich selbst (`beispiele/41`: ein Fehlalarm, gemessen).
        let gelesen_vorher: Vec<String> = gelesen.clone();
        let mut z: Vec<Ort> = Vec::new();
        crate::schreibziele(s, &mut z);
        geschrieben.extend(z.iter().map(|o| grundname(&o.text())));
        leseziele(s, &mut gelesen);
        // Was der umgebende Block NACH dieser Anweisung noch schreibt -- plus das, was
        // schon von weiter aussen mitgereicht wurde.
        let mut spaeter: Vec<String> = spaeter_aussen.to_vec();
        for nach in &b.anweisungen[i + 1..] {
            let mut z: Vec<Ort> = Vec::new();
            crate::schreibziele(nach, &mut z);
            spaeter.extend(z.iter().map(|o| grundname(&o.text())));
        }
        for k in crate::unterbloecke(s) {
            reihenfolge(k, &geschrieben, &gelesen_vorher, &spaeter, wo, absagen);
        }
    }
}

/// **V011 -- a clean awaited load expires on a publish to the same carrier.**
///
/// An `awaits` load is fresh until a concurrent store to the SAME carrier lands: a
/// `Publish` to that carrier between the load and the use invalidates the loaded
/// value, and any later read of the old binding without revalidation falls.
///
/// ```gabbro
/// let f = F awaits { n };
/// n = 1;
/// F = true publishes { n };
/// if f { return n; }   -- V011: `f` was expired by the publish above
/// ```
///
/// Revalidation is a fresh `awaits` binding of the same name AFTER the publish; a
/// publish to a DIFFERENT carrier does not expire; a publish BEFORE the load does
/// not expire either. Only clean carriers are tracked (declared `acquire`,
/// `release` or `seq`): a `relaxed` load or one without an ordering word already
/// falls at `V004`/`V005`, and a second verdict there would double-book one defect.
///
/// Branch-local on purpose: a publish inside one `if` arm expires uses inside that
/// arm, not uses after the `if` and not uses in a sibling arm. The other direction
/// (union over arms) would refuse programs where only one path publishes, and the
/// corpus (`beispiele/42`, match arms that await in one arm and publish in another)
/// says that path is the common one. Fewer ends recognised means fewer refusals.
///
/// Call arguments are not read positions here, for the same reason `V007` does not
/// see them either (`eigene_ausdruecke` carries no `Ruf`): `if`, `match`, `return`,
/// `let`/`assignment` values and `narrow` subjects are. An `exchange` to the same
/// carrier does NOT expire either -- this rule tracks `Publish` only, and says so.
fn stale_gebrauch(
    b: &Block,
    ordnungen: &[(String, Option<Ordnung>)],
    wo: &str,
    absagen: &mut Absagen,
) {
    let mut live: Vec<(String, String)> = Vec::new();
    let mut stale: Vec<String> = Vec::new();
    stale_block(b, ordnungen, wo, &mut live, &mut stale, absagen);
}

/// Live awaited bindings (`var -> carrier`) and expired ones, threaded linearly
/// through one block; sub-blocks are entered with a clone and never merged back.
fn stale_block(
    b: &Block,
    ordnungen: &[(String, Option<Ordnung>)],
    wo: &str,
    live: &mut Vec<(String, String)>,
    stale: &mut Vec<String>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        for name in gelesene_namen(s) {
            if stale.iter().any(|v| v == &name) {
                absagen.schiebe(
                    Absage::fehler(
                        "V011",
                        s.span,
                        format!(
                            "`{name}` was awaited in `{wo}` and is used after a publish \
                             to the same carrier without revalidation"
                        ),
                    )
                    .mit_notiz(
                        "an acquire load is fresh until a store to the same carrier lands \
                         -- after the publish the old value is stale",
                    )
                    .mit_notiz(
                        "revalidate with a fresh `awaits` load after the publish; a publish \
                         to a different carrier, or before the load, does not expire it",
                    ),
                );
                break;
            }
        }
        match &s.art {
            StmtArt::AwaitLoad(a) => {
                live.retain(|(v, _)| v != &a.name.text);
                stale.retain(|v| v != &a.name.text);
                if ist_sauber(&grundname(&a.quelle.text()), ordnungen) {
                    live.push((a.name.text.clone(), grundname(&a.quelle.text())));
                }
            }
            StmtArt::Publish(p) => {
                let traeger = grundname(&p.ziel.text());
                let mut abgelaufen: Vec<String> = Vec::new();
                live.retain(|(v, c)| {
                    if c == &traeger {
                        abgelaufen.push(v.clone());
                        false
                    } else {
                        true
                    }
                });
                for v in abgelaufen {
                    if !stale.iter().any(|x| x == &v) {
                        stale.push(v);
                    }
                }
            }
            StmtArt::Let(l) => {
                live.retain(|(v, _)| v != &l.name.text);
                stale.retain(|v| v != &l.name.text);
            }
            StmtArt::Exchange(e) => {
                live.retain(|(v, _)| v != &e.name.text);
                stale.retain(|v| v != &e.name.text);
            }
            StmtArt::LetSonst(l) => {
                live.retain(|(v, _)| v != &l.name.text);
                stale.retain(|v| v != &l.name.text);
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            let mut live2 = live.clone();
            let mut stale2 = stale.clone();
            stale_block(k, ordnungen, wo, &mut live2, &mut stale2, absagen);
        }
    }
}

/// Clean means the carrier declares an ordering that carries: `acquire`, `release`
/// or `seq`. `relaxed` and the missing word lower to `memory_order_relaxed` on both
/// sides and already fall at `V004`/`V005`. An undeclared carrier is tracked: the
/// rule knows the statement shape, not the declaration, and silence there would be
/// fail-open.
fn ist_sauber(traeger: &str, ordnungen: &[(String, Option<Ordnung>)]) -> bool {
    match ordnungen.iter().find(|(n, _)| n == traeger) {
        Some((_, Some(Ordnung::Acquire) | Some(Ordnung::Release) | Some(Ordnung::Seq))) => true,
        Some(_) => false,
        None => true,
    }
}

/// Every place a statement itself reads: its own expressions plus the `narrow`
/// subject, which `eigene_ausdruecke` does not carry. Same positions `V007` reads;
/// call arguments stay out for the same reason they stay out there.
fn gelesene_namen(s: &Stmt) -> Vec<String> {
    let mut aus: Vec<String> = Vec::new();
    for e in crate::eigene_ausdruecke(s) {
        for o in crate::alle_orte(e) {
            aus.push(o.basis.text.clone());
        }
    }
    if let StmtArt::Narrow(n) = &s.art {
        aus.push(n.ort.basis.text.clone());
    }
    aus
}

/// `s.bytes[i].x` -> `s`.
fn grundname(k: &str) -> String {
    k.split(['.', '[']).next().unwrap_or(k).to_string()
}

/// Mirror of `crate::schreibziele` for the read side: every place an instruction
/// reads -- its own expressions, the payload an `awaits` names (an acquire load is
/// a read of what follows it), and everything inside its sub-blocks.
///
/// `reihenfolge` accumulated reads with `eigene_ausdruecke` only, so a read inside
/// a PRECEDING sibling branch never reached `gelesen`: `V007` missed exactly the
/// shape `gift/186` closed for `V006`. Branches of ONE `if` stay separate all the
/// same -- each is entered with the state from BEFORE the statement, so a read in
/// one arm never taints an `awaits` in another.
fn leseziele(s: &Stmt, out: &mut Vec<String>) {
    for e in crate::eigene_ausdruecke(s) {
        orte_gelesen(e, out);
    }
    if let StmtArt::AwaitLoad(a) = &s.art {
        out.extend(a.erwartet.iter().map(|o| grundname(&o.text())));
    }
    for k in crate::unterbloecke(s) {
        for i in &k.anweisungen {
            leseziele(i, out);
        }
    }
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

/// One body's share of `V009` -- what this body writes is gathered here, because a place it
/// writes itself is this core's value and not a foreign payload.
fn tore_im_rumpf(
    b: &Block,
    name: &str,
    lastfrei: &BTreeSet<String>,
    geteilte: &BTreeSet<String>,
    absagen: &mut Absagen,
) {
    let mut z: Vec<Ort> = Vec::new();
    for s in &b.anweisungen {
        crate::schreibziele(s, &mut z);
    }
    let lage = Torlage {
        lastfrei,
        geteilte,
        eigene: z.iter().map(|o| grundname(&o.text())).collect(),
    };
    tore(b, &lage, &mut Vec::new(), name, absagen);
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
                    let mut gesagt = false;
                    for z in &m.zweige {
                        if melde(&at, &z.rumpf.anweisungen) {
                            gesagt = true;
                            break;
                        }
                    }
                    // **And what stands AFTER the `match`, when an arm ends the flow** --
                    // the rule `if` has above, for every kind of match (review 2026-09-21,
                    // fix lane F1; lifted by Simon 2026-09-26). `match s { 0 => { return X; }
                    // … } return payload;` puts the read behind the gate exactly like
                    // `if s == 0 { return X; } return payload;`. `&[]` for the divergent
                    // names is the safe direction: fewer ends recognised, fewer refusals.
                    if !gesagt
                        && m.zweige.iter().any(|z| crate::endet_immer(&z.rumpf, &[]))
                    {
                        melde(&at, &b.anweisungen[i + 1..]);
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

/// **V012 -- the unguarded user-copy handoff.**
///
/// The Adressraum shape (`Grammatik/Adressraum.lean`): a validated copy is a region, a
/// copy, and the check over the SAME triple -- inseparable by shape, because check and
/// copy name the same region, address, and length (`GepruefteKopie`). A check over one
/// triple paired with a copy over another is not of that shape; it is the TOCTOU
/// sequence (`PruefDannKopie`), sound only under the named single-copy premise
/// (`EinSnapshot`).
///
/// At the checker the inseparability ends at the body boundary: a function that checks
/// a `user`-space pointer and then hands it to a callee puts the check in one body and
/// the use in another. The user side may rewrite the bytes between them, and no fact
/// the checker holds crosses that window -- so the handoff is refused unless the use
/// is covered where it stands:
///
/// ```gabbro
/// impl fn nutze(p : ptr<user, r> u8) -> u8
///     effects { reads p } costs <= 8 ops { return p[0]; }
/// impl fn pruefe(p : ptr<user, r> u8) -> u8
///     effects { reads p } costs <= 16 ops
/// {
///     if p[0] != 0 { return nutze(p); }   -- V012: checked here, copied there
///     return 0;
/// }
/// ```
///
/// ## What counts, and what stays out by statement
///
/// * CHECK on `P` is a comparison (`BinOp::ist_vergleich`) mentioning `P`, or a
///   `narrow` on `P`. Comparisons on user pointers are validation attempts by
///   construction: there is nothing else to compare them for. Contract expressions
///   (`requires`/`ensures`) are promises, not checks, and never count.
/// * HANDOFF of `P` is a call with the bare name `P` as an argument -- the same
///   under-approximation `R008` states: a field, a local, or a return value carries no
///   declared space this pass can read.
/// * Only NAMED callees with a Gabbro body are followed. An `extern fn` is the booked
///   foreign-body gap (the boundary kill already forces a re-read after the call);
///   an indirect call (`t->f()`) or an unresolvable name is undecidable (W10: neither
///   refused nor confirmed). A callee whose receiving parameter is not itself a
///   `user`-space pointer belongs to `R008`/`M140`, and a second verdict there would
///   double-book one defect.
/// * GUARDED means re-validated or untouched: the callee checks the receiving
///   parameter before its first use of it (check and use atomic in one body, under
///   the `EinSnapshot` premise), or the callee never touches it at all (a pure
///   forward carries nothing). A check AFTER the first use, or on a different
///   parameter, guards nothing.
/// * Positions are statement-granular in one in-order walk: a check and a handoff in
///   the SAME statement never precede each other, and a comparison's own operands
///   are its check, never its use.
///
/// ## Remainder, booked not hidden
///
/// * Length companions are not tracked: a check on a `u32` length travelling beside
///   the pointer does not count as a check on the pointer. The rule sees the
///   address half of the Adressraum triple, not the length half.
/// * Overwriting the pointer between check and handoff does not silence the rule:
///   the check covered the old value, the handoff carries the new unchecked one.
fn benutzer_handoff(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
    g: &crate::aufrufgraph::Graph,
    absagen: &mut Absagen,
) {
    // First every Gabbro body, walked once: the callee side needs its own walk
    // before any handoff into it is judged.
    struct Koerper {
        modul: String,
        benutzer: Vec<(usize, String)>,
        lauf: BenutzerLauf,
    }
    let mut koerper: BTreeMap<String, Koerper> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut lauf = BenutzerLauf::default();
        let mut pos = 0usize;
        benutzer_lauf(b, &mut pos, &mut lauf);
        koerper.insert(
            crate::umgebung::qualifiziere(modul, &f.name.text),
            Koerper {
                modul: modul.to_string(),
                benutzer: benutzer_parameter(f),
                lauf,
            },
        );
    });
    for (rufer, k) in &koerper {
        for h in &k.lauf.rufe {
            // The handed name must be one of the caller's own user pointers.
            if !k.benutzer.iter().any(|(_, n)| n == &h.basis) {
                continue;
            }
            // The check must precede the handoff: a validation beside the call
            // covers no use across it.
            if !k
                .lauf
                .checks
                .iter()
                .any(|(c, p)| c == &h.basis && *p < h.pos)
            {
                continue;
            }
            let Some(ziel) = g.aufloesen(u, &k.modul, &h.ziel) else {
                continue;
            };
            let Some(gk) = koerper.get(&ziel) else {
                continue;
            };
            // The receiving parameter must be a user-space pointer too: anything
            // else is `R008`/`M140`, not this rule.
            let Some((_, qname)) = gk.benutzer.iter().find(|(i, _)| *i == h.arg) else {
                continue;
            };
            let erste_nutzung = gk
                .lauf
                .nutzungen
                .iter()
                .filter(|(n, _)| n == qname)
                .map(|(_, p)| *p)
                .min();
            let gedeckt = match erste_nutzung {
                None => true,
                Some(fu) => gk
                    .lauf
                    .checks
                    .iter()
                    .any(|(c, p)| c == qname && *p < fu),
            };
            if gedeckt {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "V012",
                    h.span,
                    format!(
                        "`{}` checks `{}` and hands it to `{}`, which uses it without \
                         revalidating",
                        crate::umgebung::kurzname(rufer),
                        h.basis,
                        crate::umgebung::kurzname(&ziel),
                    ),
                )
                .mit_notiz(
                    "a check in one body covers no use in another: the user side may \
                     rewrite the bytes between them (`PruefDannKopie`)",
                )
                .mit_notiz(
                    "check and use must be atomic (one body) or re-validated (the callee \
                     checks the same parameter before its first use)",
                )
                .mit_notiz(
                    "SYNTAX.md §16.2 item 12: the run performs no range check -- what the \
                     checker does not refuse reaches the run unchecked",
                ),
            );
        }
    }
}

/// The `user`-space pointer parameters of a function, with their positions:
/// `ptr<user, …>` is the seventh side, and only it is user memory.
fn benutzer_parameter(f: &FnDecl) -> Vec<(usize, String)> {
    f.parameter
        .iter()
        .enumerate()
        .filter_map(|(i, p)| match &p.typ {
            TypExpr::Zeiger(z) => match &z.raum {
                Raum::Benannt(n) if n.text == "user" => Some((i, p.name.text.clone())),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// One body's share of V012: where it checks, where it hands off, where it uses.
///
/// Positions are statement-granular from one in-order walk: each statement takes one
/// position, its sub-blocks follow in place. Two events in the same statement never
/// precede each other.
#[derive(Default)]
struct BenutzerLauf {
    /// `(basis, pos)`: a comparison mentioning the basis, or a `narrow` on it.
    checks: Vec<(String, usize)>,
    /// Handoffs: a bare user-pointer name as a call argument.
    rufe: Vec<BenutzerRuf>,
    /// `(basis, pos)`: every other read of the basis -- call arguments, plain
    /// places, `lenof`/`sizeof` subjects, index expressions. A comparison's own
    /// operands are its check and never a use.
    nutzungen: Vec<(String, usize)>,
}

struct BenutzerRuf {
    basis: String,
    arg: usize,
    ziel: String,
    span: Span,
    pos: usize,
}

fn benutzer_lauf(b: &Block, pos: &mut usize, w: &mut BenutzerLauf) {
    for s in &b.anweisungen {
        let p = *pos;
        *pos += 1;
        match &s.art {
            StmtArt::Narrow(n) => {
                w.checks.push((n.ort.basis.text.clone(), p));
                for e in crate::ausdruecke_im_ort(&n.ort) {
                    benutzer_expr(e, p, w);
                }
            }
            StmtArt::Ruf(r) => benutzer_ruf(r, p, w),
            StmtArt::LetSonst(l) => {
                if let Some(r) = l.als_ruf() {
                    benutzer_ruf(r, p, w);
                }
            }
            _ => {}
        }
        for e in crate::eigene_ausdruecke(s) {
            benutzer_expr(e, p, w);
        }
        for k in crate::unterbloecke(s) {
            benutzer_lauf(k, pos, w);
        }
    }
}

fn benutzer_expr(x: &Expr, p: usize, w: &mut BenutzerLauf) {
    match &x.art {
        ExprArt::Binaer(op, l, r) if op.ist_vergleich() => {
            for o in crate::alle_orte(l).iter().chain(crate::alle_orte(r).iter()) {
                w.checks.push((o.basis.text.clone(), p));
            }
            // Calls nested inside the checked expression still hand off
            // (`if f(q) != 0` passes `q` at this position) -- but an equal
            // position never precedes, so they stay silent by construction.
            for y in crate::alle_ausdruecke(x) {
                if let ExprArt::Ruf(r) = &y.art {
                    benutzer_ruf(r, p, w);
                }
            }
        }
        ExprArt::Ruf(r) => benutzer_ruf(r, p, w),
        _ => {
            match &x.art {
                ExprArt::Ort(o) | ExprArt::Alt(o) => {
                    w.nutzungen.push((o.basis.text.clone(), p));
                }
                ExprArt::Eingebaut(g) => match &**g {
                    Eingebaut::Sizeof(TypOderOrt::Ort(o))
                    | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                        w.nutzungen.push((o.basis.text.clone(), p));
                    }
                    _ => {}
                },
                _ => {}
            }
            for k in crate::unterausdruecke(x) {
                benutzer_expr(k, p, w);
            }
        }
    }
}

fn benutzer_ruf(r: &Ruf, p: usize, w: &mut BenutzerLauf) {
    // A record constructor carries no callee: its arguments are uses and checks,
    // never a handoff.
    if !r.ist_verbundwert() {
        if let CallTarget::Path(pfad) = &r.ziel {
            for (i, a) in r.argumente.iter().enumerate() {
                if let Some(o) = ort_bloss(a) {
                    w.rufe.push(BenutzerRuf {
                        basis: o.basis.text.clone(),
                        arg: i,
                        ziel: pfad.text(),
                        span: r.span,
                        pos: p,
                    });
                }
            }
        }
    }
    if let CallTarget::Place(o) = &r.ziel {
        w.nutzungen.push((o.basis.text.clone(), p));
    }
    for a in &r.argumente {
        benutzer_expr(a, p, w);
    }
}

/// A bare name under parentheses: `p`, not `p.n` and not `p[i]`. Only a bare
/// parameter name carries a declared space the rule can read -- the same
/// under-approximation `R008` states.
fn ort_bloss(e: &Expr) -> Option<&Ort> {
    match &e.art {
        ExprArt::Klammer(x) => ort_bloss(x),
        ExprArt::Ort(o) if o.suffixe.is_empty() => Some(o),
        _ => None,
    }
}
#[cfg(test)]
mod v011_tests {
    use super::*;

    /// Count V011 verdicts over a source: the unit twin of the gift probes below.
    fn v011_in(quelle: &str) -> usize {
        let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", quelle);
        pass(&baum, &mut absagen);
        absagen.absagen.iter().filter(|a| a.code == "V011").count()
    }

    const KOPF: &str = "module p { static mut n : u32 = 0; static mut m : u32 = 0;
        atomic F : bool release; atomic G : bool release;
        impl fn w(v : u32) effects { writes n, publishes F } costs <= 8 ops
        { n = v; F = true publishes { n }; }
        impl fn wg(v : u32) effects { writes m, publishes G } costs <= 8 ops
        { m = v; G = true publishes { m }; }
        impl fn rg() -> u32 effects { reads G, reads m } costs <= 8 ops
        { let g = G awaits { m }; if g { return m; } return 0; }";

    #[test]
    fn stale_use_after_publish_falls() {
        let q = format!(
            "{KOPF} impl fn r() -> u32 effects {{ reads F, reads n, writes n, publishes F }} \
             costs <= 16 ops {{ let f = F awaits {{ n }}; n = 1; F = true publishes {{ n }}; \
             if f {{ return n; }} return 0; }} }}"
        );
        assert_eq!(v011_in(&q), 1, "stale use must fall exactly once");
    }

    #[test]
    fn fresh_revalidation_stays_silent() {
        let q = format!(
            "{KOPF} impl fn r() -> u32 effects {{ reads F, reads n, writes n, publishes F }} \
             costs <= 16 ops {{ let f = F awaits {{ n }}; n = 1; F = true publishes {{ n }}; \
             let g = F awaits {{ n }}; if g {{ return n; }} return 0; }} }}"
        );
        assert_eq!(
            v011_in(&q),
            0,
            "revalidation after the publish must stay silent"
        );
    }

    #[test]
    fn other_carrier_and_prior_publish_stay_silent() {
        let q = format!(
            "{KOPF} impl fn r() -> u32 effects {{ reads F, reads n, writes m, publishes G }} \
             costs <= 16 ops {{ let f = F awaits {{ n }}; m = 1; G = true publishes {{ m }}; \
             if f {{ return n; }} return 0; }}
             impl fn s() -> u32 effects {{ reads F, reads n, writes n, publishes F }} costs <= 16 ops
             {{ n = 1; F = true publishes {{ n }}; let f = F awaits {{ n }}; \
             if f {{ return n; }} return 0; }} }}"
        );
        assert_eq!(
            v011_in(&q),
            0,
            "different carrier and publish-before-load must stay silent"
        );
    }
}

#[cfg(test)]
mod v012_tests {
    use super::*;

    /// Count V012 verdicts over a source: the unit twin of gift probes 766-768.
    /// Only this pass runs here (`pass`, not `pruefe`), so the sources below pin
    /// the V012 shape and nothing else.
    fn v012_in(quelle: &str) -> usize {
        let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", quelle);
        pass(&baum, &mut absagen);
        absagen.absagen.iter().filter(|a| a.code == "V012").count()
    }

    const NUTZE: &str = "impl fn nutze(p : ptr<user, r> u8) -> u8 effects { reads p } \
        costs <= 8 ops { return p[0]; }";
    const TREU: &str = "impl fn treu(p : ptr<user, r> u8) -> u8 effects { reads p } \
        costs <= 16 ops { if p[0] != 0 { return p[0]; } return 0; }";

    #[test]
    fn unguarded_handoff_falls_once() {
        let q = format!(
            "module p {{ {NUTZE} \
             impl fn pruefe(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 24 ops \
             {{ if p[0] != 0 {{ return nutze(p); }} return 0; }} }}"
        );
        assert_eq!(v012_in(&q), 1, "checked here, used there: must fall exactly once");
    }

    #[test]
    fn narrow_check_handoff_falls_once() {
        let q = format!(
            "module p {{ {NUTZE} \
             impl fn pruefe(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 24 ops \
             {{ narrow p[0] to 1 .. 255 else {{ return 0; }} return nutze(p); }} }}"
        );
        assert_eq!(v012_in(&q), 1, "narrow is a check too: must fall exactly once");
    }

    #[test]
    fn same_body_check_and_use_stays_silent() {
        let q = format!("module p {{ {TREU} }}");
        assert_eq!(
            v012_in(&q),
            0,
            "check and use in one body are atomic under the snapshot premise"
        );
    }

    #[test]
    fn revalidating_callee_stays_silent() {
        let q = format!(
            "module p {{ {TREU} \
             impl fn rufer(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 24 ops \
             {{ if p[0] != 0 {{ return treu(p); }} return 0; }} }}"
        );
        assert_eq!(
            v012_in(&q),
            0,
            "the callee checks the same parameter before its first use"
        );
    }

    #[test]
    fn extern_handoff_stays_silent() {
        // The booked foreign-body gap: the boundary kill forces a re-read after
        // the call, and what happens inside foreign code is exported, not checked.
        let q = format!(
            "module p {{ extern fn liest(p : ptr<user, r> u8) -> u8 effects {{ pure }} \
             costs <= 1 ops; \
             impl fn pruefe(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 16 ops \
             {{ if p[0] != 0 {{ return liest(p); }} return 0; }} }}"
        );
        assert_eq!(v012_in(&q), 0, "foreign callees are the booked gap, not a refusal");
    }

    #[test]
    fn forward_without_check_stays_silent() {
        // `beispiele/68` in miniature: no check, no check-then-use shape.
        let q = format!(
            "module p {{ {NUTZE} \
             impl fn weiter(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 16 ops \
             {{ return nutze(p); }} }}"
        );
        assert_eq!(v012_in(&q), 0, "a handoff with no check is no TOCTOU shape");
    }

    #[test]
    fn check_on_other_param_stays_open() {
        // The callee checks a DIFFERENT parameter than the one handed over:
        // still unguarded, still one verdict.
        let q = format!(
            "module p {{ \
             impl fn nutze(p : ptr<user, r> u8, n : u32) -> u8 effects {{ reads p }} \
             costs <= 8 ops {{ if n != 0 {{ return p[0]; }} return 0; }} \
             impl fn pruefe(p : ptr<user, r> u8) -> u8 effects {{ reads p }} costs <= 24 ops \
             {{ if p[0] != 0 {{ return nutze(p, 4); }} return 0; }} }}"
        );
        assert_eq!(
            v012_in(&q),
            1,
            "revalidation must cover the handed pointer, not a bystander"
        );
    }
}
