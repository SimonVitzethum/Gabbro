//! **«K5.3» -- die Ausführungskontexte, und was sie einander verbieten.**
//!
//! `H013` nahm seit dem 2026-08-19 die **grobe** Antwort: *jeder `entry` ist ein Kontext, und
//! ein Platz, den einer davon schreibt, ist geteilt.* Grob in die sichere Richtung — aber zu
//! grob an drei Stellen, und alle drei stehen längst in der Grammatik:
//!
//! | Form | was sie sagt |
//! |---|---|
//! | `masks IRQ` | schliesst den Interruptkontext aus |
//! | `nested never` | der Eintritt unterbricht sich nicht selbst |
//! | `per cpu` | gehört genau einem Kern |
//!
//! ## Die Zeile, die ehrlich bleiben muss
//!
//! **Auf mehr als einem Kern schliesst `masks IRQ` gar nichts aus.** Ein zweiter Kern läuft
//! weiter, gleichgültig wie die Interruptmaske dieses Kerns steht. Die Ausnahmen dieser Matrix
//! gelten also **nur unter einer Annahme**, und die muss dastehen:
//!
//! ```gabbro
//! assume ein_kern "Dieser Kern läuft auf genau einem Prozessor."
//!     falsifier sonde_zweiter_kern;
//! ```
//!
//! **Ohne diese Zeile wird nichts ausgenommen** — `H013` bleibt, was es war. *Das ist der
//! Unterschied zwischen einer Lockerung, die man sieht, und einer, die der Prüfer sich selbst
//! erlaubt:* die Annahme steht im Zeugnis, unter „bewiesen unter A1…An", und ihr Falsifikator
//! ist eine Probe, die auf zwei Kernen bootet.
//!
//! > **Und darum ist `ein_kern` falsifizierbar und A10 nicht.** Ein zweiter Kern ist eine
//! > Tatsache, die man herstellen kann; eine Umordnung im Speichermodell ist es nicht.
//!
//! ## «B38» — die Nebenbedingung am benannten Traeger (`H101`, 2026-08-21)
//!
//! `FRAGMENTE.md` F8 misst fuenf Werte, die im Planer eine Sperrgrenze ueberqueren. **Drei
//! tragen das Muster „die Fortsetzung prueft neu"; zwei nicht** — sie ruhen auf der
//! Interruptmaskierung, und das ist der heisseste Pfad (`exit_current`, die IPC-Uebergabe).
//! Die ehrliche Form heisst darum nicht *„jede Fortsetzung prueft neu"*, sondern
//!
//! > *„jede Fortsetzung prueft neu **oder nennt, was sie stattdessen traegt** — und ein
//! > Traeger `masks IRQ` zaehlt nur, wenn der Eintrittskontext `nested masked` traegt."*
//!
//! **Warum die zweite Haelfte nicht schmueckend ist, gemessen am 2026-08-21:**
//!
//! ```text
//! $ gabbro pruefe probe-schlupfloch.gab   # masks IRQ + assume ein_kern, entry nested never
//!   5 Items, 0 Fehler
//! $ gabbro pruefe probe-ohne-masks.gab    # dieselbe Datei OHNE masks IRQ
//!   [H013] this entry writes `z`, and nothing declares it shared
//! ```
//!
//! *Ein Wort in der Wirkungsliste kaufte die Ausnahme von `H013`* — ohne jede Kopplung an
//! den Zustand, in dem der Weg laeuft. **Genau die Zusicherung aus R15: erfuellt, sobald der
//! Pruefer schweigt.** `H101` schliesst das: wer den Traeger nennt, schreibt den Zustand an
//! den Eintritt.
//!
//! **Und `nested never` ist NICHT dasselbe.** `never` sagt, dass der Vektor sich nicht selbst
//! wieder betritt; `masked` sagt, in welchem Zustand er laeuft. *Ueber eine Sperrgrenze traegt
//! der Zustand, nicht die Abwesenheit von Wiedereintritt.* Dieselbe Schnittkante wie bei
//! `H005`: dort entscheidet die STAERKE des Zeugen, hier der ZUSTAND am Eintritt — beide Male
//! genuegt das blosse Nennen nicht.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

/// Ein Ausführungskontext — heute ist das genau ein `entry`.
pub struct Kontext {
    pub name: String,
    /// `dispatch` — die Wurzel, von der aus die Wirkungen zählen.
    pub wurzel: String,
    pub modul: String,
    /// `nested never` — der Eintritt unterbricht sich selbst nicht.
    pub nie_verschachtelt: bool,
    /// `nested masked` — der Eintritt LAEUFT mit maskierten Interrupts.
    ///
    /// **Das ist eine andere Aussage als `nested never`**, und «B38» haengt an dem
    /// Unterschied: `never` sagt, dass dieser Vektor sich nicht selbst wieder betritt;
    /// `masked` sagt, in welchem ZUSTAND der Weg laeuft. *Nur der Zustand traegt einen Wert
    /// ueber eine Sperrgrenze.*
    pub maskiert_verschachtelt: bool,
    /// Ein Eintritt über die IDT ist ein Interruptkontext; er kann preemptieren.
    pub unterbricht: bool,
    pub span: gabbro_syntax::span::Span,
}

pub fn erhebe(baum: &Programm) -> Vec<Kontext> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Entry(e) = &item.art {
            aus.push(Kontext {
                name: e.name.text.clone(),
                wurzel: e.dispatch.text(),
                modul: modul.to_string(),
                nie_verschachtelt: matches!(e.verschachtelt, Some(Verschachtelt::Nie)),
                maskiert_verschachtelt: matches!(
                    e.verschachtelt,
                    Some(Verschachtelt::Maskiert)
                ),
                // **Was einen Eintritt zum Interruptkontext macht**, syntaktisch: er kommt
                // über die IDT. *Ein Syscall auch — aber der wird gerufen, nicht geworfen,
                // und er preemptiert niemanden.* `via` ist die einzige Stelle, an der die
                // Sprache den Unterschied heute ausspricht.
                unterbricht: e.via.as_ref().is_some_and(|v| v.text == "idt"),
                span: e.name.span,
            });
        }
    });
    aus
}

/// **Läuft unter der Annahme `ein_kern` überhaupt noch etwas gleichzeitig?**
///
/// Die Antwort ist eine Aussage über den ZUGRIFF, nicht über den Kontext: greift jeder
/// schreibende Weg mit maskierten Interrupts zu, kann ihn auf einem Kern nichts unterbrechen.
/// **Und seit «B38» steht `H101` DAVOR.** Diese Zeile nimmt `masks …` weiterhin als
/// Ausschluss — aber ein Eintritt, der einen `masks`-Traeger erreicht und **kein**
/// `nested masked` traegt, wird von `H101` schon abgesagt. Die Ausnahme ist damit nicht mehr
/// kaeuflich: *wer sie nimmt, hat den Zustand am Eintritt hingeschrieben.*
///
/// ## Und `nested masked` fehlte hier — gefunden 2026-08-21 beim Bau von `H101`
///
/// `matches!(e.verschachtelt, Some(Verschachtelt::Nie))` war die einzige Stelle, die
/// `entryextra` je gelesen hat; `Maskiert` und `Begrenzt` kannte ausser dem Erzeuger niemand.
/// **Die Folge war ein Widerspruch:** `nested never` bekam die Ausnahme, `nested masked`
/// nicht — obwohl `masked` genau die Praemisse der Ausnahme AUSSPRICHT und `never` sie nur
/// nahelegt.
///
/// > *Eine Regel, deren Abhilfe eine andere Regel ausloest, ist keine Abhilfe.* Ohne diese
/// > Zeile haette `H101` verlangt, `nested masked` zu schreiben — und `H013` waere daraufhin
/// > NEU gefallen. Gemessen am 2026-08-21 an `probe-gedeckt.gab`: erst `[H013]`, nach der
/// > Zeile 0 Fehler.
pub fn ein_kern_deckt(maskiert: bool, k: &Kontext) -> bool {
    // Maskiert schliesst jeden Interruptkontext aus; `nested never` den Eintritt selbst,
    // und `nested masked` sagt denselben Ausschluss am Eintritt statt am Weg.
    maskiert && (k.nie_verschachtelt || k.maskiert_verschachtelt || !k.unterbricht)
}

/// **Die Lage am benannten Traeger — die Zahlen, die neben dem Urteil stehen.**
///
/// Ohne sie weiss niemand, ob `H101` eine Luecke schliesst oder den Korpus zerlegt; und ohne
/// `unerreicht` liest sich ein stiller Lauf wie ein bestandener (W10).
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Traegerlage {
    /// Ausfuehrungskontexte insgesamt.
    pub kontexte: usize,
    /// Kontexte, deren Huelle mindestens einen `masks …`-Traeger nennt.
    pub mit_traeger: usize,
    /// davon: der Eintritt traegt `nested masked` — der Traeger haelt.
    pub gedeckt: usize,
    /// davon: er traegt es nicht — hier faellt `H101`.
    pub ungedeckt: usize,
    /// Kontexte, deren Huelle unvollstaendig ist (Zyklus oder unbekannter Gerufener).
    /// **Ueber einer unteren Schranke wird nicht abgesagt** (R16).
    pub unentscheidbar: usize,
    /// Funktionen, die `masks …` DEKLARIEREN — der Nenner.
    pub traeger_erklaert: usize,
    /// davon: von keinem sichtbaren Kontext erreicht. **Diese sind nicht freigesprochen,
    /// sondern ungesehen** — in einer Uebersetzungseinheit ohne `entry` fragt niemand.
    pub traeger_unerreicht: usize,
    /// **«B39» -- the numbers next to `H102`.** Locks declared in this unit.
    pub sperren: usize,
    /// of those: they carry `masks irqs`, so taking them masks interrupts.
    pub sperren_maskiert: usize,
    /// Contexts that a piece of hardware THROWS -- `via idt`. Only these can arrive
    /// between two instructions of a path that is holding a lock.
    pub irq_kontexte: usize,
    /// of those: they reach a `locks L` whose `L` masks nothing -- here `H102` falls.
    pub irq_nimmt_unmaskiert: usize,
}

/// **Welche Knoten erreicht dieser Kontext?** Eine eigene kleine Wanderung, weil der Graph
/// die HUELLE der Wirkungen liefert und nicht die Menge der Namen.
///
/// Der Weg endet an einem Namen, den der Graph nicht kennt — das ist genau die Stelle, an
/// der `Huelle::unvollstaendig` steht, und darum wird die Zahl daneben mitgefuehrt statt
/// stillschweigend fuer vollstaendig gehalten.
fn erreichbare(g: &crate::aufrufgraph::Graph, start: &str) -> Vec<String> {
    let mut gesehen: Vec<String> = Vec::new();
    let mut offen = vec![start.to_string()];
    while let Some(n) = offen.pop() {
        if gesehen.contains(&n) {
            continue;
        }
        let Some(k) = g.knoten.get(&n) else {
            gesehen.push(n);
            continue;
        };
        for (ziel, _) in &k.rufe {
            offen.push(ziel.clone());
        }
        gesehen.push(n);
    }
    gesehen
}

/// Nennt diese Funktion einen Traeger `masks …` in ihrer Wirkungsliste?
fn erklaert_traeger(f: &FnDecl) -> bool {
    f.effects.as_ref().is_some_and(|w| {
        w.liste
            .iter()
            .any(|x| matches!(x.art, WirkungArt::Maskiert(_)))
    })
}

/// **«B38» — die Nebenbedingung am benannten Traeger, gerechnet.**
///
/// Liefert die Zahlen und die Absagen in einem Durchgang, damit `pass` und `zeige` nicht
/// zwei verschiedene Antworten geben koennen. *Zwei Register ueber derselben Sache sind W7.*
fn erhebe_lage(baum: &Programm) -> (Traegerlage, Vec<Absage>) {
    let mut lage = Traegerlage::default();
    let mut absagen = Vec::new();

    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let kontexte = erhebe(baum);
    lage.kontexte = kontexte.len();

    // Welche erklaerten Traeger erreicht ueberhaupt ein Kontext? Der Schluessel ist der
    // QUALIFIZIERTE Name -- zwei gleichnamige Funktionen in zwei Modulen sind zwei Knoten
    // (derselbe Fehler, den `140-gleicher-name-fremdes-modul.gab` festhaelt).
    // **«B39» -- the lock table, and it is the half `kontexte.rs` never had.**
    //
    // `LockDecl::maskiert` is filled by the reader and, until 2026-08-31, read by nobody:
    // `pruefe-klauseln.py` carried `maskiert / LockDecl` under **UNGELESEN** -- *"the reader
    // fills it, nobody looks"*. The other half stood right here: `EntryDecl::dispatch` has
    // been the root of this file since «K5.3».
    //
    // > *Both parts existed and were correct; what was missing was the line that brings
    // > them together.* Exactly the class `zaehle-verdrahtung.py` counts -- and `Entry/Lock`
    // > was one of its 32 open pairs on the day this was written.
    let mut sperren: Vec<(String, bool)> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            sperren.push((l.name.text.clone(), l.maskiert.is_some()));
        }
    });
    lage.sperren = sperren.len();
    lage.sperren_maskiert = sperren.iter().filter(|(_, m)| *m).count();
    lage.irq_kontexte = kontexte.iter().filter(|k| k.unterbricht).count();

    let mut erklaert: Vec<String> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            if erklaert_traeger(f) {
                erklaert.push(crate::umgebung::qualifiziere(modul, &f.name.text));
            }
        }
    });
    lage.traeger_erklaert = erklaert.len();
    let mut erreicht: Vec<String> = Vec::new();

    for k in &kontexte {
        let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) else {
            continue;
        };
        // **Der Nenner zuerst, und fuer JEDEN Kontext.** Wer ihn erst hinter der
        // Traegerfrage erhoebe, zaehlte einen Traeger als „unerreicht", den ein Kontext sehr
        // wohl erreicht -- naemlich dann, wenn die Huelle an einer unbekannten Kante abbricht
        // und die Wirkung darum gar nicht ankommt.
        for n in erreichbare(&g, &voll) {
            if erklaert.contains(&n) && !erreicht.contains(&n) {
                erreicht.push(n);
            }
        }
        let h = g.huelle(&voll);

        // **`H102` -- a handler takes no lock that leaves interrupts unmasked.**
        //
        // `nested never` says this vector does not re-enter ITSELF. It says nothing about a
        // path that was INTERRUPTED while holding a lock. If the handler then takes that
        // same lock, it waits for a holder who only resumes once the handler returns --
        // **on one core that is the standstill, and no loop is spinning in it.**
        //
        // Linux writes `spin_lock_irqsave` for this, and `lock … masks irqs` IS that word.
        // Measured before the build (`beispiele/gift/460`): **0 errors.**
        //
        // ## Why the trigger is `via idt` and not `vector`
        //
        // `Kontext::unterbricht` is the tree's OWN answer to "what makes an entry an
        // interrupt context", and it has a reason written next to it: a syscall carries a
        // vector too, but it is CALLED, not thrown. Asking the question a second time here,
        // with a second answer, would be a fourth register over the same set (W7) -- the
        // very form this rule was built out of. *So it reuses the answer instead.*
        //
        // **And that leaves a gap this rule does not close, named rather than hidden:**
        // `beispiele/57`'s `halt_ipi vector 0xF0` is an IPI and therefore thrown, but it
        // writes no `via idt` -- so `unterbricht` is false and `H102` stays silent over it.
        // *That is a gap in the LANGUAGE (`via` is the only place it says the difference),
        // not a gap in this rule.*
        //
        // ## It fires on PRESENCE, so an incomplete hull is no excuse
        //
        // The same argument `H101` carries one screen up: the effect set only GROWS, so a
        // `locks L` in a lower bound stands in the full hull too (R16 forbids refusing on
        // ABSENCE, and this is not one). *The reverse -- a lock hidden behind a cut edge --
        // is possible, and that is why `unentscheidbar` keeps being counted.*
        if k.unterbricht {
            for w in &h.wirkungen {
                let Some(ort) = w
                    .strip_prefix("locks shared ")
                    .or_else(|| w.strip_prefix("locks "))
                else {
                    continue;
                };
                // The last segment: `locks a::b::L` and `lock L` are the same lock.
                let kurz = ort.rsplit("::").next().unwrap_or(ort);
                // **A lock this unit does not declare is not refused.** We would be
                // guessing at its `masks` clause, and a guess in the refusing direction is
                // exactly what R16 forbids.
                let Some((_, maskiert)) = sperren.iter().find(|(n, _)| n == kurz) else {
                    continue;
                };
                if *maskiert {
                    continue;
                }
                lage.irq_nimmt_unmaskiert += 1;
                absagen.push(
                    Absage::fehler(
                        "H102",
                        k.span,
                        format!(
                            "`{}` is thrown by hardware and takes `{kurz}`, which does not \
                             declare `masks irqs`",
                            k.name
                        ),
                    )
                    .mit_notiz(&format!(
                        "an interrupted path may be holding `{kurz}` -- the handler then \
                         waits for a holder that only resumes once the handler returns"
                    ))
                    .mit_notiz(
                        "the remedy is one word at the DECLARATION: `lock … masks irqs`, \
                         the same statement `spin_lock_irqsave` makes",
                    )
                    .mit_notiz(
                        "`nested never` is not this promise -- it says the vector does not \
                         re-enter itself, and says nothing about the path it interrupted",
                    ),
                );
            }
        }

        let traeger: Vec<&String> = h
            .wirkungen
            .iter()
            .filter(|w| w.starts_with("masks "))
            .collect();
        // **Und ueber einer unvollstaendigen Huelle wird hier sehr wohl abgesagt** -- anders
        // als bei `H013`, und mit Grund: `H013` loest auf ABWESENHEIT aus (nichts erklaert
        // den Platz geteilt), und eine untere Schranke darf keine Abwesenheit belegen (R16).
        // `H101` loest auf ANWESENHEIT aus. Die Wirkungsmenge waechst nur; was in einer
        // unteren Schranke steht, steht auch in der vollen. *Die Zahl bleibt trotzdem
        // daneben stehen, weil die Gegenrichtung -- ein Traeger, den die abgeschnittene
        // Kante verbirgt -- sehr wohl moeglich ist.*
        if h.unvollstaendig.is_some() {
            lage.unentscheidbar += 1;
        }
        if traeger.is_empty() {
            continue;
        }
        lage.mit_traeger += 1;
        if k.maskiert_verschachtelt {
            lage.gedeckt += 1;
            continue;
        }
        lage.ungedeckt += 1;
        let namen: Vec<&str> = traeger.iter().map(|s| s.as_str()).collect();
        absagen.push(
            Absage::fehler(
                "H101",
                k.span,
                format!(
                    "`{}` reaches a carrier `{}` but does not declare `nested masked`",
                    k.name,
                    namen.join("`, `")
                ),
            )
            .mit_notiz(
                "`masks IRQ` in an effect list says that the function MASKS -- not that \
                 it RUNS masked; only the entry context states the latter, and `entrydecl` \
                 has the word for it",
            )
            .mit_notiz(
                "either write `nested masked` at this entry, or let the continuation \
                 re-check instead of naming a carrier",
            )
            .mit_notiz(
                "`nested never` is NOT this promise -- it says the vector does not \
                 re-enter itself, and a value across a lock boundary is carried by the \
                 STATE, not by the absence of re-entry",
            ),
        );
    }
    lage.traeger_unerreicht = lage.traeger_erklaert.saturating_sub(erreicht.len());
    (lage, absagen)
}

/// Die Zahlen allein — fuer Berichte und Proben.
pub fn lage(baum: &Programm) -> Traegerlage {
    erhebe_lage(baum).0
}

/// **Der Pass: «B38», die Kopplung zwischen Traeger und Eintrittszustand.**
///
/// Er laeuft in der Familie von Pass 12 (Sperren) und bekommt darum keine eigene Nummer;
/// die Regel gehoert zur Kontextmatrix, nicht zu einer neuen Spalte.
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    for a in erhebe_lage(baum).1 {
        absagen.schiebe(a);
    }
}

/// **`gabbro kontexte` — je Platz die Kontextmenge, und daneben die ZAHL.**
///
/// Der Bericht steht in `PLAN.md` als Tor, und der Grund ist W1: *ohne die Zahl der berührten
/// Plätze sieht ein leerer Lauf aus wie ein bestandener.* Auf diesem Korpus ist er leer, weil
/// alle vier `dispatch`-Ziele `extern fn` sind — **und genau das soll man sehen.**
pub fn zeige(baum: &Programm, datei: &str) -> String {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let kontexte = erhebe(baum);
    let annahmen = crate::annahmen(baum);
    let ein_kern = annahmen.contains_key("ein_kern");

    let mut aus = format!("# {datei}\n\n");
    aus.push_str(&format!(
        "contexts: {}   ·   assumption `ein_kern`: {}\n\n",
        kontexte.len(),
        if ein_kern {
            "YES -- the matrix grants exemptions"
        } else {
            "no -- nothing is exempt"
        }
    ));
    // **«B38» -- die Traegerzeile, und sie steht VOR dem Abbruch bei null Kontexten.**
    //
    // Genau dort ist sie am wichtigsten: eine Uebersetzungseinheit ohne `entry` hat erklaerte
    // Traeger und keinen einzigen Kontext, der sie prueft. *Wer die Zeile hinter den Abbruch
    // legte, druckte die Zahl nie, wenn sie etwas heisst.*
    let l = lage(baum);
    aus.push_str(&format!(
        "carriers `masks …` declared: {}   ·   reached by a context: {}   ·   \
         backed by `nested masked`: {}   ·   UNBACKED (H101): {}   ·   \
         contexts with an incomplete hull: {}\n\n",
        l.traeger_erklaert,
        l.traeger_erklaert - l.traeger_unerreicht,
        l.gedeckt,
        l.ungedeckt,
        l.unentscheidbar
    ));
    if l.traeger_unerreicht > 0 {
        aus.push_str(&format!(
            "  **{} declared carrier(s) are reached by NO visible context.** They are not \n\
             \x20 cleared, they are unseen -- in a unit without an `entry` nobody asks (W10).\n\n",
            l.traeger_unerreicht
        ));
    }
    if kontexte.is_empty() {
        aus.push_str("  (no `entry` -- without a context root the question is not asked)\n");
        return aus;
    }

    let mut zeilen: Vec<String> = Vec::new();
    let mut plaetze = 0usize;
    let mut ohne_rumpf = 0usize;
    for k in &kontexte {
        let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) else {
            ohne_rumpf += 1;
            zeilen.push(format!("  {:<16} {} -- unknown", k.name, k.wurzel));
            continue;
        };
        let h = g.huelle(&voll);
        if let Some(grund) = &h.unvollstaendig {
            ohne_rumpf += 1;
            zeilen.push(format!("  {:<16} {} -- incomplete: {grund}", k.name, k.wurzel));
            continue;
        }
        let maskiert = h.wirkungen.iter().any(|w| w.starts_with("masks "));
        let geschrieben: Vec<&str> = h
            .wirkungen
            .iter()
            .filter_map(|w| w.strip_prefix("writes "))
            .collect();
        plaetze += geschrieben.len();
        zeilen.push(format!(
            "  {:<16} {:<32} writes {:>3}{}{}{}",
            k.name,
            k.wurzel,
            geschrieben.len(),
            if maskiert { "  masks" } else { "" },
            if k.maskiert_verschachtelt { "  nested-masked" } else { "" },
            if k.nie_verschachtelt { "  nested-never" } else { "" },
        ));
        for p in geschrieben {
            zeilen.push(format!("      {p}"));
        }
    }
    aus.push_str(&zeilen.join("\n"));
    aus.push('\n');
    // **Die Zahl daneben, und sie ist der Zweck des Berichts.**
    aus.push_str(&format!(
        "\nplaces touched: {plaetze}   ·   context roots with no visible body: {ohne_rumpf} of {}\n",
        kontexte.len()
    ));
    if plaetze == 0 {
        aus.push_str(
            "\n  **ZERO BITE.** No context reaches a place Gabbro can see -- the rule\n\
             \x20 `H013` does not fall here a single time. *An empty run is not a passed\n\
             \x20 one* (W1).\n",
        );
    }
    aus
}
