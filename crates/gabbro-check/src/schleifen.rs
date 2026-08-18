//! **Pass 6 -- M4/Schleifen, der Teil, der ohne Typen faellt.**
//!
//! `SPRACHE.md` §8.2: *„Beide zielen auf eine **benannte** Schleifenform. `break`/`continue`
//! ohne Namen gibt es nicht -- bei geschachtelten Schleifen ist das Ziel sonst Konvention statt
//! Syntax."* Der Parser nimmt `leave x;` an, weil `x` ein Bezeichner ist; **ob es eine Marke
//! gibt, kann nur dieser Pass sagen.**
//!
//! Was hier NICHT faellt und in M2 gehoert: `leaves identlist` nennt die linearen Werte, die den
//! Ausgang verlassen -- ob die Liste stimmt, entscheidet der Linearitaetspass.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

/// Was der Pass beim Absteigen mitfuehrt.
///
/// **Bis 2026-08-18 war das nur `div`.** `progress` kam dazu, weil `pruefe-klauseln.py` das
/// Feld als ungelesen ausgewiesen hat -- *gefunden von einem Werkzeug, nicht von Hand.*
struct Lage<'a> {
    /// Die Namen, die `-> never` oder `diverges` erklaeren.
    div: &'a [String],
    /// Annahme -> ist sie falsifizierbar?
    annahmen: std::collections::BTreeMap<String, bool>,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let div = divergierende(baum);
    let lg = Lage {
        div: &div,
        annahmen: crate::annahmen(baum),
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                block(b, &mut Vec::new(), &lg, absagen);
            }
        }
        ItemArt::Check(c) => block(&c.can_fail, &mut Vec::new(), &lg, absagen),
        _ => {}
    });
}

fn block(b: &Block, marken: &mut Vec<String>, lg: &Lage, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        anweisung(s, marken, lg, absagen);
    }
}

fn anweisung(s: &Stmt, marken: &mut Vec<String>, lg: &Lage, absagen: &mut Absagen) {
    match &s.art {
        StmtArt::Leave(ziel) => ziel_pruefen(ziel, marken, "leave", absagen),
        StmtArt::Next(ziel) => ziel_pruefen(ziel, marken, "next", absagen),
        StmtArt::Wenn(w) => {
            for (_, b) in &w.zweige {
                block(b, marken, lg, absagen);
            }
            if let Some(b) = &w.sonst {
                block(b, marken, lg, absagen);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                block(&z.rumpf, marken, lg, absagen);
            }
        }
        StmtArt::Bricht(b) => block(&b.rumpf, marken, lg, absagen),
        StmtArt::Narrow(n) => block(&n.sonst, marken, lg, absagen),
        StmtArt::Sperrt(l) => block(&l.rumpf, marken, lg, absagen),
        StmtArt::Observiert(o) => block(&o.rumpf, marken, lg, absagen),
        StmtArt::LetSonst(l) => {
            // **U7.** `SYNTAX.md` §7: *„der `else`-Zweig muss divergieren oder
            // zurueckkehren"*. Faellt er durch, ist `let … else` genau der verborgene
            // Kontrollfluss, gegen den es geschrieben wurde -- der Name waere danach
            // gebunden, ohne dass je ein Wert entstand.
            if !endet_immer(&l.sonst, lg.div) {
                absagen.schiebe(
                    Absage::fehler(
                        "S002",
                        l.sonst.span,
                        format!(
                            "the `else` branch of `let {} = …` falls through",
                            l.name.text
                        ),
                    )
                    .mit_notiz(
                        "SYNTAX.md §7: die einzige Fehlerfortpflanzung ist `let … else (e) \
                         { … }`, und ihr Zweig muss divergieren oder zurueckkehren",
                    ),
                );
            }
            block(&l.sonst, marken, lg, absagen);
        }
        StmtArt::Exchange(e) => {
            if let XForm::Update { rumpf, .. } = &e.form {
                block(rumpf, marken, lg, absagen);
            }
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            // `traverse` traegt keine Marke -- die Grammatik gibt ihr keine Stelle dafuer.
            Schleife::Traverse(t) => block(&t.rumpf, marken, lg, absagen),
            Schleife::Retry(r) => {
                fortschritt_pruefen(r.fortschritt.as_ref(), lg, absagen);
                mit_marke(r.marke.as_ref(), &r.rumpf, marken, lg, absagen);
            }
            Schleife::Forever(f) => {
                fortschritt_pruefen(f.fortschritt.as_ref(), lg, absagen);
                mit_marke(f.marke.as_ref(), &f.rumpf, marken, lg, absagen);
            }
        },
        _ => {}
    }
}

fn mit_marke(
    marke: Option<&Ident>,
    rumpf: &Block,
    marken: &mut Vec<String>,
    lg: &Lage,
    absagen: &mut Absagen,
) {
    if let Some(m) = marke {
        marken.push(m.text.clone());
        block(rumpf, marken, lg, absagen);
        marken.pop();
    } else {
        block(rumpf, marken, lg, absagen);
    }
}

/// Verlaesst dieser Block seinen Weg immer? Syntaktisch, ohne Fixpunkt -- dieselbe Frage,
/// die M1 fuer die V1-Verneinung stellt.
///
/// **Wer divergiert, endet auch.** Ein Block, der auf `exit();` endet, faellt nicht durch --
/// wenn `exit` als `-> never` oder mit `diverges` erklaert ist.
///
/// Bis 2026-08-15 sah `endet_immer` nur `return`/`leave`/`next` und hielt jeden Aufruf fuer
/// eine gewoehnliche Anweisung. **Sieben `S002` im Fragmentkorpus kamen allein daher** --
/// jeder Fehlerzweig eines `let … else`, der mit einem Abbruch endet, galt als
/// durchfallend. Der Pass war zu streng, und zwar an der Stelle, an der ein Kernel seine
/// Fehlerbehandlung schreibt.
///
/// *Gefunden am Fragmentlauf, wie schon der `E005`-Fehler. Die Fragmente sind das einzige
/// Werkzeug im Ordner, das den Pruefer gegen ECHTEN Code haelt statt gegen Beispiele, die
/// ich selbst geschrieben habe.*
fn divergierende(baum: &Programm) -> Vec<String> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            let nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
            let div = f.klasse == Some(FnKlasse::Divergent)
                || f.effects.as_ref().is_some_and(|w| {
                    w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert))
                });
            if nie || div {
                aus.push(f.name.text.clone());
            }
        }
    });
    aus
}

fn endet_immer(b: &Block, div: &[String]) -> bool {
    let Some(letzte) = b.anweisungen.last() else {
        return false;
    };
    match &letzte.art {
        StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
        StmtArt::Ruf(r) => r
            .pfad
            .teile
            .last()
            .is_some_and(|n| div.iter().any(|d| d == &n.text)),
        StmtArt::Wenn(w) => {
            w.sonst.as_ref().is_some_and(|r| endet_immer(r, div))
                && w.zweige.iter().all(|(_, r)| endet_immer(r, div))
        }
        StmtArt::Match(m) => m.zweige.iter().all(|z| endet_immer(&z.rumpf, div)),
        _ => false,
    }
}

fn ziel_pruefen(ziel: &Ident, marken: &[String], wort: &str, absagen: &mut Absagen) {
    if marken.iter().any(|m| m == &ziel.text) {
        return;
    }
    let mut a = Absage::fehler(
        "S001",
        ziel.span,
        format!(
            "`{wort} {}` targets no enclosing loop label",
            ziel.text
        ),
    )
    .mit_notiz(
        "SPRACHE.md §8.2: `break`/`continue` ohne Namen gibt es nicht -- \
         bei geschachtelten Schleifen waere das Ziel sonst Konvention statt Syntax",
    );
    if marken.is_empty() {
        a = a.mit_notiz("no label is in scope here; `retry`/`forever` take one");
    } else {
        a = a.mit_notiz(format!("im Geltungsbereich: {}", marken.join(", ")));
    }
    absagen.schiebe(a);
}

/// **`progress` hatte bis 2026-08-18 keinen Leser** -- ausgewiesen von `pruefe-klauseln.py`.
///
/// **Was hier NICHT geprueft wird, ist Lebendigkeit.** D8 sagt es und behaelt recht:
/// *„`progress` nennt Annahmen, beweist keine Lebendigkeit. Kein Konstrukt behauptet eine."*
/// Ein Pass, der hier mehr verspraeche, waere genau die Sorte Zusage, gegen die dieser Ordner
/// gebaut ist.
///
/// **Geprueft wird, was die Sprache verspricht**, nicht mehr: `progress` nennt WER die
/// Schleife beendet, und zwar als **Annahme mit Falsifikator** (`SYNTAX.md` §8.3: *„The
/// watchdog IS the falsifier"*). Zwei Weisen, wie dieses Versprechen leer sein kann:
///
/// ```text
/// S003   der Name gehoert keiner Annahme -- die Schleife ruht auf einem Wort,
///        das niemand aufgeschrieben hat, und im Zeugnis steht es nirgends
/// S004   die Annahme ist `unfalsifiable` -- dann endet die Schleife, weil es
///        dasteht, und keine Sonde kann je widersprechen
/// ```
///
/// *Eine unfalsifizierbare Fortschrittsannahme nimmt dem Wachhund seinen Gegenstand.*
fn fortschritt_pruefen(zeuge: Option<&Ident>, lg: &Lage, absagen: &mut Absagen) {
    let Some(z) = zeuge else { return };
    match lg.annahmen.get(&z.text) {
        None => absagen.schiebe(
            Absage::fehler(
                "S003",
                z.span,
                format!("`progress {}` names no declared assumption", z.text),
            )
            .mit_notiz(
                "SYNTAX.md §8.3: `progress` nennt WER die Schleife beendet -- eine Annahme \
                 ueber die Umgebung. Ohne `assume`/`axiom` steht der Name in keinem Manifest \
                 und kommt in kein Zeugnis",
            ),
        ),
        Some(false) => absagen.schiebe(
            Absage::fehler(
                "S004",
                z.span,
                format!("`progress {}` rests on an unfalsifiable assumption", z.text),
            )
            .mit_notiz(
                "der Wachhund IST der Falsifikator (`on_exceeded`); eine Annahme, der keine \
                 Sonde je widersprechen kann, beendet die Schleife nur auf dem Papier",
            ),
        ),
        Some(true) => {}
    }
}
