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

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let div = divergierende(baum);
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                block(b, &mut Vec::new(), &div, absagen);
            }
        }
        ItemArt::Check(c) => block(&c.can_fail, &mut Vec::new(), &div, absagen),
        _ => {}
    });
}

fn block(b: &Block, marken: &mut Vec<String>, div: &[String], absagen: &mut Absagen) {
    for s in &b.anweisungen {
        anweisung(s, marken, div, absagen);
    }
}

fn anweisung(s: &Stmt, marken: &mut Vec<String>, div: &[String], absagen: &mut Absagen) {
    match &s.art {
        StmtArt::Leave(ziel) => ziel_pruefen(ziel, marken, "leave", absagen),
        StmtArt::Next(ziel) => ziel_pruefen(ziel, marken, "next", absagen),
        StmtArt::Wenn(w) => {
            for (_, b) in &w.zweige {
                block(b, marken, div, absagen);
            }
            if let Some(b) = &w.sonst {
                block(b, marken, div, absagen);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                block(&z.rumpf, marken, div, absagen);
            }
        }
        StmtArt::Bricht(b) => block(&b.rumpf, marken, div, absagen),
        StmtArt::Narrow(n) => block(&n.sonst, marken, div, absagen),
        StmtArt::Sperrt(l) => block(&l.rumpf, marken, div, absagen),
        StmtArt::LetSonst(l) => {
            // **U7.** `SYNTAX.md` §7: *„der `else`-Zweig muss divergieren oder
            // zurueckkehren"*. Faellt er durch, ist `let … else` genau der verborgene
            // Kontrollfluss, gegen den es geschrieben wurde -- der Name waere danach
            // gebunden, ohne dass je ein Wert entstand.
            if !endet_immer(&l.sonst, div) {
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
            block(&l.sonst, marken, div, absagen);
        }
        StmtArt::Exchange(e) => {
            if let XForm::Update { rumpf, .. } = &e.form {
                block(rumpf, marken, div, absagen);
            }
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            // `traverse` traegt keine Marke -- die Grammatik gibt ihr keine Stelle dafuer.
            Schleife::Traverse(t) => block(&t.rumpf, marken, div, absagen),
            Schleife::Retry(r) => {
                mit_marke(r.marke.as_ref(), &r.rumpf, marken, div, absagen);
            }
            Schleife::Forever(f) => {
                mit_marke(f.marke.as_ref(), &f.rumpf, marken, div, absagen);
            }
        },
        _ => {}
    }
}

fn mit_marke(
    marke: Option<&Ident>,
    rumpf: &Block,
    marken: &mut Vec<String>,
    div: &[String],
    absagen: &mut Absagen,
) {
    if let Some(m) = marke {
        marken.push(m.text.clone());
        block(rumpf, marken, div, absagen);
        marken.pop();
    } else {
        block(rumpf, marken, div, absagen);
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
