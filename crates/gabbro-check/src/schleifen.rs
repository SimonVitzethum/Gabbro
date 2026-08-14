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
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                block(b, &mut Vec::new(), absagen);
            }
        }
        ItemArt::Check(c) => block(&c.can_fail, &mut Vec::new(), absagen),
        _ => {}
    });
}

fn block(b: &Block, marken: &mut Vec<String>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        anweisung(s, marken, absagen);
    }
}

fn anweisung(s: &Stmt, marken: &mut Vec<String>, absagen: &mut Absagen) {
    match &s.art {
        StmtArt::Leave(ziel) => ziel_pruefen(ziel, marken, "leave", absagen),
        StmtArt::Next(ziel) => ziel_pruefen(ziel, marken, "next", absagen),
        StmtArt::Wenn(w) => {
            for (_, b) in &w.zweige {
                block(b, marken, absagen);
            }
            if let Some(b) = &w.sonst {
                block(b, marken, absagen);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                block(&z.rumpf, marken, absagen);
            }
        }
        StmtArt::Bricht(b) => block(&b.rumpf, marken, absagen),
        StmtArt::Narrow(n) => block(&n.sonst, marken, absagen),
        StmtArt::Sperrt(l) => block(&l.rumpf, marken, absagen),
        StmtArt::LetSonst(l) => block(&l.sonst, marken, absagen),
        StmtArt::Exchange(e) => {
            if let XForm::Update { rumpf, .. } = &e.form {
                block(rumpf, marken, absagen);
            }
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            // `traverse` traegt keine Marke -- die Grammatik gibt ihr keine Stelle dafuer.
            Schleife::Traverse(t) => block(&t.rumpf, marken, absagen),
            Schleife::Retry(r) => {
                mit_marke(r.marke.as_ref(), &r.rumpf, marken, absagen);
            }
            Schleife::Forever(f) => {
                mit_marke(f.marke.as_ref(), &f.rumpf, marken, absagen);
            }
        },
        _ => {}
    }
}

fn mit_marke(marke: Option<&Ident>, rumpf: &Block, marken: &mut Vec<String>, absagen: &mut Absagen) {
    if let Some(m) = marke {
        marken.push(m.text.clone());
        block(rumpf, marken, absagen);
        marken.pop();
    } else {
        block(rumpf, marken, absagen);
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
            "`{wort} {}` zielt auf keine umgebende Schleifenmarke",
            ziel.text
        ),
    )
    .mit_notiz(
        "SPRACHE.md §8.2: `break`/`continue` ohne Namen gibt es nicht -- \
         bei geschachtelten Schleifen waere das Ziel sonst Konvention statt Syntax",
    );
    if marken.is_empty() {
        a = a.mit_notiz("hier ist keine Marke im Geltungsbereich; `retry`/`forever` nehmen eine");
    } else {
        a = a.mit_notiz(format!("im Geltungsbereich: {}", marken.join(", ")));
    }
    absagen.schiebe(a);
}
