//! **Pass 8 -- `effects`, und der Grund, warum dieser Pass ueberhaupt existiert.**
//!
//! `SPRACHE.md` §7 und `SYNTAX.md` §6:
//!
//! > **`effects` ist NICHT fail-open.** Eine Funktion **ohne** `effects` ist ein
//! > Uebersetzungsfehler; wer nichts anfasst, schreibt `effects { pure }`. Die frueher
//! > moegliche Auslassung war zugleich **die staerkste Zusage und die kuerzeste
//! > Spezifikation** -- der Anreiz stand gegen die Vollstaendigkeit.
//!
//! Genau deshalb faellt die Pflicht **an der Abwesenheit**, nicht am Inhalt: der Parser laesst
//! die Klausel weg, wenn sie fehlt, und dieser Pass sieht das Loch. Ein Werkzeug, das eine
//! fehlende Klausel als „keine Wirkungen" liest, belohnt das Weglassen.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => funktion(f, absagen),
        ItemArt::Axiom(a) => rein_allein(&a.effects, absagen),
        _ => {}
    });
}

fn funktion(f: &FnDecl, absagen: &mut Absagen) {
    match &f.effects {
        None => {
            // `spec fn` hat keine Laufzeitwirkung; fuer sie ist die Klausel freigestellt.
            if f.klasse != Some(FnKlasse::Spec) {
                absagen.schiebe(
                    Absage::fehler(
                        "E001",
                        f.name.span,
                        format!("`{}` hat keine `effects`-Klausel", f.name.text),
                    )
                    .mit_notiz(
                        "SPRACHE.md §7: `effects` ist Pflicht und nicht fail-open -- \
                         wer nichts anfasst, schreibt `effects { pure }`",
                    )
                    .mit_notiz(
                        "die Auslassung war zugleich die staerkste Zusage und die kuerzeste \
                         Spezifikation; der Anreiz stand gegen die Vollstaendigkeit",
                    ),
                );
            }
        }
        Some(w) => rein_allein(w, absagen),
    }

    if f.klasse == Some(FnKlasse::Divergent) {
        let divergiert = f
            .effects
            .as_ref()
            .map(|w| w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert)))
            .unwrap_or(false);
        if !divergiert {
            absagen.schiebe(
                Absage::hinweis(
                    "E003",
                    f.name.span,
                    format!(
                        "`divergent fn {}` nennt `diverges` nicht in seinen Wirkungen",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SYNTAX.md §14 schreibt `divergent fn idle() effects { diverges };` -- \
                     die ausgesprochene Nichtterminierung gehoert in die Wirkungsliste",
                ),
            );
        }
    }

    // Eine `spec fn` mit `= pred;` ist die einzige Form, in der ein Quantor im Rumpf steht.
    if f.klasse != Some(FnKlasse::Spec) {
        if let FnRumpf::Pred(p) = &f.rumpf {
            absagen.schiebe(
                Absage::fehler(
                    "E004",
                    p.span,
                    "ein Praedikat als Rumpf steht nur einer `spec fn` zu",
                )
                .mit_notiz("`fndecl`: `= pred ;` nur fuer `spec fn`"),
            );
        }
    }
}

/// `pure` heisst „fasst nichts an". Eine zweite Wirkung daneben ist ein Widerspruch, kein
/// Zusatz -- und der Widerspruch faellt hier, nicht beim Leser.
fn rein_allein(w: &Wirkungen, absagen: &mut Absagen) {
    let rein: Vec<&Wirkung> = w
        .liste
        .iter()
        .filter(|e| matches!(e.art, WirkungArt::Rein))
        .collect();
    if rein.is_empty() {
        return;
    }
    if w.liste.len() > 1 {
        let andere: Vec<&str> = w
            .liste
            .iter()
            .filter(|e| !matches!(e.art, WirkungArt::Rein))
            .map(|e| e.art.benennung())
            .collect();
        let stelle = rein[0].span;
        absagen.schiebe(
            Absage::fehler(
                "E002",
                stelle,
                format!(
                    "`pure` steht neben {} -- `pure` heisst, dass nichts angefasst wird",
                    andere.join(", ")
                ),
            )
            .mit_notiz("entweder `effects { pure }` allein, oder die Wirkungen ohne `pure`"),
        );
    }
    if rein.len() > 1 {
        absagen.schiebe(Absage::fehler(
            "E002",
            rein[1].span,
            "`pure` steht zweimal in derselben Wirkungsliste",
        ));
    }
}
