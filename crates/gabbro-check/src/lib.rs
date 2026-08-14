//! **Die Pruefpaesse, in fester Reihenfolge.**
//!
//! `SPRACHE.md` Teil III §6 legt die Architektur fest:
//!
//! > Lexer → Parser (aus der vereinigten EBNF, handgeschrieben, kein Generator) → ein Kernbaum
//! > → **Pruefpaesse in fester Reihenfolge** (Namen, D1/D2, M1+V1–V3, M3, M2, M4/Schleifen,
//! > Paarung, effects, costs) → C-Emission.
//! >
//! > *jede Regel dieser drei Dokumente ist genau **ein** Pass oder ein benannter Teil eines
//! > Passes -- die Spezifikation ist die Passliste*
//!
//! Deshalb steht die Liste hier **vollstaendig**, samt der Paesse, die es noch nicht gibt.
//! Ein Pass mit Zustand [`Zustand::Offen`] prueft nichts und **sagt das**: ein Werkzeug, das
//! ungeprueftes Schweigen wie ein Gruen aussehen laesst, ist ein falsches Gruen -- dieselbe
//! Fehlerklasse, die `pruefe-syntax.sh` zweimal bezahlt hat.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::Absagen;

mod m1;
mod namen;
mod schleifen;
mod wirkungen;

pub mod typen;
pub mod umgebung;

pub use m1::Zaehlung;

pub mod korpus;
pub mod manifest;

/// Was ein Pass heute leistet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Zustand {
    /// Gebaut und in diesem Lauf gefahren.
    Gebaut,
    /// **Gebaut, aber mit benannten Loechern.** Die Gegenpruefung vom 2026-08-14 fand
    /// Dateien, die durchkamen und fallen mussten; der Text nennt, was heute noch
    /// durchkommt. *Ein teilgebauter Pass, der sich als gebaut meldet, ist ein falsches
    /// Gruen -- und genau das war er, bis diese Stufe dazukam.*
    Teilgebaut(&'static str),
    /// Nicht gebaut. Der Text nennt, was fehlt -- und was damit **ungeprueft** ist.
    Offen(&'static str),
}

/// Ein Pass der festen Reihenfolge.
pub struct Pass {
    pub nummer: u32,
    pub name: &'static str,
    /// Fundstelle der Regel, die dieser Pass abnimmt.
    pub quelle: &'static str,
    pub zustand: Zustand,
}

/// Die Passliste. **Die Reihenfolge ist Teil der Festlegung, nicht des Geschmacks.**
pub fn passliste() -> Vec<Pass> {
    vec![
        Pass {
            nummer: 1,
            name: "Namen",
            quelle: "E5: jede Deklaration ist an genau einer Stelle vollstaendig",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 2,
            name: "D1/D2",
            quelle: "SPRACHE.md §3: undurchsichtige Neutypen, vollstaendige Layouts, \
                     erschoepfende Aufzaehlung",
            zustand: Zustand::Offen(
                "erschoepfendes `match` ueber `tagged` braucht den Typ des Gegenstands \
                 und damit M1; heute ungeprueft",
            ),
        },
        Pass {
            nummer: 3,
            name: "M1 + V1–V3",
            quelle: "SPRACHE.md §3.2: Bereichstypen und die drei Flussregeln",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 4,
            name: "M3",
            quelle: "SYNTAX.md §3: Adressraeume und Zugriffsrechte am Zeiger",
            zustand: Zustand::Offen("Rechtepruefung an Lesen/Schreiben, Barriere aus dem Raum"),
        },
        Pass {
            nummer: 5,
            name: "M2",
            quelle: "SPRACHE.md §4: lineare und geisterhafte Werte",
            zustand: Zustand::Offen(
                "P4 des Prueferplans: echte Linearitaet -- der einzige Mechanismus, den \
                 kein vorhandenes Werkzeug liefert",
            ),
        },
        Pass {
            nummer: 6,
            name: "M4/Schleifen",
            quelle: "SYNTAX.md §8: drei Schleifenformen, `leave`/`next` zielen auf eine Marke",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 7,
            name: "Paarung",
            quelle: "SPRACHE.md Teil II §1: Ordering wird gepaart, nicht deklariert",
            zustand: Zustand::Offen("P6 des Prueferplans: `publishes`/`awaits` gegenueberstellen"),
        },
        Pass {
            nummer: 8,
            name: "effects",
            quelle: "SPRACHE.md §7: `effects` ist Pflicht und nicht fail-open",
            zustand: Zustand::Teilgebaut(
                "Schreiben und `locks` werden gegen die Liste gehalten; **Lesen nicht** \
                 (FRAGMENTE.md liest ueberall ohne `reads`-Zeile, und ob das ein Befund ist, \
                 entscheidet nicht dieser Pass), und **Aufrufwirkungen nicht** -- dazu \
                 muessten die Wirkungen des Gerufenen auf die Argumente abgebildet werden",
            ),
        },
        Pass {
            nummer: 9,
            name: "costs",
            quelle: "SPRACHE.md §7: 1 op = eine Gabbro-Primitive, statisch ausgerechnet",
            zustand: Zustand::Offen(
                "verlangt das Kostenmodell ueber dem Kernbaum -- `held`, `per_pass` und \
                 `bounded` sprechen in dieser Groesse",
            ),
        },
    ]
}

/// Was ein Lauf angesehen hat. **Steht neben dem Ergebnis, nicht dahinter:** eine Zahl
/// ueber die Deckung ist der Unterschied zwischen „nichts gefunden" und „nichts angesehen".
#[derive(Debug, Clone, Copy, Default)]
pub struct Bericht {
    pub m1: Zaehlung,
}

/// Fahrt aller **gebauten** Paesse ueber einen Baum, in der Reihenfolge der Liste.
pub fn pruefe(baum: &Programm, absagen: &mut Absagen) -> Bericht {
    namen::pass(baum, absagen);
    let m1 = m1::pass(baum, absagen);
    schleifen::pass(baum, absagen);
    wirkungen::pass(baum, absagen);
    Bericht { m1 }
}

/// Was dieser Lauf **nicht** geprueft hat -- zum Abdrucken neben dem Ergebnis.
pub fn ungeprueft() -> Vec<Pass> {
    passliste()
        .into_iter()
        .filter(|p| matches!(p.zustand, Zustand::Offen(_) | Zustand::Teilgebaut(_)))
        .collect()
}

/// Laeuft ueber jedes Item, auch die in Modulen.
pub(crate) fn fuer_jedes_item(baum: &Programm, f: &mut impl FnMut(&Item)) {
    fuer_jedes_item_im_modul(baum, &mut |i, _| f(i));
}

/// Wie oben, aber **mit dem Modulpfad**. Ohne ihn kann ein Pass einen Namen nicht
/// aufloesen -- er sieht `nimm` und weiss nicht, ob `eins::nimm` oder `zwei::nimm` gemeint
/// ist. Genau daran loeschte M1 bis zum 2026-08-14 Bereichspruefungen stillschweigend.
pub(crate) fn fuer_jedes_item_im_modul(baum: &Programm, f: &mut impl FnMut(&Item, &str)) {
    fn geh(items: &[Item], pfad: &str, f: &mut impl FnMut(&Item, &str)) {
        for i in items {
            f(i, pfad);
            if let ItemArt::Modul(m) = &i.art {
                let innen = if pfad.is_empty() {
                    m.pfad.text()
                } else {
                    format!("{pfad}::{}", m.pfad.text())
                };
                geh(&m.items, &innen, f);
            }
        }
    }
    geh(&baum.items, "", f);
}
