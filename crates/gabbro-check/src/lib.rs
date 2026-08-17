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

pub mod aufrufgraph;
pub mod m2;
pub mod m3;
pub mod paarung;
pub mod gruppe;
pub mod emit;
pub mod geteilt;
pub mod kbedingung;
pub mod kosten;
mod m1;
mod namen;
mod schleifen;
mod wirkungen;

pub mod typen;
pub mod umgebung;

pub use m1::Zaehlung;
pub use kosten::Zaehlung as Kostenzaehlung;

pub mod korpus;
pub mod manifest;
pub mod schablonen;
pub mod zeugnis;

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
            quelle: "E5: every declaration is complete in exactly one place",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 2,
            name: "D1/D2",
            quelle: "SPRACHE.md §3: undurchsichtige Neutypen, vollstaendige Layouts, \
                     erschoepfende Aufzaehlung",
            zustand: Zustand::Teilgebaut(
                "die K-Bedingung ist gebaut (`D001`: keine Handmutation an einer `table` \
                 mit `ops`) -- **erschoepfendes `match` ueber `tagged` nicht**, und \
                 undurchsichtige Neutypen ohne Umwandlung ebenfalls nicht",
            ),
        },
        Pass {
            nummer: 3,
            name: "M1 + V1–V3",
            quelle: "SPRACHE.md §3.2: range types and the three flow rules",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 4,
            name: "M3",
            quelle: "SYNTAX.md §3: Adressraeume und Zugriffsrechte am Zeiger",
            zustand: Zustand::Teilgebaut(
                "gebaut: Rechtepruefung an Lesen und Schreiben, die Platzierungsregel \
                 `ops`-Traeger nicht im `dma`-Raum (`R001`-`R003`). **NICHT gebaut: die \
                 Barriere aus dem Raum** -- welche Barriere ein `dma`-Zugriff verlangt, ist \
                 eine Aussage ueber das Speichermodell, dieselbe Axiomschicht wie bei der \
                 Paarung. **Und keine Aliasanalyse**: zwei `ptr<normal, rw>` auf dasselbe \
                 Objekt bleiben ununterscheidbar, dafuer steht `own`",
            ),
        },
        Pass {
            nummer: 5,
            name: "M2",
            quelle: "SPRACHE.md §4: lineare und geisterhafte Werte",
            zustand: Zustand::Teilgebaut(
                "gebaut: genau-einmal je Weg, Zweigabgleich, `consumes` gegen geliehen \
                 (`L101`-`L105`). **NICHT gebaut: die Ghost-Loeschung** -- ein `ghost`-Wert \
                 existiert zur Laufzeit nicht, seine Linearitaet ist eine Aussage ueber den \
                 BEWEIS, und die Aliasfrage gehoert M3",
            ),
        },
        Pass {
            nummer: 6,
            name: "M4/Schleifen",
            quelle: "SYNTAX.md §8: three loop forms, `leave`/`next` target a label",
            zustand: Zustand::Gebaut,
        },
        Pass {
            nummer: 7,
            name: "Paarung",
            quelle: "SPRACHE.md part II §1: ordering is PAIRED, not declared",
            zustand: Zustand::Teilgebaut(
                "gebaut: `publishes`/`awaits`/`exchange` ueber die vereinigte Menge, \
                 Namensgleichheit nach Indexsubstitution (`V001`-`V004`). **NICHT gebaut: die \
                 Aussage ueber das SPEICHERMODELL** -- dass `release`/`acquire` die \
                 Sichtbarkeit herstellen, die die Paarung behauptet, faellt in die \
                 Axiomschicht und nicht in diesen Pass",
            ),
        },
        Pass {
            nummer: 8,
            name: "effects",
            quelle: "SPRACHE.md §7: `effects` is mandatory and not fail-open",
            zustand: Zustand::Teilgebaut(
                "Schreiben, `locks` **und seit 2026-08-16 das Lesen** (Lesart A, `E010`) \
                 werden gegen die Liste gehalten. **Was fehlt, ist die Reichweite von \
                 `E010`:** es spricht nur ueber bekannten Weltzustand (`static`, `atomic`, \
                 `table`, `device`, `state`), weil eine Variante kein Ort ist und ein \
                 AUSSCHNITT seine Namen nicht deklariert -- auf dem Fragmentkorpus hat die \
                 Regel damit **null Biss**, und ihr Beleg kommt aus Gift 62 und zwei \
                 Mutationen, nicht vom Korpus",
            ),
        },
        // **Pass 10 ist neu, und das ist eine Aenderung an der Spezifikation.**
        //
        // `SPRACHE.md` Teil III §6 legt neun Paesse fest und sagt: *„die Spezifikation IST die
        // Passliste"*. Ein zehnter Pass heisst also nicht „ein Modul mehr", sondern **die
        // Liste ist gewachsen** -- und das gehoert gebucht, nicht eingeschoben. Der Grund ist
        // gemessen (`MESSUNGEN.md`, SWEEP, V4) und nicht entworfen: eine Invariante ZWISCHEN
        // Traegern hat in den neun Paessen keine Stelle. Pass 2 prueft Deklarationen, Pass 8
        // die Wirkungsliste einer Funktion gegen ihren Rumpf -- keiner von beiden kennt einen
        // Verbund.
        Pass {
            nummer: 10,
            name: "Gruppe",
            quelle: "MESSUNGEN.md, SWEEP der Verbindungs-Invarianten (2026-08-16), V4",
            zustand: Zustand::Teilgebaut(
                "gebaut: der SPERRABDRUCK (`U001`-`U005`), der ZUG (`U006`) und die \
                 VERBINDUNGSAUSSAGE als Form (`U007`: eine Gruppen-Invariante nennt \
                 mindestens zwei Traeger, sonst gehoert sie an die Tabelle). **NICHT \
                 gebaut: die Erhaltung** -- dass die Invariante unter einer Operation HAELT, \
                 ist Beweisersache und faellt an S16/S17, nicht an diesen Pass. Er prueft \
                 die drei Bedingungen, unter denen die Frage ueberhaupt gestellt werden \
                 kann",
            ),
        },
        Pass {
            nummer: 9,
            name: "costs",
            quelle: "SPRACHE.md §7: 1 op = one Gabbro primitive, computed statically",
            zustand: Zustand::Teilgebaut(
                "gerechnet werden Ruempfe, `locks`-Bloecke gegen `held` und Aufrufe ueber \
                 die DEKLARIERTEN Kosten des Gerufenen -- **Rekursion traegt damit eine \
                 Annahme statt einer Rechnung**, und `per_pass` mit eingabeabhaengiger \
                 Schranke steht nicht fest",
            ),
        },
    ]
}

/// Was ein Lauf angesehen hat. **Steht neben dem Ergebnis, nicht dahinter:** eine Zahl
/// ueber die Deckung ist der Unterschied zwischen „nichts gefunden" und „nichts angesehen".
#[derive(Debug, Clone, Copy, Default)]
pub struct Bericht {
    pub m1: Zaehlung,
    pub kosten: Kostenzaehlung,
}

/// Fahrt aller **gebauten** Paesse ueber einen Baum, in der Reihenfolge der Liste.
pub fn pruefe(baum: &Programm, absagen: &mut Absagen) -> Bericht {
    namen::pass(baum, absagen);
    kbedingung::pass(baum, absagen);
    let m1 = m1::pass(baum, absagen);
    schleifen::pass(baum, absagen);
    wirkungen::pass(baum, absagen);
    geteilt::pass(baum, absagen);
    m3::pass(baum, absagen);
    m2::pass(baum, absagen);
    paarung::pass(baum, absagen);
    gruppe::pass(baum, absagen);
    let kosten = kosten::pass(baum, absagen);
    Bericht { m1, kosten }
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
pub fn fuer_jedes_item_im_modul(baum: &Programm, f: &mut impl FnMut(&Item, &str)) {
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
