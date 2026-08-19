//! **«B24» an EINER Stelle -- und zwei Leser statt einem.**
//!
//! Die Entscheidung fiel am 2026-08-18 und wurde am selben Tag gebaut: *eine Bitlage liegt
//! im EIGENEN WORT des Feldes; jenseits davon gibt es nichts zu bedeuten.* Gebaut wurde sie
//! im **Erzeuger** -- und `gabbro pruefe` senkt nicht ab.
//!
//! ```gabbro
//! format F endian big { a : u8 @[9:4], }     -- gabbro pruefe: 0 Fehler
//! device D(b : Pa) at mmio {
//!     reg R : u32 @0x00 class r fields { A @40, }   -- gabbro pruefe: 0 Fehler
//! }
//! ```
//!
//! **Gemessen 2026-08-19: sechs Giftformen, sechsmal Schweigen.** Die Regel gab es, sie stand
//! nur auf einer Flaeche, die die meisten Programme nie beruehren -- *dieselbe Lage wie
//! `D004` auf diesem Korpus, nur schaerfer, weil hier die Absage schon geschrieben war.*
//!
//! ## Was hier steht und was nicht
//!
//! | | wo | warum dort |
//! |---|---|---|
//! | Lage jenseits der Wortbreite | **Pruefer** (`N007`) | falsch, ob jemand absenkt oder nicht |
//! | zwei Lagen ueberlappen | **Pruefer** (`N008`) | dito -- und `N003` sagt es fuer Register laengst |
//! | eine Luecke im Wort | **Erzeuger** (`C001`) | erst die Absenkung braucht eine bestimmte Wortgrenze |
//!
//! *Der Schnitt ist die Antwort auf „warum nicht alles im Pruefer": eine Luecke macht das
//! Wort fuer den Erzeuger UNENTSCHEIDBAR; eine Lage jenseits der Breite und eine
//! Ueberlappung sind fuer jeden FALSCH.* **Und `format Elf64Ph` haengt daran** -- `p_flags :
//! u32 @[2:0]` laesst 29 Bits unbenannt, geht aber durch, weil niemand es absenkt.

use gabbro_syntax::ast::{BitPos, FeldDecl, TypExpr};
use gabbro_syntax::kw::Kw;

/// Ein Eintrag der Feldliste, nach «B24» gelesen.
pub enum Eintrag {
    /// Ein Feld ohne Bitlage -- ein ganzes Wort fuer sich.
    Ganz(usize),
    /// Eine Bitgruppe: alle folgenden Felder mit Lage, gleichem Ganzzahlwort, EIN Wort.
    Gruppe {
        breite_bytes: u32,
        /// je Feld: (Index in `felder`, hi, lo)
        felder: Vec<(usize, u128, u128)>,
        /// Sind alle Bits des Wortes benannt? *Der Erzeuger braucht das, der Pruefer nicht.*
        gekachelt: bool,
    },
    /// Ein Feld, dessen Traeger keine Ganzzahl ist -- **hier schweigt «B24»**, weil die
    /// Wortbreite ohne den Traeger nicht feststeht. `bool @63` in einer `Pte` ist genau das:
    /// die 63 kommt aus dem Wort der Gruppe, nicht aus `bool`.
    ///
    /// *W10: eine untere Schranke weist weder zurueck noch bestaetigt sie.*
    Unklar(usize),
}

/// Was an einer Bitlage falsch sein kann, unabhaengig von jeder Absenkung.
pub struct Befund {
    pub feld: usize,
    /// Bei einer Ueberlappung: das andere Feld.
    pub anderes: Option<usize>,
    pub kennung: &'static str,
    pub text: String,
    pub notiz: &'static str,
}

/// Die Wortbreite einer Ganzzahl in Bytes. `None`, wenn der Traeger keine Ganzzahl ist.
pub fn wortbreite(t: &TypExpr) -> Option<(u32, Kw)> {
    let TypExpr::Int(i) = t else { return None };
    Some(aus_intty(i))
}

/// Dieselbe Breite, aber direkt am Ganzzahltyp -- ein `reg` traegt ihn ohne `TypExpr` herum.
pub fn aus_intty(i: &gabbro_syntax::ast::IntTy) -> (u32, Kw) {
    let b = match i.wort {
        Kw::U8 | Kw::I8 => 1,
        Kw::U16 | Kw::I16 => 2,
        Kw::U32 | Kw::I32 => 4,
        _ => 8,
    };
    (b, i.wort)
}

/// **Die Regel fuer EINE Lage, und sie ist die ganze erste Haelfte von «B24».**
///
/// `hi < lo` ist keine Umkehrung, sondern ein Schreibfehler: `@[3:7]` nennt keinen Bereich.
pub fn lage_pruefen(bp: &BitPos, bits: u32, feld: usize, name: &str, wort: &str) -> Option<Befund> {
    let (hi, lo) = match bp {
        BitPos::Bit(b) => (*b, *b),
        BitPos::Bereich(h, l) => (*h, *l),
    };
    if hi < lo {
        return Some(Befund {
            feld,
            anderes: None,
            kennung: "N007",
            text: format!("`{name}` writes `@[{hi}:{lo}]` -- the high bit is below the low one"),
            notiz: "«B24»: a bit range runs from high to low, and `@[3:7]` names none",
        });
    }
    if hi >= bits as u128 {
        return Some(Befund {
            feld,
            anderes: None,
            kennung: "N007",
            text: format!(
                "bit {hi} of `{name}` lies outside its own word ({wort} has bits 0..{})",
                bits - 1
            ),
            notiz: "«B24», decided 2026-08-18: a position lies inside the field's OWN word -- \
                    beyond it there is nothing to mean. A 128-bit entry is TWO words, and \
                    saying so is cheaper than a rule about crossing",
        });
    }
    None
}

/// Die Feldliste eines `format` nach «B24** gelesen: Woerter, Gruppen, Befunde.
///
/// **Die Gruppenbildung ist die Wortgrenze selbst**, nicht eine Pruefung darueber: ein Wort
/// endet, wenn seine Bits vollstaendig sind. *Der erste Anlauf las alle aufeinanderfolgenden
/// Bitfelder gleicher Breite als EIN Wort und meldete an `dscp @[7:2]` eine Ueberlappung mit
/// `version @[7:4]` -- zwei Bytes des IP-Kopfs, als eines gelesen.*
pub fn lies(felder: &[FeldDecl]) -> (Vec<Eintrag>, Vec<Befund>) {
    let mut aus = Vec::new();
    let mut befunde = Vec::new();
    let mut i = 0usize;
    while i < felder.len() {
        if felder[i].bitpos.is_none() {
            aus.push(Eintrag::Ganz(i));
            i += 1;
            continue;
        }
        let Some((breite, wort)) = wortbreite(&felder[i].typ.typ) else {
            aus.push(Eintrag::Unklar(i));
            i += 1;
            continue;
        };
        let bits = breite * 8;
        let wortname = format!("{wort:?}").to_lowercase();
        let mut belegt: u128 = 0;
        let mut gruppe: Vec<(usize, u128, u128)> = Vec::new();
        while i < felder.len() {
            let g = &felder[i];
            let Some(bp) = &g.bitpos else { break };
            match wortbreite(&g.typ.typ) {
                Some((_, w2)) if w2 == wort => {}
                _ => break,
            }
            if let Some(b) = lage_pruefen(bp, bits, i, &g.name.text, &wortname) {
                befunde.push(b);
                i += 1;
                continue;
            }
            let (hi, lo) = match bp {
                BitPos::Bit(b) => (*b, *b),
                BitPos::Bereich(h, l) => (*h, *l),
            };
            let maske: u128 = (((1u128 << (hi - lo + 1)) - 1) << lo) & u128::from(u64::MAX);
            if belegt & maske != 0 {
                let anderes = gruppe
                    .iter()
                    .find(|(_, h2, l2)| lo <= *h2 && *l2 <= hi)
                    .map(|(x, _, _)| *x);
                befunde.push(Befund {
                    feld: i,
                    anderes,
                    kennung: "N008",
                    text: format!("the bits of `{}` overlap in this word", g.name.text),
                    notiz: "a word says which bits exist, and twice is not an answer -- \
                            `N003` says the same for a device register",
                });
                i += 1;
                continue;
            }
            belegt |= maske;
            gruppe.push((i, hi, lo));
            i += 1;
            let voll: u128 = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
            if belegt == voll {
                break;
            }
        }
        let voll: u128 = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
        aus.push(Eintrag::Gruppe {
            breite_bytes: breite,
            felder: gruppe,
            gekachelt: belegt == voll,
        });
    }
    (aus, befunde)
}
