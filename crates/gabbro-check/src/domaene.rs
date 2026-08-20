//! **Die Domaenenschranke -- an EINER Stelle, und zwei Leser.**
//!
//! `kosten.rs` rechnete sie seit jeher (`traverse` mal Rumpfkosten), und M1 brauchte sie am
//! 2026-08-19 fuer «H2.1»: *ein Traversierungszaehler erbt die Schranke seiner Domaene.*
//!
//! **Sie nachzubauen waere genau der Einwand, den dieser Ordner dreimal gegen sich selbst
//! erhoben hat** -- dieselbe Mechanik an zwei Orten, und nur eine geprueft. Also umgezogen
//! statt kopiert: `kosten.rs` ruft dieselben drei Funktionen wie `m1.rs`.
//!
//! *Die Funde, die in diesen Zeilen stecken, sind mitgezogen und stehen weiter dabei* -- der
//! `index into T`-Fall vom 2026-08-17 (`ancestors of`, kein Beispiel hatte die Stelle je
//! ausgeloest) und der Warteschlangenfall vom 2026-08-15 (die letzte Stelle, an der Tor P2
//! haengte).

use gabbro_syntax::ast::{Domaene, Ort};
use std::collections::HashMap;

use crate::typen::Typ;
use crate::umgebung::Umgebung;

pub struct Sicht<'a> {
    pub u: &'a Umgebung,
    pub modul: &'a str,
    pub lokal: &'a HashMap<String, Typ>,
}

impl<'a> Sicht<'a> {
    /// Die Schranke einer Domaene, soweit die Deklaration sie nennt.
    pub fn domaenenschranke(&self, d: &Domaene) -> Option<i128> {
        // **`elems of <Feld>` -- die Laenge steht im Typ, und niemand las sie.**
        //
        // Gefunden am 2026-08-19 beim Bau von «H2.1»: `traverse w of s over elems of
        // s.worte` lieferte KEINE Schranke, weil `tabellenname` nach einer Tabelle sucht und
        // `s.worte` ein Feld ist. *Dieselbe Klasse wie der `index into T`-Fall vom
        // 2026-08-17 -- eine Schranke, die dasteht und die der Pass nicht liest.*
        //
        // Der Fall stand nie auf: `unberuehrt` traegt keine `costs`-Zeile, also fragte der
        // Kostenpass nie. **Erst der Zaehler hat ihn ausgeloest.**
        if let Domaene::ElementeVon(o) = d {
            if let Typ::Feld { laenge: Some(n), .. } =
                self.u.typ_von_ort(self.modul, o, self.lokal).durchgreifen()
            {
                return Some(*n as i128);
            }
        }
        let tabelle = match d {
            // **`ancestors of` erbt die Schranke von `descendants of`** -- dieselbe Kante,
            // andere Richtung, und eine aufsteigende Kette kann ohne Zyklus nicht laenger
            // sein als die Tabelle Slots hat.
            Domaene::SlotsVon(o)
            | Domaene::NachfahrenVon(o)
            | Domaene::VorfahrenVon(o)
            | Domaene::ElementeVon(o) => {
                // `descendants of c.slots[s]` zeigt IN die Tabelle -- die Schranke ist die
                // der Tabelle, nicht die des Slots.
                self.tabellenname(o).or_else(|| {
                    self.tabellenname(&Ort {
                        basis: o.basis.clone(),
                        suffixe: Vec::new(),
                        span: o.span,
                    })
                })?
            }
            // **`queue place` -- die Schranke steht im Verbund, nicht in einer Tabelle.**
            //
            // Eine Warteschlange ist in Gabbro ein gewoehnlicher Verbund mit **genau einem
            // Feldarray** (`TidQueue = { buf : [u32; 32], head, tail, count }`). Damit ist
            // ihre Schranke die Laenge dieses Arrays, und zwar eindeutig -- gaebe es zwei
            // Arrays, waere nicht entscheidbar, welches die Schlange traegt.
            //
            // **Die Eindeutigkeit ist die Regel, nicht eine Konvention:** haben wir mehr
            // oder weniger als ein Array, liefert diese Funktion `None`, der Kostenpass
            // sagt `K003` und verlangt eine Deklaration. Er raet nicht.
            //
            // Gefunden am IPC-Fragment 2026-08-15: `traverse cand over queue
            // e.slots[core].receivers` war die letzte Stelle, an der Tor P2 haengte.
            Domaene::Schlange(o) => return self.arraylaenge_im_verbund(o),
            // **`mappings of` -- die Schranke steht in der `walk`-Deklaration.**
            // Gefunden am MMU-Fragment: dieselbe Klasse wie `queue` -- eine Schranke, die
            // dasteht und die der Pass nicht las, also `K003` sagte statt zu rechnen.
            //
            // **Seit Stufe 3 ist es `Knotenlaenge ^ levels`** und nicht mehr `levels x
            // Knotenlaenge` -- siehe `umgebung.rs::walkschranken`. Die Lesart ist
            // entschieden: die Domaene ist die BLATTMENGE, weil sie gebaut wurde, damit W^X
            // ueber die ganze Tabelle formulierbar wird. *Eine Kostenzusage ueber einer
            // Laufzeit-Traversierung darueber gibt es damit nicht mehr, und das ist die
            // wahre Aussage statt der bequemen.*
            Domaene::AbbildungenVon(o) => {
                // Der Ort nennt den PARAMETER (`mappings of w`), nicht den Walk -- der
                // Name kommt aus dem Typ, wie bei den Tabellen.
                let name = match self.u.typ_von_ort(self.modul, o, &*self.lokal).durchgreifen() {
                    Typ::Benannt { name, .. } => name.clone(),
                    Typ::Verbundname(n) => n.clone(),
                    _ => o.basis.text.clone(),
                };
                let kurz = name.rsplit("::").next().unwrap_or(&name).to_string();
                return self
                    .u
                    .walkschranken
                    .iter()
                    .find(|(k, _)| *k == &name || k.rsplit("::").next() == Some(kurz.as_str()))
                    .map(|(_, n)| *n as i128);
            }
            _ => return None,
        };
        // **Der Name kann unqualifiziert sein** -- `index into Topologie` nennt die Tabelle
        // ohne Modulpfad, waehrend `kapazitaeten` qualifiziert schluesselt. Ohne diesen
        // Umweg fiel die Schranke still aus, und `K003` machte daraus eine Absage ueber die
        // DEKLARATION statt ueber die Aufloesung.
        self.u
            .kapazitaeten
            .get(&tabelle)
            .copied()
            .or_else(|| {
                self.u
                    .kandidaten_aufloesbar(self.modul, &tabelle)
                    .into_iter()
                    .find_map(|k| self.u.kapazitaeten.get(&k).copied())
            })
            .map(|n| n as i128)
    }

    /// Die Laenge des **einzigen** Feldarrays eines Verbundes -- oder `None`.
    fn arraylaenge_im_verbund(&self, o: &Ort) -> Option<i128> {
        let t = self.u.typ_von_ort(self.modul, o, &*self.lokal);
        let Typ::Verbund(felder) = t.durchgreifen() else {
            return None;
        };
        let mut gefunden = None;
        for (_, ft) in felder {
            if let Typ::Feld { laenge, .. } = ft.durchgreifen() {
                if gefunden.is_some() {
                    return None; // zwei Arrays -- nicht entscheidbar, also nicht geraten
                }
                gefunden = laenge.map(|n| n as i128);
            }
        }
        gefunden
    }

    /// Auf welche Tabelle zeigt dieser Ort?
    fn tabellenname(&self, o: &Ort) -> Option<String> {
        let t = self.u.typ_von_ort(self.modul, o, &*self.lokal);
        match t {
            // **Ein `index into T` benennt seine Tabelle, und das war eine Luecke.**
            //
            // Gefunden am 2026-08-17 beim Bau von `ancestors of`: `traverse v over
            // descendants of g` mit `g : index into Topologie` lieferte `K003` -- keine
            // Schranke. Und das galt fuer `descendants of` schon vorher; **kein Beispiel
            // hatte die Stelle je ausgeloest**, weil der Korpus `descendants of` nur in
            // PRAEDIKATEN fuehrt (`ensures !exists k in descendants of s`), wo kein
            // Kostenpass laeuft.
            //
            // *Eine Schranke, die nie ausgeloest wurde, ist nicht gedeckt, sondern
            // unbeschaedigbar -- dieselbe Klasse wie eine Flaeche mit 0 Mutationen.*
            crate::typen::Typ::Benannt { ref name, .. } if name.starts_with("index into ") => {
                Some(name["index into ".len()..].to_string())
            }
            _ => match t.durchgreifen() {
                crate::typen::Typ::Tabelle(n) => Some(n.clone()),
                _ => None,
            },
        }
    }
}
