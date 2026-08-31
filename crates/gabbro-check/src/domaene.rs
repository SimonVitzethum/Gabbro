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

use gabbro_syntax::ast::{
    Block, Domaene, FnRumpf, Ident, Item, ItemArt, Ort, OrtSuffix, Pred, PredArt, Programm,
    Schleife, StmtArt,
};
use gabbro_syntax::diag::{Absage, Absagen};
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

// ==========================================================================================
// `chain(a, b) in <place>` -- the two field names. **The one domain that names its edge AT
// THE WALK is the one whose edge nobody checked.**
// ==========================================================================================

/// **`D014`/`D015`/`D016` -- the sibling-chain edge, held against the table it walks.**
///
/// `SYNTAX.md`:1060 moved the tree edge to the `table` with the argument that two sites could
/// name different fields *"without anybody comparing the two"* -- and it names `chain(a, b)
/// in` as the model that could already do it. **On `chain` itself the argument never fell
/// back.** Measured on 2026-08-31 (`messung/DOMAENENNAMEN.md` §2c): five falsifications of
/// the edge in `beispiele/55-kindkette.gab`, in `ensures`, in an `invariant` and in a `spec
/// fn` body -- **0 errors and 0 `C001` every time**, while `tree { child gibtsnicht }` at the
/// very same table falls at `D006`.
///
/// The three rules are `D006`-`D008` word for word, and deliberately so: it is the SAME
/// question about the SAME kind of name, and a second wording would be a second rule.
///
/// * **`D014`** -- the field stands in the slot. A name that stands nowhere is no edge.
/// * **`D015`** -- it is `option index into <table>`. A chain must be able to END, and the
///   sentinel for that is `count` itself (`beweise/Option_Sonderwert.thy`); an `index into T`
///   without `option` has no end, a `bool` is not an edge at all.
/// * **`D016`** -- it points into the table it is walked in. An edge into another table is a
///   foreign key, and `chain(a, b) in` says nothing about that.
///
/// ## What this does NOT say, and it is two of the five falsifications
///
/// `chain(naechstes_geschwister, erstes_kind)` (the declared pair with the roles exchanged)
/// and `chain(elter, elter)` (the tree's parent edge) pass all three rules **and they should
/// under Regel A**: both are structurally well-formed chains. `chain(x, x)` walks the leftmost
/// spine and stands in the corpus (`messung/proben/probe-vier-zellen.gab`:59,
/// `chain(naechst, naechst)`); `chain(parent, parent)` is the ancestor chain. *Refusing them
/// needs a statement about what the author MEANT, and no measurement of this bench carries
/// one.* The gap is named in `messung/DOMAENENNAMEN.md` and left open there.
///
/// ## And the carrier is not held either
///
/// If the place does not resolve to a table, this pass is **silent**. That is the S2 gap of
/// the same measurement -- the TYPE of a domain's place is checked by nobody, for all nine
/// domains -- and it is a separate build over nine words, not a side effect of this one.
pub fn kettenkanten(baum: &Programm, u: &Umgebung, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        kettenkanten_im_item(item, modul, u, absagen);
    });
}

fn kettenkanten_im_item(item: &Item, modul: &str, u: &Umgebung, absagen: &mut Absagen) {
    match &item.art {
        // A function: its parameters are the local view, and its CONTRACTS as well as
        // its BODY are read. **All positions**, not just `ensures` -- the position finding
        // of `messung/DOMAENENNAMEN.md` stands right beside this rule.
        ItemArt::Funktion(f) => {
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            for p in &f.parameter {
                lokal.insert(p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ));
            }
            let s = Sicht { u, modul, lokal: &lokal };
            for p in f.requires.iter().chain(f.ensures.iter()) {
                aus_pred(p, &s, absagen);
            }
            match &f.rumpf {
                FnRumpf::Pred(p) => aus_pred(p, &s, absagen),
                FnRumpf::Block(b) => aus_block(b, &s, absagen),
                _ => {}
            }
        }
        // A table invariant: `Self` IS the table, and nobody else binds the name --
        // the environment does not know it (`m1.rs` says exactly that at `M120`).
        ItemArt::Tabelle(t) => {
            let q = if modul.is_empty() {
                t.name.text.clone()
            } else {
                format!("{modul}::{}", t.name.text)
            };
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            lokal.insert("Self".to_string(), Typ::Tabelle(q));
            let s = Sicht { u, modul, lokal: &lokal };
            for i in &t.invarianten {
                aus_pred(&i.pred, &s, absagen);
            }
        }
        ItemArt::Gruppe(g) => {
            let lokal: HashMap<String, Typ> = HashMap::new();
            let s = Sicht { u, modul, lokal: &lokal };
            for i in &g.invarianten {
                aus_pred(&i.pred, &s, absagen);
            }
        }
        _ => {}
    }
}

fn aus_block(b: &Block, s: &Sicht, absagen: &mut Absagen) {
    for st in &b.anweisungen {
        if let StmtArt::Schleife(sch) = &st.art {
            if let Schleife::Traverse(t) = sch.as_ref() {
                kette_pruefen(&t.domaene, s, absagen);
                if let Some(p) = &t.invariante {
                    aus_pred(p, s, absagen);
                }
            }
        }
        for k in crate::unterbloecke(st) {
            aus_block(k, s, absagen);
        }
    }
}

fn aus_pred(p: &Pred, s: &Sicht, absagen: &mut Absagen) {
    match &p.art {
        PredArt::Quantor(q) => {
            kette_pruefen(&q.domaene, s, absagen);
            aus_pred(&q.rumpf, s, absagen);
        }
        PredArt::Klammer(i) | PredArt::Nicht(i) => aus_pred(i, s, absagen),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            aus_pred(a, s, absagen);
            aus_pred(b, s, absagen);
        }
        // **No `_` arm.** The remaining predicate kinds carry no quantifier, and when
        // one grows that changes this pass should fail to compile rather than overlook it
        // -- the lesson of the 78 holes behind `lib.rs::unterbloecke`.
        PredArt::Vergleich(_)
        | PredArt::Element(_, _)
        | PredArt::Erreicht { .. }
        | PredArt::Held { .. } => {}
    }
}

fn kette_pruefen(d: &Domaene, s: &Sicht, absagen: &mut Absagen) {
    let Domaene::KetteIn { a, b, ort } = d else { return };
    let Some(tabelle) = s.kettentabelle(ort) else { return };
    // **Module-aware, and not a direct `.get(` on a qualified map.** `tabellenname` returns
    // the QUALIFIED name for a `Typ::Tabelle` and the bare one for an `index into T` (it
    // reads it out of the type name) -- a straight lookup would silently miss the second
    // kind, and a silent miss here reads as "this chain is fine". *That is the shape of the
    // `M103` hole of 2026-08-17, and `zaehle-karten.py` counts exactly this move.*
    let kurz = kurzname(&tabelle);
    let Some((_, felder)) = s
        .u
        .tabellen
        .iter()
        .find(|(k, _)| *k == &tabelle || kurzname(k) == kurz)
    else {
        return;
    };
    // **The position stands in the message.** `chain(a, b)` has TWO edges, and a refusal
    // about "the edge" sends the reader to the wrong one half the time.
    kante_pruefen(a, true, kurz, felder, absagen);
    kante_pruefen(b, false, kurz, felder, absagen);
}

/// `erste` says which of the two edges is refused -- the message writes `chain(a, …)` or
/// `chain(…, b)` and thereby names the position along with the name.
fn kante_pruefen(
    kante: &Ident,
    erste: bool,
    kurz: &str,
    felder: &[(String, Typ)],
    absagen: &mut Absagen,
) {
    let form = if erste {
        format!("chain({}, …)", kante.text)
    } else {
        format!("chain(…, {})", kante.text)
    };
    let Some((_, typ)) = felder.iter().find(|(n, _)| *n == kante.text) else {
        absagen.schiebe(
            Absage::fehler(
                "D014",
                kante.span,
                format!("`{form}` names no field of `{kurz}`'s slot"),
            )
            .mit_notiz(
                "a chain edge is a FIELD of the slot it walks -- a name that stands nowhere \
                 is none. `D006` says the same sentence at the `tree` of a table",
            ),
        );
        return;
    };
    // `option index into T` stands as the NAME in the type (`umgebung.rs`) -- and that it
    // is a DIFFERENT type from `index into T` is the finding of «C1».
    let name = match typ {
        Typ::Benannt { name, .. } => name.as_str(),
        _ => "",
    };
    let Some(ziel) = name.strip_prefix("option index into ") else {
        absagen.schiebe(
            Absage::fehler(
                "D015",
                kante.span,
                format!("`{form}` is not `option index into {kurz}`"),
            )
            .mit_notiz(
                "the chain must be able to END, and the sentinel for that is `count` itself \
                 (beweise/Option_Sonderwert.thy) -- an `index into T` without `option` has no \
                 end, and a field that is no index at all is no edge",
            ),
        );
        return;
    };
    if kurzname(ziel) != kurz {
        absagen.schiebe(
            Absage::fehler(
                "D016",
                kante.span,
                format!(
                    "`{form}` points into `{}`, not into `{kurz}` itself",
                    kurzname(ziel)
                ),
            )
            .mit_notiz(
                "a chain stays inside the table it is walked in -- an edge into another one \
                 is a foreign key, and `chain(a, b) in` says nothing about that",
            ),
        );
    }
}

fn kurzname(n: &str) -> &str {
    n.rsplit("::").next().unwrap_or(n)
}

impl<'a> Sicht<'a> {
    /// **Which table does `chain(a, b) in <place>` walk?** -- and `None` means *stay silent*.
    ///
    /// Two shapes, and only two, because a third one would be guessing:
    ///
    /// * `<base>.slots[i]` -- a slot. The type of the whole place is a `Verbund` and has lost
    ///   the table name (`umgebung.rs::feld_von`), so the BASE is asked instead.
    /// * `<base>` alone -- a table or an `index into T`.
    ///
    /// *`domaenenschranke` falls back from the whole place to the base for the same purpose.
    /// That is enough for a BOUND and not for a refusal:* there a too-large number is a
    /// too-weak verdict, here a wrongly guessed carrier would be a false alarm about a field
    /// name belonging to some other table.
    fn kettentabelle(&self, o: &Ort) -> Option<String> {
        let basis = Ort {
            basis: o.basis.clone(),
            suffixe: Vec::new(),
            span: o.span,
        };
        match o.suffixe.as_slice() {
            [] => self.tabellenname(o),
            [OrtSuffix::Feld(f), OrtSuffix::Index(_)] if f.text == "slots" => {
                self.tabellenname(&basis)
            }
            _ => None,
        }
    }
}
