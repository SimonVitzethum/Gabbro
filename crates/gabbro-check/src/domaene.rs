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
use crate::umgebung::{Feldurteil, Umgebung};

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

/// **The PLACE of a quantifier domain -- its name (`D017`), its type (`D018`), and the two
/// edges of a chain (`D014`-`D016`).**
///
/// `SYNTAX.md`:1060 moved the tree edge to the `table` with the argument that two sites could
/// name different fields *"without anybody comparing the two"* -- and it names `chain(a, b)
/// in` as the model that could already do it. **On `chain` itself the argument never fell
/// back.** Measured on 2026-08-31 (`messung/DOMAENENNAMEN.md` §2c): five falsifications of
/// the edge in `beispiele/55-kindkette.gab`, in `ensures`, in an `invariant` and in a `spec
/// fn` body -- **0 errors and 0 `C001` every time**, while `tree { child gibtsnicht }` at the
/// very same table falls at `D006`.
///
/// The three chain rules are `D006`-`D008` word for word, and deliberately so: it is the SAME
/// question about the SAME kind of name, and a second wording would be a second rule.
///
/// * **`D014`** -- the field stands in the slot. A name that stands nowhere is no edge.
/// * **`D015`** -- it is `option index into <table>`. A chain must be able to END, and the
///   sentinel for that is `count` itself (`beweise/Option_Sonderwert.thy`); an `index into T`
///   without `option` has no end, a `bool` is not an edge at all.
/// * **`D016`** -- it points into the table it is walked in. An edge into another table is a
///   foreign key, and `chain(a, b) in` says nothing about that.
///
/// ## The place itself -- `D017` and `D018`, built 2026-08-31 on the second measurement
///
/// `messung/DOMAENENSTELLUNGEN.md` verified each of the 53 corpus quantifier sites OUTSIDE
/// `ensures` one by one: the base name of the place replaced by `zzznix`, the base load of
/// the same file subtracted. **51 stayed silent and 2 answered with `D012`** -- the premise
/// rule at a call of a generated operation, which lives in `opsruf.rs` and says nothing
/// about the name. *Zero of 53
/// got a refusal about the name.* And 38 TYPE falsifications across all five positions
/// (`slots of` over a record, `queue` over a table, `elems of` over a scalar field, …) got
/// zero.
///
/// * **`D017`** -- the base name of the place resolves. The same question `M109` asks in
///   `m1.rs`, in the positions `M109` does not read.
/// * **`D018`** -- the place is of the kind the DOMAIN needs: a table for `slots of`, a
///   record for `queue`, an array field for `elems of`, a `walk` for `mappings of`, a slot
///   for the three that walk the tree.
///
/// ### Why `D017` is its own code and not a wider `M109` (`m1.rs`)
///
/// All three rules named below live in `m1.rs`, in one loop over `f.ensures`.
/// **26 of the 53 places are `Self`**, 22 at a `table` and 4 at a `walk`. `M109` shares its
/// loop with `M120` -- *"`Self` in `ensures` names no carrier"* -- and in a `table`
/// invariant `Self` is EXACTLY the carrier. The same loop laid over the invariants would
/// have produced 26 false alarms, and `M111` (*"cannot establish this postcondition"*) has
/// nothing to say about a precondition. *The measurement decided the shape, not taste.*
///
/// ### What `D018` deliberately does NOT do
///
/// **`None` means stay silent.** A place whose type does not resolve is not a place of the
/// wrong kind, and a refusal about the checker's own ignorance is the false alarm this
/// bench spent a whole build undoing. `domaenenschranke` above falls back from the whole
/// place to its base for its own purpose; *that is enough for a BOUND and not for a
/// refusal* -- there a too-large number is a too-weak verdict, here a wrongly guessed
/// carrier would name a foreign field.
///
/// ## What this does NOT say, and it is two of the five chain falsifications
///
/// `chain(naechstes_geschwister, erstes_kind)` (the declared pair with the roles exchanged)
/// and `chain(elter, elter)` (the tree's parent edge) pass all three rules **and they should
/// under Regel A**: both are structurally well-formed chains. `chain(x, x)` walks the leftmost
/// spine and stands in the corpus (`messung/proben/probe-vier-zellen.gab`:59,
/// `chain(naechst, naechst)`); `chain(parent, parent)` is the ancestor chain. *Refusing them
/// needs a statement about what the author MEANT, and no measurement of this bench carries
/// one.* The gap is named in `messung/DOMAENENNAMEN.md` and left open there.
pub fn domaenen(baum: &Programm, u: &Umgebung, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        domaenen_im_item(item, modul, u, absagen);
    });
}

/// In which clause does the domain stand? **The refusal names it**, and one of the five is
/// skipped by `D017` because `M109` in `m1.rs` already reads it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stellung {
    Nachbedingung,
    Vorbedingung,
    Invariante,
    Spezifikation,
    Durchlauf,
}

impl Stellung {
    fn wort(self) -> &'static str {
        match self {
            Stellung::Nachbedingung => "`ensures`",
            Stellung::Vorbedingung => "`requires`",
            Stellung::Invariante => "an `invariant`",
            Stellung::Spezifikation => "the body of a `spec fn`",
            Stellung::Durchlauf => "a `traverse`",
        }
    }
}

fn domaenen_im_item(item: &Item, modul: &str, u: &Umgebung, absagen: &mut Absagen) {
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
            let mut geb = Vec::new();
            for p in &f.requires {
                aus_pred(p, &s, Stellung::Vorbedingung, &mut geb, absagen);
            }
            for p in &f.ensures {
                aus_pred(p, &s, Stellung::Nachbedingung, &mut geb, absagen);
            }
            match &f.rumpf {
                // A `spec fn` body IS a predicate -- and `= forall s in slots of c : …` is
                // five of the 53 places.
                FnRumpf::Pred(p) => aus_pred(p, &s, Stellung::Spezifikation, &mut geb, absagen),
                FnRumpf::Block(b) => aus_block(b, &s, &mut geb, absagen),
                FnRumpf::Asm(_) | FnRumpf::Keiner => {}
            }
        }
        // A table invariant: `Self` IS the table, and nobody else binds the name --
        // the environment does not know it (`m1.rs` says exactly that at `M120`).
        ItemArt::Tabelle(t) => {
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            lokal.insert("Self".to_string(), Typ::Tabelle(qualifiziert(modul, &t.name.text)));
            let s = Sicht { u, modul, lokal: &lokal };
            let mut geb = Vec::new();
            for i in &t.invarianten {
                aus_pred(&i.pred, &s, Stellung::Invariante, &mut geb, absagen);
            }
        }
        // **A `walk` invariant, and until today no reader of this pass came here.** Four of
        // the 53 places are `mappings of Self` under a `walk` -- among them the two that
        // carry W^X over the whole page table (`beispiele/07`). A `walk` head is a
        // `Verbundname` in the type world, exactly as `umgebung.rs` resolves it, and
        // `walknamen` is what tells it apart from a `format`.
        ItemArt::Walk(w) => {
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            lokal.insert(
                "Self".to_string(),
                Typ::Verbundname(qualifiziert(modul, &w.name.text)),
            );
            let s = Sicht { u, modul, lokal: &lokal };
            let mut geb = Vec::new();
            for i in &w.invarianten {
                aus_pred(&i.pred, &s, Stellung::Invariante, &mut geb, absagen);
            }
        }
        // A group invariant names its carriers by name; there is no `Self`, because a group
        // has SEVERAL carriers and the word would not know which one it means.
        //
        // **And the carriers are DECLARED by the `over { … }` list.** Without that line
        // `dokumente/SYNTAX.md`:1440 -- the grammar's own `group` example, which declares
        // no tables at all -- fell at `D017` over `Endpunkte`, a name its own first line
        // introduces. *A refusal that the documentation of the language triggers is a
        // refusal about the pass, not about the program.* Whether the carrier EXISTS is a
        // different question, and `D010` in `kbedingung.rs` asks it.
        ItemArt::Gruppe(g) => {
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            for tr in &g.traeger {
                // Known by NAME even when the carrier is of unknown kind -- `D018` then
                // stays silent, which is what it does everywhere it does not know.
                let art = match u.nennt_tabelle(modul, &tr.text) {
                    Some(q) => Typ::Tabelle(q),
                    None => Typ::Unbekannt,
                };
                lokal.insert(tr.text.clone(), art);
            }
            let s = Sicht { u, modul, lokal: &lokal };
            let mut geb = Vec::new();
            for i in &g.invarianten {
                aus_pred(&i.pred, &s, Stellung::Invariante, &mut geb, absagen);
            }
        }
        _ => {}
    }
}

fn qualifiziert(modul: &str, name: &str) -> String {
    if modul.is_empty() {
        name.to_string()
    } else {
        format!("{modul}::{name}")
    }
}

fn aus_block(b: &Block, s: &Sicht, geb: &mut Vec<String>, absagen: &mut Absagen) {
    for st in &b.anweisungen {
        if let StmtArt::Schleife(sch) = &st.art {
            // **No `_` arm.** All three loop kinds carry an `invariant`, and a fourth one
            // should be a compile error here rather than a silent hole.
            match sch.as_ref() {
                Schleife::Traverse(t) => {
                    domaene_pruefen(&t.domaene, s, Stellung::Durchlauf, geb, absagen);
                    // The traversal variable is DECLARED by the loop -- a domain in the
                    // invariant that names it must not count as unresolved.
                    geb.push(t.variable.text.clone());
                    if let Some(p) = &t.invariante {
                        aus_pred(p, s, Stellung::Invariante, geb, absagen);
                    }
                    geb.pop();
                }
                Schleife::Retry(r) => {
                    if let Some(p) = &r.invariante {
                        aus_pred(p, s, Stellung::Invariante, geb, absagen);
                    }
                    if let Some(p) = &r.bis {
                        aus_pred(p, s, Stellung::Invariante, geb, absagen);
                    }
                }
                Schleife::Forever(f) => {
                    if let Some(p) = &f.invariante {
                        aus_pred(p, s, Stellung::Invariante, geb, absagen);
                    }
                }
            }
        }
        for k in crate::unterbloecke(st) {
            aus_block(k, s, geb, absagen);
        }
    }
}

fn aus_pred(p: &Pred, s: &Sicht, st: Stellung, geb: &mut Vec<String>, absagen: &mut Absagen) {
    match &p.art {
        PredArt::Quantor(q) => {
            domaene_pruefen(&q.domaene, s, st, geb, absagen);
            // The quantifier DECLARES its variable, and an inner domain may run over it --
            // without this the rule would refuse the name the outer line just introduced.
            geb.push(q.variable.text.clone());
            aus_pred(&q.rumpf, s, st, geb, absagen);
            geb.pop();
        }
        PredArt::Klammer(i) | PredArt::Nicht(i) => aus_pred(i, s, st, geb, absagen),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            aus_pred(a, s, st, geb, absagen);
            aus_pred(b, s, st, geb, absagen);
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

fn domaene_pruefen(
    d: &Domaene,
    s: &Sicht,
    st: Stellung,
    geb: &[String],
    absagen: &mut Absagen,
) {
    grundname_pruefen(d, s, st, geb, absagen);
    ortsfelder_pruefen(d, s, geb, absagen);
    ortstyp_pruefen(d, s, geb, absagen);
    kette_pruefen(d, s, absagen);
}

/// **`D019` -- the FIELD names in the suffix of the place resolve.**
///
/// `messung/DOMAENENSTELLUNGEN.md` §7 carried the cell as unchecked, and the reason it gave
/// was read off the source: *"`M109` descends only into `[index]` suffixes, not into
/// `.field`; `D017` reads the BASE name. `D018` catches the case by half: if the field name
/// does not resolve, the type of the whole place is `Unbekannt`, and then it stays silent
/// too."*
///
/// **Measured 2026-08-31** (`messung/proben/probe-elems-feldname.gab`), `elems of
/// r.plaetze` falsified to `elems of r.gibtsnichtfeld` in three positions:
///
/// ```text
/// …: 8 items, 0 errors, 0 hints
/// ```
///
/// **Not one of them**, and `ensures` among them -- so `M109` does not read it either, and
/// the §7 cell was too kind to the checker. The control in the same run: falsifying the
/// BASE name (`elems of zzznix.plaetze`) does fall, at `M109`. *The base is read and the
/// field is not.*
///
/// A quantifier over a field that stands nowhere ranges over nothing -- **the same sentence
/// `D017` says about the base name**, and the same one `M134` says about a field access in
/// a body. `M134` lives in `m1.rs` and walks EXPRESSIONS; the place of a domain is not one,
/// which is exactly why it slipped through.
///
/// ## Silence where the prefix is not known, and it is the whole discipline
///
/// The walk stops at the first suffix whose carrier did not resolve. That makes the rule
/// safe in the two positions `D017` has to skip: at a `traverse` over a `let` binding the
/// base is `Unbekannt`, so nothing is claimed about the field either -- **the missing block
/// scope cannot produce a false refusal here**, because a rule that says nothing about an
/// unknown carrier says nothing at all.
fn ortsfelder_pruefen(d: &Domaene, s: &Sicht, geb: &[String], absagen: &mut Absagen) {
    let Some(o) = ort_der_domaene(d) else { return };
    // A quantifier variable carries no type in this pass -- `mappings of w` binds `m` to a
    // page-table entry, and `m.feld` must not be guessed at.
    if geb.contains(&o.basis.text) {
        return;
    }
    let mut traeger = s
        .lokal
        .get(&o.basis.text)
        .cloned()
        .or_else(|| s.u.suche_global(s.modul, &o.basis.text).cloned())
        .unwrap_or(Typ::Unbekannt);
    for suffix in &o.suffixe {
        if traeger.ist_unbekannt() {
            return;
        }
        match suffix {
            OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => {
                match s.u.feldurteil(&traeger, &f.text) {
                    Feldurteil::KeinFeld(hat) => {
                        let mut a = Absage::fehler(
                            "D019",
                            f.span,
                            format!("`{}` is not a field of this carrier", f.text),
                        )
                        .mit_notiz(format!(
                            "the carrier is `{}`, and a quantifier over a field that \
                             stands nowhere ranges over nothing -- it stands in the \
                             certificate and in the library ABI and says nothing",
                            traeger.text()
                        ));
                        a = if hat.is_empty() {
                            a.mit_notiz("it declares no fields at all")
                        } else {
                            a.mit_notiz(format!("it has: {}", hat.join(", ")))
                        };
                        absagen.schiebe(a);
                        return;
                    }
                    Feldurteil::KeineFelder => {
                        absagen.schiebe(
                            Absage::fehler(
                                "D019",
                                f.span,
                                format!("`.{}` reads a field on something that has none", f.text),
                            )
                            .mit_notiz(format!(
                                "the carrier is `{}` -- a number, a truth value or a reason \
                                 carries no fields",
                                traeger.text()
                            )),
                        );
                        return;
                    }
                    // The carrying case walks on; `Unklar` is the honest exit -- what the
                    // pass cannot type it does not judge.
                    Feldurteil::Traegt => {}
                    Feldurteil::Unklar => return,
                }
                traeger = s.u.feld_von(s.modul, &traeger, &f.text);
            }
            OrtSuffix::Index(_) => {
                traeger = match traeger.durchgreifen() {
                    Typ::Feld { element, .. } => (**element).clone(),
                    // A `table` indexed directly, and everything else this pass cannot
                    // follow: stop rather than guess.
                    _ => return,
                };
            }
        }
    }
}

/// The place a domain names -- or `None` for the two domains that name no place.
///
/// `fields of <path>` carries a PATH and not a place, and `threads` names nothing at all
/// (`Q3`, a language decision). *Both are named in `messung/DOMAENENSTELLUNGEN.md` as
/// unchecked, with the reason, instead of being guessed at here.*
fn ort_der_domaene(d: &Domaene) -> Option<&Ort> {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o)
        | Domaene::KetteIn { ort: o, .. } => Some(o),
        Domaene::FelderVon(_) | Domaene::Threads => None,
    }
}

/// **`D017` -- the base name of the place resolves.**
///
/// The resolution is the one `M109` performs in `m1.rs`, word for word (parameter, global,
/// a resolvable type or constant), widened by the three declaration maps a place may name
/// directly: a `table`,
/// a `walk`, a `format`. *A wider resolution can only make this rule quieter, and quiet is
/// the safe direction for a refusal.*
fn grundname_pruefen(
    d: &Domaene,
    s: &Sicht,
    st: Stellung,
    geb: &[String],
    absagen: &mut Absagen,
) {
    // **`ensures` has a reader, and a second one would be a second refusal for one fault.**
    // `M109` in `m1.rs` resolves EVERY name of a postcondition, not just the domain's place.
    if st == Stellung::Nachbedingung {
        return;
    }
    // **A `traverse` is not checked here, and the reason is scope and not reach.** A domain
    // in a body may run over a `let` binding, and this pass carries no block scope -- it
    // would refuse the name the line above introduced. At a `traverse` with a `costs` line
    // `K003` from `kosten.rs` speaks instead: about the missing BOUND, not the name. *`W16`
    // shape and it is named in `messung/DOMAENENSTELLUNGEN.md`, not closed here.*
    if st == Stellung::Durchlauf {
        return;
    }
    let Some(o) = ort_der_domaene(d) else { return };
    let n = &o.basis;
    // **`Self` is the CARRIER question, and `M120` in `m1.rs` owns it.** Saying "is not
    // declared here" about `Self` sends the reader off to declare a word the language does
    // not let him declare -- the exact refusal `M120` was built to replace.
    if n.text == "Self" {
        return;
    }
    if geb.contains(&n.text) || s.lokal.contains_key(&n.text) {
        return;
    }
    if s.u.suche_global(s.modul, &n.text).is_some() {
        return;
    }
    if s.u.nennt_typ_oder_konstante(s.modul, &n.text)
        || s.u.nennt_tabelle(s.modul, &n.text).is_some()
        || s.u.nennt_walk(s.modul, &n.text)
        || s.u.nennt_kopf(s.modul, &n.text)
    {
        return;
    }
    absagen.schiebe(
        Absage::fehler(
            "D017",
            n.span,
            format!(
                "`{}` in {} is not declared here",
                n.text,
                st.wort()
            ),
        )
        .mit_notiz(
            "a quantifier whose place does not resolve quantifies over nothing -- it stands \
             in the certificate and in the library ABI and says nothing. `M109` says the \
             same sentence in `ensures`",
        ),
    );
}

/// What KIND of place is this -- as far as the environment actually knows.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ortsart {
    Tabelle,
    /// `index into T` / `option index into T` -- it names its table in the type.
    Index,
    Verbund,
    Feldarray,
    Walk,
    /// A `format` or `device` head.
    Kopf,
    Skalar,
}

impl Ortsart {
    fn benennung(self) -> &'static str {
        match self {
            Ortsart::Tabelle => "a table",
            Ortsart::Index => "an index into a table",
            Ortsart::Verbund => "a record",
            Ortsart::Feldarray => "an array",
            Ortsart::Walk => "a `walk`",
            Ortsart::Kopf => "a `format`",
            Ortsart::Skalar => "a scalar",
        }
    }
}

/// **`D018` -- the place is of the kind the DOMAIN needs.**
///
/// Seven domains, four questions, and `None` from the classifier always means silence.
fn ortstyp_pruefen(d: &Domaene, s: &Sicht, geb: &[String], absagen: &mut Absagen) {
    let (o, form, erlaubt, verlangt): (&Ort, &str, &[Ortsart], &str) = match d {
        Domaene::SlotsVon(o) => (
            o,
            "slots of",
            &[Ortsart::Tabelle, Ortsart::Index],
            "a table",
        ),
        Domaene::Schlange(o) => (o, "queue", &[Ortsart::Verbund], "a record"),
        Domaene::ElementeVon(o) => (o, "elems of", &[Ortsart::Feldarray], "an array field"),
        Domaene::AbbildungenVon(o) => (o, "mappings of", &[Ortsart::Walk], "a `walk`"),
        // The three that walk the tree take a SLOT -- and a slot is written `<x>.slots[i]`,
        // which is a shape and not a type. `ist_slotform` decides it below; a whole table
        // and a bare `index into T` are the two other forms the corpus writes.
        Domaene::NachfahrenVon(o) => (
            o,
            "descendants of",
            &[Ortsart::Tabelle, Ortsart::Index],
            "a slot of a table",
        ),
        Domaene::VorfahrenVon(o) => (
            o,
            "ancestors of",
            &[Ortsart::Tabelle, Ortsart::Index],
            "a slot of a table",
        ),
        Domaene::KetteIn { ort, .. } => (
            ort,
            "chain(a, b) in",
            &[Ortsart::Tabelle, Ortsart::Index],
            "a slot of a table",
        ),
        // **Not built, and named instead** (`messung/DOMAENENSTELLUNGEN.md`): `fields of`
        // carries a path and has zero corpus sites -- Regel A, there is no subject that
        // measures the need. `threads` names nothing (`Q3`).
        Domaene::FelderVon(_) | Domaene::Threads => return,
    };
    let laeuft_im_baum = matches!(
        d,
        Domaene::NachfahrenVon(_) | Domaene::VorfahrenVon(_) | Domaene::KetteIn { .. }
    );
    if laeuft_im_baum && s.ist_slotform(o) {
        return;
    }
    let Some(art) = s.ortsart(o, geb) else { return };
    if erlaubt.contains(&art) {
        return;
    }
    absagen.schiebe(
        Absage::fehler(
            "D018",
            o.span,
            format!(
                "`{form} {}` needs {verlangt}, and `{}` is {}",
                kurzform(o),
                kurzform(o),
                art.benennung()
            ),
        )
        .mit_notiz(
            "the DOMAIN decides what its place must be -- `slots of` a table, `queue` a \
             record, `elems of` an array field, `mappings of` a `walk`, and the three that \
             walk the tree a slot. A quantifier over a place of another kind ranges over \
             nothing the language can name",
        ),
    );
}

/// The place, as far as a message should repeat it -- base plus its written suffixes.
fn kurzform(o: &Ort) -> String {
    let mut t = o.basis.text.clone();
    for su in &o.suffixe {
        match su {
            OrtSuffix::Feld(f) => {
                t.push('.');
                t.push_str(&f.text);
            }
            OrtSuffix::Ueber(f) => {
                t.push_str("->");
                t.push_str(&f.text);
            }
            OrtSuffix::Index(_) => t.push_str("[…]"),
        }
    }
    t
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

    /// **Is the place written as a SLOT of a table** -- `<base>.slots[i]`?
    ///
    /// A shape and not a type: the type of `c.slots[s]` is a `Verbund` and has lost the
    /// name of the table it came out of (`umgebung.rs::feld_von`). *`D018` asks the shape
    /// so that a slot is not mistaken for a plain record.*
    ///
    /// The base is accepted three ways -- a table type, an `index into T`, and the BARE
    /// declaration name (`descendants of Kappenraum.slots[s]` stands in the corpus, and a
    /// declaration name is no value, so it is not in `globale`).
    fn ist_slotform(&self, o: &Ort) -> bool {
        let [OrtSuffix::Feld(f), OrtSuffix::Index(_)] = o.suffixe.as_slice() else {
            return false;
        };
        if f.text != "slots" {
            return false;
        }
        let basis = Ort {
            basis: o.basis.clone(),
            suffixe: Vec::new(),
            span: o.span,
        };
        self.tabellenname(&basis).is_some() || self.benannte_deklaration(&o.basis.text) == Some(Ortsart::Tabelle)
    }

    /// The kind of a place -- **and `None` means *stay silent*, which is the whole
    /// discipline of `D018`.**
    ///
    /// A place whose type does not resolve is not a place of the wrong kind. Sum types,
    /// device registers, reasons and function pointers land here too: none of them is a
    /// domain carrier, but refusing them would be a refusal this bench has not measured.
    fn ortsart(&self, o: &Ort, gebunden: &[String]) -> Option<Ortsart> {
        // A quantifier variable carries no type in this pass -- `mappings of w` binds `m`
        // to a page-table entry, and an inner domain over `m.feld` must not be guessed at.
        if gebunden.contains(&o.basis.text) {
            return None;
        }
        let t = self.u.typ_von_ort(self.modul, o, self.lokal);
        // **`index into T` is the NAME of a `Benannt`**, so it has to be read before
        // `durchgreifen` looks past it -- the same move `tabellenname` makes above.
        if let Typ::Benannt { name, .. } = &t {
            if name.starts_with("index into ") || name.starts_with("option index into ") {
                return Some(Ortsart::Index);
            }
        }
        let art = match t.durchgreifen() {
            Typ::Tabelle(_) => Some(Ortsart::Tabelle),
            // A `walk` head and a `format` head are the same type constructor; `walknamen`
            // is what tells them apart (`umgebung.rs`, 2026-08-31).
            Typ::Verbundname(n) => Some(if self.u.walknamen.contains(n) {
                Ortsart::Walk
            } else {
                Ortsart::Kopf
            }),
            Typ::Verbund(_) => Some(Ortsart::Verbund),
            Typ::Feld { .. } => Some(Ortsart::Feldarray),
            Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Gleitkomma(_) | Typ::Wahrheit => {
                Some(Ortsart::Skalar)
            }
            _ => None,
        };
        if art.is_some() {
            return art;
        }
        // **A bare DECLARATION name is not a value and therefore not in `globale`.**
        // `forall s in slots of Kappenraum` and `forall m in mappings of Inodebaum` name
        // the carrier itself -- seventeen of the 53 corpus places are of that shape, and
        // without this step every one of them would be `Unbekannt`.
        if !o.suffixe.is_empty() {
            return None;
        }
        self.benannte_deklaration(&o.basis.text)
    }

    fn benannte_deklaration(&self, name: &str) -> Option<Ortsart> {
        if self.u.nennt_tabelle(self.modul, name).is_some() {
            return Some(Ortsart::Tabelle);
        }
        if self.u.nennt_walk(self.modul, name) {
            return Some(Ortsart::Walk);
        }
        if self.u.nennt_kopf(self.modul, name) {
            return Some(Ortsart::Kopf);
        }
        None
    }
}
