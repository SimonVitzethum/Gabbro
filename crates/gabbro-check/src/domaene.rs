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
    Block, Domaene, Expr, ExprArt, FnRumpf, Ident, Item, ItemArt, Ort, OrtSuffix, Pred, PredArt,
    Programm, Schleife, StmtArt,
};
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{HashMap, HashSet};

use crate::typen::Typ;
use crate::umgebung::{modul_von, Feldurteil, Umgebung};

pub struct Sicht<'a> {
    pub u: &'a Umgebung,
    pub modul: &'a str,
    pub lokal: &'a HashMap<String, Typ>,
}

impl<'a> Sicht<'a> {
    /// **The `walk` a `mappings of` place stands for -- qualified and bare.**
    ///
    /// The place names the PARAMETER (`mappings of w`), not the walk; the name comes out of
    /// the type, the way it does for tables. `Self` inside the declaration falls through to
    /// the base name, which is then the walk's own name.
    ///
    /// *Extracted on 2026-09-01 because a second reader appeared:* `domaenenschranke` asks
    /// for the leaf COUNT, `D020` for the node FORMAT, and both start from this one
    /// resolution. **Two readers of one lookup, written once** -- the rule this file's own
    /// head paragraph states about `kosten.rs` and `m1.rs`.
    fn walkname(&self, o: &Ort) -> (String, String) {
        let name = match self.u.typ_von_ort(self.modul, o, self.lokal).durchgreifen() {
            Typ::Benannt { name, .. } => name.clone(),
            Typ::Verbundname(n) => n.clone(),
            _ => o.basis.text.clone(),
        };
        let kurz = name.rsplit("::").next().unwrap_or(&name).to_string();
        (name, kurz)
    }

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
                let (name, kurz) = self.walkname(o);
                return self
                    .u
                    .walkschranken
                    .iter()
                    .find(|(k, _)| *k == &name || k.rsplit("::").next() == Some(kurz.as_str()))
                    .map(|(_, n)| *n as i128);
            }
            // **The three domains that carry NO bound out of the declaration, spelled out**
            // *(2026-08-31)*. They stood on a `_ => return None` -- the honest answer, but
            // an invisible one: nothing in this file said which domains it was about, and
            // the certificate covered all five non-tree forms with one word. Naming them
            // makes the gap countable, and it makes a TENTH domain a translation error here
            // instead of a silent `K003` -- that refusal lives in `kosten.rs`, which asks
            // this function and passes the silence on.
            //
            //   `chain(a, b) in`  the chain ends because its edge is `option index into T`
            //                     -- an END is not a LENGTH
            //   `fields of`       finitely many and statically known, but no length is
            //                     written down
            //   `threads`         how many there are is a statement about the MACHINE
            Domaene::KetteIn { .. } | Domaene::FelderVon(_) | Domaene::Threads => return None,
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
    /// **Four positions this walk did not reach until 2026-09-02**, and each was measured
    /// silent in all twenty name kinds before it was hooked up
    /// (`messung/PREDICATE-NAMES.md`): the `floor` of a `check`, the `down` and `leaf` of a
    /// `walk`, the `when` of a compare-exchange, and the `requires` of an `axiom` -- which
    /// takes `Vorbedingung`, because it is one.
    Untergrenze,
    Walkschritt,
    Tausch,
}

impl Stellung {
    fn wort(self) -> &'static str {
        match self {
            Stellung::Nachbedingung => "`ensures`",
            Stellung::Vorbedingung => "`requires`",
            Stellung::Invariante => "an `invariant`",
            Stellung::Spezifikation => "the body of a `spec fn`",
            Stellung::Durchlauf => "a `traverse`",
            Stellung::Untergrenze => "a `floor`",
            Stellung::Walkschritt => "the step of a `walk`",
            Stellung::Tausch => "the `when` of an exchange",
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
            // **`down … when` and `leaf` are predicates, and until 2026-09-02 no pass of
            // this file came here.** All twenty name kinds were accepted in both.
            //
            // `it` is the ELEMENT of the node array; the declaration binds it and no other
            // line does. It goes on `geb` and not into the map, the same treatment a
            // quantifier variable gets: the pass knows the name is bound and nothing about
            // its type, and guessing one would be `D018` speaking about a guess.
            geb.push("it".to_string());
            aus_pred(&w.ab_wenn, &s, Stellung::Walkschritt, &mut geb, absagen);
            aus_pred(&w.blatt, &s, Stellung::Walkschritt, &mut geb, absagen);
            geb.pop();
        }
        // **The assumption tier, and it is the position with the most weight.** A
        // `requires` at an `axiom` is what the whole relative claim rests on -- *"proved
        // under A1…An"* -- and it was read here by nobody: twenty of twenty name kinds
        // accepted. Its parameters are its local view, exactly as at a function.
        ItemArt::Axiom(a) => {
            let mut lokal: HashMap<String, Typ> = HashMap::new();
            for p in &a.parameter {
                lokal.insert(p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ));
            }
            let s = Sicht { u, modul, lokal: &lokal };
            let mut geb = Vec::new();
            for p in &a.requires {
                aus_pred(p, &s, Stellung::Vorbedingung, &mut geb, absagen);
            }
        }
        // **A `check … floor` names quantities, and nothing said they exist.** `N022` in
        // `namen.rs` asks
        // whether the floor covers what `measures` names one-sidedly; put a phantom name
        // beside a legitimate conjunct and it goes silent, which is what made it look like
        // a reader and what it is not. The `can_fail` block is an ordinary body.
        ItemArt::Check(c) => {
            let lokal: HashMap<String, Typ> = HashMap::new();
            let s = Sicht { u, modul, lokal: &lokal };
            let mut geb = Vec::new();
            for p in &c.floor {
                aus_pred(p, &s, Stellung::Untergrenze, &mut geb, absagen);
            }
            aus_block(&c.can_fail, &s, &mut geb, absagen);
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

/// **The block scope -- the second half of the 2026-08-31 finding.**
///
/// Until then this walk carried ONLY the parameters, and a `let` in an inner block was
/// invisible. Where it shadows a parameter, `ortsart` asks the type of the PARAMETER -- and
/// `D018` then says *"`slots of t` needs a table, and `t` is a scalar"* about a program in
/// which `t` IS a table at that point. **A false refusal from the same root as the wrong
/// cost number in `kosten.rs`.**
///
/// The value stands in the OLD scope, so the check runs first and the name is bound after.
///
/// ## Two more binders, measured 2026-08-31 and both a FALSE REFUSAL
///
/// The scope above was built for `let`, and two other statements declare a name that no
/// `let` writes down: **the traversal variable** and **the binder of a `match` arm**. The
/// first was pushed around the loop's own `invariant` and popped again before the body was
/// walked; the second was never pushed at all. In both cases a domain deeper inside names
/// something the enclosing line just introduced -- and `D017` says it *"is not declared
/// here"*:
///
/// ```text
/// traverse a of g over ancestors of g {
///     traverse b of g over ancestors of g
///         invariant forall k in descendants of a : …      -> [D017] `a` … not declared
/// ```
///
/// ```text
/// match x { Knoten(k) => {
///     traverse a of g over ancestors of g
///         invariant forall z in descendants of k : …      -> [D017] `k` … not declared
/// ```
///
/// Both fall against the UNCHANGED checker; moving the same `invariant` up to the line that
/// binds the name gives `0 errors`. *A refusal about a name the program declares is a
/// refusal about the pass.*
///
/// **The name goes on `geb`, not into `karte`** -- the same treatment a quantifier variable
/// gets, and for the same reason: the pass knows the name is bound and knows nothing about
/// its type, so `ortsart` returns `None` and every rule here stays silent about it. Binding
/// it to a TYPE would be a guess, and `m1.rs` writes `Typ::Unbekannt` at the same spot.
///
/// **And it is popped again.** A domain AFTER the loop that names the traversal variable
/// still falls -- the scope ends with the block, and a version that merely stopped refusing
/// would look exactly like this one from the inside.
fn aus_block(b: &Block, aussen: &Sicht, geb: &mut Vec<String>, absagen: &mut Absagen) {
    let mut karte = aussen.lokal.clone();
    for st in &b.anweisungen {
        let s = &Sicht { u: aussen.u, modul: aussen.modul, lokal: &karte };
        // How many names THIS statement declares for its own sub-blocks -- popped below.
        let mut gebunden = 0usize;
        if let StmtArt::Schleife(sch) = &st.art {
            // **No `_` arm.** All three loop kinds carry an `invariant`, and a fourth one
            // should be a compile error here rather than a silent hole.
            match sch.as_ref() {
                Schleife::Traverse(t) => {
                    // The domain is read in the OUTER scope: `traverse i over slots of i`
                    // must not resolve against the name the same line introduces.
                    domaene_pruefen(&t.domaene, s, Stellung::Durchlauf, geb, absagen);
                    // The traversal variable is DECLARED by the loop -- a domain in the
                    // invariant OR IN THE BODY that names it must not count as unresolved.
                    geb.push(t.variable.text.clone());
                    gebunden += 1;
                    if let Some(p) = &t.invariante {
                        aus_pred(p, s, Stellung::Invariante, geb, absagen);
                    }
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
        // **The `when` of a compare-exchange, and it RUNS.** `lib.rs::eigene_praedikate`
        // says so in its own head since 2026-09-02; this file did not read it either, and
        // sixteen of twenty name kinds went through. The binder of the exchange is declared
        // by the statement and is not in scope in its own condition -- `binde` puts it into
        // the map below, after the check, the same order a `let` gets.
        if let StmtArt::Exchange(x) = &st.art {
            if let gabbro_syntax::ast::XForm::Vergleich { bedingung, .. } = &x.form {
                aus_pred(bedingung, s, Stellung::Tausch, geb, absagen);
            }
        }
        // **A `match` is walked HERE and not through `unterbloecke`**, because each arm
        // carries its OWN binder and a shared walk cannot tell them apart. `Nichts` binds
        // nothing, `Knoten(k)` binds `k`, and neither name reaches the other arm.
        if let StmtArt::Match(m) = &st.art {
            for z in &m.zweige {
                if let Some(bi) = &z.binder {
                    geb.push(bi.text.clone());
                }
                aus_block(&z.rumpf, s, geb, absagen);
                if z.binder.is_some() {
                    geb.pop();
                }
            }
        } else {
            for k in crate::unterbloecke(st) {
                aus_block(k, s, geb, absagen);
            }
        }
        for _ in 0..gebunden {
            geb.pop();
        }
        binde(st, &mut karte, aussen.u, aussen.modul);
    }
}

/// What a statement leaves behind in NAMES -- the same question `kosten.rs::binde` asks,
/// and the same answer: what cannot be read here becomes `Unbekannt` rather than being
/// passed over. **`ortsart` stays silent about `Unbekannt`**, and silence is the answer
/// `D018` gives everywhere it knows nothing.
fn binde(st: &gabbro_syntax::ast::Stmt, karte: &mut HashMap<String, Typ>, u: &Umgebung, modul: &str) {
    match &st.art {
        StmtArt::Let(l) => {
            let t = match (&l.typ, &l.wert.art) {
                (Some(td), _) => u.typ_von_ausdruck_decl(modul, td),
                (None, gabbro_syntax::ast::ExprArt::Ort(o)) => u.typ_von_ort(modul, o, karte),
                _ => Typ::Unbekannt,
            };
            karte.insert(l.name.text.clone(), t);
        }
        StmtArt::LetSonst(l) => {
            karte.insert(l.name.text.clone(), Typ::Unbekannt);
        }
        StmtArt::AwaitLoad(a) => {
            let t = u.typ_von_ort(modul, &a.quelle, karte);
            karte.insert(a.name.text.clone(), t);
        }
        StmtArt::Exchange(e) => {
            karte.insert(e.name.text.clone(), Typ::Unbekannt);
        }
        _ => {}
    }
}

fn aus_pred(p: &Pred, s: &Sicht, st: Stellung, geb: &mut Vec<String>, absagen: &mut Absagen) {
    match &p.art {
        PredArt::Quantor(q) => {
            domaene_pruefen(&q.domaene, s, st, geb, absagen);
            abbildungsfelder_pruefen(q, s, absagen);
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
        //
        // They carry PLACES, though, and `M141` reads the literal index of each.
        PredArt::Vergleich(e) => {
            let frei = merkmalsnamen(e);
            for o in crate::alle_orte(e) {
                indexschranke_pruefen(o, s, st, absagen);
                grundname_im_praedikat(o, s, st, geb, &frei, absagen);
            }
        }
        // **`expr in domain` produces a DOMAIN too, and this arm did not read it**
        // (measured 2026-09-02). The grammar has exactly two producers of `domain` --
        // `quant` above and `member` here -- and the rule was built for one of them:
        // `requires i in slots of GIBTSNICHT` gave `0 errors`, while the same words under
        // a `forall` fall at `D017`. *A form without a reader is not neutral; it is a
        // hole* -- the sentence `ast.rs` writes over `FnZeiger`.
        //
        // It binds no variable, so `geb` travels unchanged.
        PredArt::Element(e, d) => {
            domaene_pruefen(d, s, st, geb, absagen);
            let frei = merkmalsnamen(e);
            for o in crate::alle_orte(e) {
                indexschranke_pruefen(o, s, st, absagen);
                grundname_im_praedikat(o, s, st, geb, &frei, absagen);
            }
        }
        PredArt::Erreicht { von, nach, .. } => {
            let frei = HashSet::new();
            indexschranke_pruefen(von, s, st, absagen);
            indexschranke_pruefen(nach, s, st, absagen);
            grundname_im_praedikat(von, s, st, geb, &frei, absagen);
            grundname_im_praedikat(nach, s, st, geb, &frei, absagen);
        }
        // `Held(L)` and `Held(L, shared)` name a LOCK and nothing else.
        PredArt::Held { .. } => {}
    }
}

/// **`D021` -- the base name of a place in a PREDICATE resolves.**
///
/// `M109` in `m1.rs` asks this of an `ensures` and of nothing else; `N053` in `namen.rs`
/// asks it of a device promise; `N032` asks it of a `format … where`. **Sixteen of the
/// nineteen predicate positions the grammar has asked it of nobody**, and that was measured
/// position by position before this rule was written (`messung/PREDICATE-NAMES.md`):
///
/// ```text
/// requires gibt_es_nicht(s) == 0   ->  0 errors, 3 hints [E009]   Lean: DROPPED
/// requires GIBTESNICHT == 1        ->  0 errors, 0 hints          Lean: EXPORTED
/// ```
///
/// The two lines are the same fault and the second is the worse one. **A dropped conjunct is
/// visible; an exported one over a name that exists nowhere is not.** `gabbro lean` writes
///
/// ```lean
/// ∧ eval s (.bin .eq (.global "GIBTESNICHT") (.lit (.int 1))) = some (.bool true)
/// ```
///
/// into `<fn>_pre`, *"what the caller grants"*, and `Gabbro.Body` reads `.global` out of a
/// TOTAL store -- so the premise is not vacuous, it is satisfiable, and a proof that leans
/// on it has proved something about a state no program can be in. **That is not a missing
/// finding but a wrong proof object**, and it is the sixth class of `PLAN.md` in pure form:
/// a sentence is proved and nothing establishes its premise.
///
/// ## What it does NOT do, and why each exemption is there
///
/// A predicate legitimately names things a body cannot, and a resolver that started
/// refusing those would break correct programs. Each of these is forced by a corpus file:
///
/// * **`result` and a reason case are not places at all** -- `ExprArt::Ergebnis` and
///   `ExprArt::Grund` are their own variants, and `alle_orte` does not yield them.
/// * **`old(x)`** IS a place (`ExprArt::Alt`) and its name has to exist: a postcondition
///   about the old value of nothing is none. `M109` says the same in `ensures`.
/// * **A quantifier variable, a `traverse` variable and a `match` binder** stand in `geb`,
///   which `aus_pred` and `aus_block` maintain for `D017` already.
/// * **`Self`** belongs to `M120`, which names the place the line belongs to instead of
///   sending the reader off to declare a word the language does not let him declare.
/// * **`ensures`** belongs to `M109`, and a second refusal for one fault is worse than one.
/// * **The argument of `Has(…)` and of `Held(…)`** is not a place. A machine feature is not
///   a program name and a lock is not a value; both are spelled as a call, and both would
///   otherwise be read as one. `beispiele/01-tabelle.gab` writes `Held(KAPPEN)` at every
///   `impl fn` in the file, and `beispiele/11-grammatikbefunde.gab` writes `Has(RDTSCP)`.
///
/// > **The exemption is by NAME and not by site**, exactly as `namen.rs::zusagenstelle`
/// > does it: a predicate that writes `Has(F)` and `F.x == 1` in one breath exempts `F` in
/// > both. That is coarse, and it is coarse in the quiet direction.
///
/// The resolution itself is `D017`'s, word for word -- parameter or local, global, a
/// resolvable type or constant, a `table`, a `walk`, a `format`/`device` head. *A wider
/// resolution can only make this rule quieter, and quiet is the safe direction.*
fn grundname_im_praedikat(
    o: &Ort,
    s: &Sicht,
    st: Stellung,
    geb: &[String],
    frei: &HashSet<String>,
    absagen: &mut Absagen,
) {
    // **The three lines below are spelled differently from `grundname_pruefen`'s on
    // purpose.** Two mutations of `mutiere-pruefer.py` anchor on that function's literal
    // source, and a second byte-identical copy makes each anchor AMBIGUOUS -- `--anker`
    // reported exactly that on the day this rule was written, and an ambiguous anchor
    // measures nothing. *Two rules that ask the same question are still two rules.*
    //
    // `ensures` has a reader -- `M109` in `m1.rs` resolves EVERY name of a postcondition.
    if matches!(st, Stellung::Nachbedingung) {
        return;
    }
    let n = &o.basis;
    if n.text == "Self" || frei.contains(&n.text) {
        return;
    }
    let gebunden = geb.contains(&n.text) || s.lokal.contains_key(&n.text);
    if gebunden || s.u.suche_global(s.modul, &n.text).is_some() {
        return;
    }
    if s.u.nennt_typ_oder_konstante(s.modul, &n.text)
        || s.u.nennt_tabelle(s.modul, &n.text).is_some()
        || s.u.nennt_walk(s.modul, &n.text)
        || s.u.nennt_kopf(s.modul, &n.text)
    {
        return;
    }
    // **A REGISTER of a device, and this one is measured rather than guessed.**
    // `messung/fragmente/F09.gab`:72 writes `down : roh when EINTRAG.PS == 0`, and
    // `EINTRAG` is a `reg` of `device Seitentabelle` in the same unit -- declared, and
    // named by none of the four maps above, which carry device HEADS and not their
    // registers. *A refusal about a name the program declares is a refusal about the pass*,
    // the sentence this file already writes one rule up.
    //
    // Whether a walk step may reach for a device register at all is a different question
    // and belongs to whoever owns the walk lowering; **this rule asks only whether the name
    // exists**, and it does. The lookup is over every device of the unit and not over the
    // one in scope, which is coarse in the quiet direction.
    if s
        .u
        .geraete
        .values()
        .any(|register| register.iter().any(|(r, _)| *r == n.text))
    {
        return;
    }
    absagen.schiebe(
        Absage::fehler(
            "D021",
            n.span,
            format!("`{}` in {} is not declared here", n.text, st.wort()),
        )
        .mit_notiz(
            "this compiler hands a predicate on as an ASSUMPTION -- `gabbro lean` writes a \
             `requires` into `<fn>_pre`, \"what the caller grants\". A conjunct over a name \
             nothing declares is not a missing check but a WRONG PROOF OBJECT: the prover \
             carries a premise whose referent exists nowhere, and unlike a dropped conjunct \
             that is visible in no channel",
        )
        .mit_notiz(
            "`M109` says the same sentence in `ensures`, `N053` at a device promise and \
             `N032` in a `format … where` -- this is the same question in the sixteen \
             positions that had no reader",
        ),
    );
}

/// The names a predicate expression spells as a CALL but does not mean as a place:
/// `Has(F)` names a machine feature, `Held(L)` and `Held(L, shared)` name a lock.
///
/// **Both are pseudo-calls in the grammar of an expression**, so `alle_orte` yields their
/// arguments like any other place. `Held` additionally becomes an ordinary call the moment
/// brackets stand around it (`(Held(L))` parses as `PredArt::Klammer` over a comparison, not
/// as `PredArt::Held`) -- measured 2026-09-02, and the reason this collector reads the
/// expression form rather than trusting the predicate form.
fn merkmalsnamen(e: &Expr) -> HashSet<String> {
    let mut aus = HashSet::new();
    for x in crate::alle_ausdruecke(e) {
        let ExprArt::Ruf(r) = &x.art else { continue };
        if !r.heisst("Has") && !r.heisst("Held") {
            continue;
        }
        for a in &r.argumente {
            if let ExprArt::Ort(o) = &crate::ohne_klammern(a).art {
                aus.insert(o.basis.text.clone());
            }
        }
    }
    aus
}

/// **`M141` -- a LITERAL index in a PREDICATE, held against the declaration of the carrier.**
///
/// `m1.rs` says of itself, in its own head -- the German original is at the top of that
/// file: *it checks bodies and not predicates; `requires`, `ensures` and `invariant` are
/// ghost expressions with no run-time effect, and they belong to the PROVER, not to M1.*
/// **The second half of that sentence is what this rule
/// is about**, and it was measured on 2026-09-02 rather than assumed:
///
/// ```text
/// impl fn f() -> bool requires T.slots[9].x == 0 …    -- `table T count 8`.  0 errors.
/// ```
///
/// and `gabbro lean` over the same file writes
///
/// ```lean
/// /-- `f` -- what the caller grants: the declared parameter shapes and the
///     `requires` this channel can say. -/
/// def f_pre (s : State) : Prop :=
///   eval s (.bin .eq (.place "T" (.lit (.int 9)) "x") (.lit (.int 0))) = some (.bool true)
/// ```
///
/// `Gabbro.Body`'s world is a TOTAL map over `slot (carrier) (index : Int) (field)`, and
/// `wellFormed` quantifies over every `k` -- so `f_pre` is not vacuous but *satisfiable*, a
/// premise about a cell no Gabbro program can address. **The prover does not check what the
/// checker declined to look at; it assumes it.** That is the sixth class in pure form
/// (`PLAN.md`): *a sentence is proved, and nothing establishes its premise.*
///
/// ## The limit is in the code, not in a footnote
///
/// **Only a NUMBER LITERAL is compared, and only against a length the declaration writes
/// down.** A computed index stays silent -- `W10`, a lower bound neither refuses nor
/// confirms -- and so does a quantifier variable, which is exactly the form the corpus
/// writes (`forall s in slots of Self : Self.slots[s].a == 0`). *A rule that started
/// refusing those would break correct programs, and the counter-direction of its test says
/// so.* The same limit `namen.rs` draws at `N009` for a register offset, one construct
/// further.
///
/// ## Why it stands HERE and not in `m1.rs`
///
/// This file already carries the exhaustive walk over the predicate POSITIONS -- `requires`,
/// `ensures`, a `spec fn` body, the invariants of a `table`, a `walk`, a `group` and all
/// three loops -- and `m1.rs` calls it (`domaenen`, one line into pass 3). **Copying that
/// walk into `m1.rs` would be the second register over one matter**, the class this folder's
/// own head paragraph writes against. What is shared is the walk; the rule is new.
fn indexschranke_pruefen(o: &Ort, s: &Sicht, st: Stellung, absagen: &mut Absagen) {
    let mut praefix = Ort {
        basis: o.basis.clone(),
        suffixe: Vec::new(),
        span: o.span,
    };
    for suffix in &o.suffixe {
        if let OrtSuffix::Index(e) = suffix {
            if let gabbro_syntax::ast::ExprArt::Zahl(v) = &crate::ohne_klammern(e).art {
                if let Typ::Feld { laenge: Some(n), .. } =
                    s.u.typ_von_ort(s.modul, &praefix, s.lokal).durchgreifen()
                {
                    if *v >= *n {
                        absagen.schiebe(
                            Absage::fehler(
                                "M141",
                                e.span,
                                format!(
                                    "in {}: the index is {v}, and `{}` has {n} elements",
                                    st.wort(),
                                    praefix.text(),
                                ),
                            )
                            .mit_notiz(
                                "M4: no unchecked indexing -- the bound comes from the \
                                 declaration of the carrier, and a predicate is not exempt",
                            )
                            .mit_notiz(
                                "a `requires` leaves this compiler as an ASSUMPTION (`gabbro \
                                 lean` writes it as `<fn>_pre`, \"what the caller grants\") -- \
                                 a grant over a slot that does not exist is a premise \
                                 nothing can establish",
                            ),
                        );
                    }
                }
            }
        }
        praefix.suffixe.push(suffix.clone());
    }
}

/// **`D020` -- the FIELD names of a bound MAPPING resolve.**
///
/// The fourth question at a quantifier, and the first one about the VARIABLE rather than the
/// place: `D017` reads the base name, `D018` its kind, `D019` the field names of its suffix
/// -- and all three stop at the place. `mappings of` is **the one domain that binds a record**
/// (`SPRACHE.md` §6: *"A domain binds the ADDRESS of an entry … `mappings of` is the one
/// exception"*), so it is the one domain where `m.field` means anything at all, and the one
/// where nobody read it.
///
/// **Measured 2026-09-01 against the UNCHANGED checker.** A `walk` over `[Pte; 512]` with
///
/// ```gabbro
/// invariant erfundenes_feld cost O(n) runs online :
///     forall m in mappings of Self : !m.gibtsnicht;
/// ```
///
/// gave `3 items, 0 errors, 0 hints` -- **`Pte` has no field of that name and no pass said
/// so.** The control in the same run: falsifying the BASE name (`mappings of GibtsNicht`)
/// does fall, at `D017`. *The base is read and the variable's field is not* -- word for word
/// the sentence `D019` says one level down, and the reason is the same: `ortsfelder_pruefen`
/// **returns early on a bound name**, because a quantifier variable carries no type in that
/// pass. For `mappings of` the type is not a guess: it stands in the `walk` declaration.
///
/// ## Two families, and the second one is the whole point of Layer 2
///
/// A mapping carries the fields of the node `format` (`walkknoten`) **and** three the domain
/// synthesises from the position -- `SPRACHE.md`:930, *"including virtual address and level"*.
/// The distinction is not cosmetic: an invariant that reads only entry fields is preserved by
/// grafting a subtree anywhere, and one that reads `va` is not. **`PLAN-HARDWARE.md` §5
/// Layer 2 rests on exactly this split, and without this pass nothing in the tree could make
/// it.**
///
/// ## Silent wherever the walk did not resolve
///
/// Same discipline as `D019`: no `walk` name, no node `format`, no field list -- no refusal.
/// A rule that says nothing about an unknown carrier says nothing at all.
///
/// **And that is a different sentence from "no field list because the lookup was not
/// module-aware"** (2026-09-03, `zaehle-karten.py`). `walkknoten` carries the node type's RAW
/// name; resolving it against `formate` goes through `suche_formate`, from the `walk`'s OWN
/// module outward -- the same candidate order `suche_global` and `funktion` already use. A
/// direct `.get(&knoten)` here only ever hit a `format` declared in the exact same module as
/// the `walk`; one enclosing module apart and `D020`'s own poison (`!m.gibtsnicht`) passed
/// with `0 errors, 0 hints` again -- word for word the finding this map was BUILT to close.
fn abbildungsfelder_pruefen(q: &gabbro_syntax::ast::Quantor, s: &Sicht, absagen: &mut Absagen) {
    let Domaene::AbbildungenVon(o) = &q.domaene else { return };
    let (name, kurz) = s.walkname(o);
    let Some(knoten) = s
        .u
        .walkknoten
        .iter()
        .find(|(k, _)| *k == &name || k.rsplit("::").next() == Some(kurz.as_str()))
        .map(|(_, v)| v.clone())
    else {
        return;
    };
    let Some(felder) = s.u.suche_formate(modul_von(&name), &knoten) else {
        return;
    };
    let v = &q.variable.text;
    let mut orte = Vec::new();
    pred_orte(&q.rumpf, v, &mut orte);
    for ort in orte {
        if &ort.basis.text != v {
            continue;
        }
        let Some(OrtSuffix::Feld(f) | OrtSuffix::Ueber(f)) = ort.suffixe.first() else {
            continue;
        };
        if STELLUNGSFELDER.contains(&f.text.as_str())
            || felder.iter().any(|(n, _)| n == &f.text)
        {
            continue;
        }
        let hat: Vec<&str> = STELLUNGSFELDER
            .iter()
            .copied()
            .chain(felder.iter().map(|(n, _)| n.as_str()))
            .collect();
        absagen.schiebe(
            Absage::fehler(
                "D020",
                f.span,
                format!("`{v}.{}` is not a field of a mapping", f.text),
            )
            .mit_notiz(format!(
                "`mappings of` binds a leaf entry of `{}` together with its position -- a \
                 quantifier over a field that stands nowhere ranges over nothing, and it \
                 stands in the certificate and in the library ABI. `D019` says the same \
                 sentence about the field names of the PLACE",
                kurz
            ))
            .mit_notiz(format!("it has: {}", hat.join(", "))),
        );
    }
}

/// **The three fields a mapping carries that the node `format` does not.**
///
/// They come from the POSITION, not from the entry -- `SPRACHE.md`:930, *"quantifies over all
/// reachable leaf entries of a `walk` structure, including virtual address and level"*, and
/// `messung/fragmente/F09.gab`:67, *"per mapping `va`, `level` and `index[level]` stand
/// ready"*. **A predicate that reads one of these is PATH-DEPENDENT**, and that is the
/// property `PLAN-HARDWARE.md` §5 Layer 2 turns on: an entry write moves them, a graft
/// re-derives them, and no bit of the table has to change for that to happen.
const STELLUNGSFELDER: &[&str] = &["va", "level", "index"];

/// Every place a predicate mentions under the name `v` -- the walker `alle_orte` performs
/// over an EXPRESSION, lifted to the predicate forms that hold one.
///
/// **It stops at an inner quantifier that REBINDS `v`.** Nesting is at most two
/// (`SPRACHE.md` §6), so `forall m in mappings of Self : exists m in slots of k : …` is
/// writable, and there the inner `m` is a table index with no fields of the walk's node
/// `format` at all. *A rule that refused it would refuse the name the inner line just
/// introduced* -- the same shadowing question `aus_pred` answers with its `geb` stack, and
/// the same sentence `grundname_pruefen` writes about a bound base name.
fn pred_orte<'p>(p: &'p Pred, v: &str, aus: &mut Vec<&'p Ort>) {
    match &p.art {
        PredArt::Vergleich(e) => aus.extend(crate::alle_orte(e)),
        PredArt::Element(e, _) => aus.extend(crate::alle_orte(e)),
        PredArt::Erreicht { von, nach, .. } => {
            aus.push(von);
            aus.push(nach);
        }
        PredArt::Quantor(q) => {
            if q.variable.text != v {
                pred_orte(&q.rumpf, v, aus);
            }
        }
        PredArt::Klammer(i) | PredArt::Nicht(i) => pred_orte(i, v, aus),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            pred_orte(a, v, aus);
            pred_orte(b, v, aus);
        }
        // **No `_` arm**, for the reason `aus_pred` states twenty lines down: a new predicate
        // kind must fail to compile here rather than slip past.
        PredArt::Held { .. } => {}
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
/// was read off the source -- `M109` lives in `m1.rs`: *"`M109` descends only into
/// `[index]` suffixes, not into
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
/// **Not one of them**, and `ensures` among them -- so `M109` in `m1.rs` does not read it
/// either, and
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
            "a domain whose place does not resolve ranges over nothing -- a `forall` over it \
             holds vacuously and an `x in` it is never true. It stands in the certificate \
             and in the library ABI and says nothing. `M109` says the same sentence in \
             `ensures`",
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
    //
    // **The `_ => ""` that stood here was a sentinel, not an answer** (struck 2026-08-31).
    // It made "this is a truth value" and "this is a name that does not start with `option
    // index into`" into ONE case by way of an empty string -- and an empty string is a name
    // like any other. Every non-`Benannt` type simply IS not an `option index into T`, so
    // the two `let … else` say that directly and the refusal below is reached once, from
    // both.
    //
    // **And the sixteen other types are written out.** They all answer the same thing,
    // namely that they are not an `option index into T` -- but they answer it because they
    // are LISTED, not because a `_` swept them up. A seventeenth type (and «C1» wants one:
    // an `option index into T` that is a type instead of a name) is a translation error
    // here instead of a silent `D015`.
    let ziel = match typ {
        Typ::Benannt { name, .. } => name.strip_prefix("option index into "),
        Typ::Ganzzahl(_)
        | Typ::Gleitkomma(_)
        | Typ::Umlaufend(_)
        | Typ::Wahrheit
        | Typ::Nie
        | Typ::Zeiger(_)
        | Typ::Summe { .. }
        | Typ::Verbund(_)
        | Typ::Feld { .. }
        | Typ::Tabelle(_)
        | Typ::Register { .. }
        | Typ::Verbundname(_)
        | Typ::Grund(_)
        | Typ::FnPtr(_)
        | Typ::Unbekannt => None,
    };
    let Some(ziel) = ziel else {
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
