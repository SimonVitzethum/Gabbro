//! **Pass 3 -- M1 und die drei Flussregeln V1–V3.**
//!
//! > *„Jede Operation muss im Bereich ihres Ergebnistyps bleiben; passt `a + b` nicht ins
//! > Ziel, ist das ein **Uebersetzungsfehler, keine Laufzeitpruefung**. Division und Rest
//! > verlangen einen Nenner, dessen Bereich die Null ausschliesst."*
//! > ([`SPRACHE.md`](SPRACHE.md) §3)
//!
//! Und die Gegenmessung -- 255 Subtraktionen, 102 flusssensitiv -- hat gezeigt, dass *eine*
//! Regel nicht reicht und `narrow` allein zum Ritual wuerde. Es gibt genau **drei**:
//!
//! | | Regel |
//! |---|---|
//! | **V1** | eine geprüfte **Bereichsbedingung** verengt den Bereich der geprüften Stelle im Zweig danach |
//! | **V2** | eine geprüfte **Beziehung zweier Stellen** wird zum Zweigfakt: unter `a >= b` hat `a - b` den Typ `0 .. a.max − b.min` |
//! | **V3** | ein `match` auf einen `tagged`-Typ verengt im Zweig auf die Variante samt Nutzlast |
//!
//! **Syntaxgesteuert, ohne Fixpunkt, ohne Loeser.** Der Pass fuehrt je Block eine
//! Faktenmenge, die nur an den drei benannten Stellen waechst und bei **jedem Schreiben auf
//! eine beteiligte Stelle stirbt**. Schleifen tragen keine Fakten hinein.
//!
//! ## Was dieser Pass NICHT tut, und es steht hier statt in einer Fussnote
//!
//! * **Er prueft Rümpfe, keine Praedikate.** `requires`, `ensures` und `invariant` sind
//!   Geisterausdruecke ohne Laufzeitwirkung; sie gehoeren dem Beweiser, nicht M1.
//! * **Er kennt keine Aufrufwirkung auf lokale Werte** -- er braucht sie auch nicht: Gabbro
//!   hat keinen Adressoperator, also kann ein Gerufener eine lokale Groesse nicht aendern.
//!   Alles **Nichtlokale** verliert seine Fakten bei jedem Aufruf.
//! * **Er zaehlt, was er nicht weiss.** Jeder Ausdruck ohne Typ geht in die Zaehlung; ein
//!   Lauf ohne diese Zahl sieht aus wie Deckung.

use crate::fremdverengung::{gespiegelt, zeichen, Stelle, Wirkung};
use crate::typen::{self, IntBereich, Typ};
use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// Was der Pass angesehen hat -- die Zahl steht neben dem Ergebnis.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Zaehlung {
    pub typisiert: usize,
    pub unbekannt: usize,
}

impl Zaehlung {
    pub fn gesamt(&self) -> usize {
        self.typisiert + self.unbekannt
    }

    pub fn deckung(&self) -> f64 {
        if self.gesamt() == 0 {
            return 0.0;
        }
        100.0 * self.typisiert as f64 / self.gesamt() as f64
    }
}

/// Ein Zweigfakt. Er lebt bis zum naechsten Schreiben auf eine beteiligte Stelle.
#[derive(Debug, Clone)]
enum Fakt {
    /// V1 -- die Stelle liegt in diesem Bereich.
    Bereich {
        schluessel: String,
        /// Die Namen, die in den Indizes des Schluessels stehen (U3).
        indizes: Vec<String>,
        min: i128,
        max: i128,
    },
    /// **«F»: die Stelle ist nicht NaN und/oder nicht unendlich.**
    ///
    /// **Keine Bereichsverfeinerung, und das ist der Punkt:** Endlichkeit ist im Gitter kein
    /// Intervall. NaN liegt in KEINEM Intervall, und dieselbe Aussage ist trotzdem nicht
    /// „der Bereich ist enger". Zwei Bits, die unabhaengig geloescht werden koennen.
    ///
    /// *Der Bedarfsbeleg ist eine Disjunktion* (`FRAGMENTE.md`, «F0»/FF1): der Fluchttest
    /// eines echten Renderers lautet `Zz2 < ER2 || isnan(de.x) || isinf(de.x) || …`, und im
    /// Nein-Zweig fallen beide Bits gleichzeitig.
    Endlich {
        schluessel: String,
        indizes: Vec<String>,
        nan: bool,
        unendlich: bool,
    },
    /// **«F»: die Stelle liegt in diesem Gleitkommaintervall.**
    ///
    /// Getrennt von `Bereich`, weil die Grenzen keine ganzen Zahlen sind -- und getrennt von
    /// `Endlich`, weil ein Intervall die zwei Bits nicht ersetzt: *mit NaN im Wertebereich
    /// ist der Vergleich keine totale Ordnung, und ohne totale Ordnung ist ein
    /// Intervallverband kein Verband.* Die zwei Bits sind die Voraussetzung dieser Zusage,
    /// nicht ihre kleinere Schwester.
    FIntervall {
        schluessel: String,
        indizes: Vec<String>,
        lo: f64,
        hi: f64,
    },
    /// V2 -- die Beziehung zweier Stellen, ausschliesslich als Vergleich.
    Beziehung {
        links: String,
        op: BinOp,
        rechts: String,
        indizes: Vec<String>,
    },
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) -> Zaehlung {
    lauf(baum, absagen).0
}

/// **One higher-order refinement debt, harvested where `&f` meets its slot.**
///
/// The record `zeigerverfeinerung_ernten` leaves behind: who owes it (`rufer`, the
/// function whose body hands `&f` to the slot), whose refinement it is (`erzeuger`),
/// which half (`requires` or `ensures`), both contracts in full, and the site. Two
/// records at most per site -- one per non-trivial half.
#[derive(Debug, Clone)]
pub(crate) struct ZeigerVerfeinerung {
    pub rufer: String,
    pub erzeuger: String,
    pub haelfte: String,
    pub slot_gestalt: String,
    pub f_requires: Vec<Pred>,
    pub slot_requires: Vec<Pred>,
    pub f_ensures: Vec<Pred>,
    pub slot_ensures: Vec<Pred>,
    pub f_rumpf_da: bool,
    pub span: Span,
}

/// **The harvested refinement debts of a unit (lane 177).**
///
/// Same run and same reader as the refusals: `lauf` with throwaway findings, the
/// third element. `gabbro obligations` counts them as kind `C`; the live run hints
/// at each (`N297`).
pub(crate) fn zeigerverfeinerungen(baum: &Programm) -> Vec<ZeigerVerfeinerung> {
    let mut fort = Absagen::neu("pflichten");
    lauf(baum, &mut fort).2
}

/// **Die Stellen, an denen der Vertrag eines FREMDEN Rumpfes im Rufer gewirkt hat.**
///
/// Fuer das Zeugnis. *Es ist derselbe Lauf und derselbe Leser* -- die Frage „verengt diese
/// `ensures`-Klausel, und wie?" wird in `fremdverengung::bereich_aus_ensures` genau einmal
/// beantwortet, und diese Funktion holt die Antwort ab, statt sie ein zweites Mal zu stellen.
///
/// > **Ein Zeugnis, das den Baum noch einmal selbst liest, waere der zweite Leser** -- und
/// > genau diese Bauart hat am 2026-08-20 eine Tatsache verloren, die zwei Leser hatte und
/// > von der nur einer las.
///
/// Die Absagen des Laufs fallen hier auf den Boden: das Zeugnis wird nur gedruckt, wenn der
/// richtige Lauf fehlerfrei war (`gabbro zeugnis` bricht sonst ab).
pub fn fremdverengungen(baum: &Programm) -> Vec<Stelle> {
    let mut fort = Absagen::neu("zeugnis");
    lauf(baum, &mut fort).1
}

fn lauf(baum: &Programm, absagen: &mut Absagen) -> (Zaehlung, Vec<Stelle>, Vec<ZeigerVerfeinerung>) {
    let umgebung = Umgebung::sammle(baum);
    // **The PLACE of a quantifier domain**, and all five rules live in `domaene.rs`: its
    // name (`D017`), its type (`D018`) and the two edges of a chain (`D014`-`D016`). The
    // call hangs here because the environment already stands here -- a second
    // `Umgebung::sammle` would be a second reader of one thing.
    //
    // *And it walks EVERY position, not just `ensures`*: `messung/DOMAENENSTELLUNGEN.md`
    // falsified each of the 53 corpus sites outside `ensures` one by one and got 51 silent
    // runs, so the position is where the gap was, not the domain.
    crate::domaene::domaenen(baum, &umgebung, absagen);
    // **`M146` -- the ends of a declared range.** It hangs here for the same reason
    // `domaenen` does: this is the pass that owns what a range MEANS, and a range
    // whose ends are not integers is a declaration M1 silently widened to the whole
    // word. *It needs no environment -- a float literal is decidable from the source.*
    bereichsgrenzen(baum, &umgebung, absagen);
    let mut spezifikationen = std::collections::HashMap::new();
    sammle_spezifikationen(&baum.items, &mut spezifikationen);
    let mut spec_fns = std::collections::HashMap::new();
    sammle_spec_fns(&baum.items, &mut spec_fns);
    let mut p = Pruefer {
        u: &umgebung,
        absagen,
        zaehlung: Zaehlung::default(),
        modul: String::new(),
        rufer: String::new(),
        fremd: Vec::new(),
        zeigerverf: Vec::new(),
        spezifikationen,
        spec_fns,
        unveraenderlich: std::collections::HashSet::new(),
        unveraenderliche_statiken: std::collections::HashMap::new(),
        schon_gemeldet: std::collections::HashSet::new(),
        fehlerkanal: None,
        geraete: crate::m3::geraetetabelle(baum),
        griffe: std::collections::BTreeMap::new(),
    };
    p.programm(baum);
    (p.zaehlung, p.fremd, p.zeigerverf)
}

/// **Alles, was `maintains` nennen darf** -- und das sind ZWEI Arten, nicht eine.
///
/// *Erster Anlauf am 2026-08-19 sammelte nur `spec fn` und meldete an
/// `maintains antwortpflicht_paarig` einen Fehler.* Der Name ist eine **Tabelleninvariante**
/// (`FRAGMENTE.md`:602), und das ist die legitimere der beiden Formen: sie steht am Traeger,
/// nicht daneben. **Eine Regel, die eine gueltige Form des Korpus faellt, ist ein Fehlalarm
/// und kein Fund** -- und dieser hier wurde beim Messen gefangen, nicht beim Ausliefern.
///
/// Unqualifiziert, weil `maintains` heute unqualifiziert schreibt; die Verschaerfung auf
/// qualifizierte Namen steht im TODO.
/// **Only `spec fn`, with arity** -- for `refines` (2026-08-24).
///
/// `sammle_spezifikationen` mixes `spec fn` with `table`/`walk`/`group` invariants, because
/// `maintains` preserves both. **`refines` names a SPECIFICATION**, not an invariant: a table
/// invariant has no body an `impl fn` could refine.
/// *Two questions, two registers -- using one where the other is meant would be a diagnostic
/// that reaches further than its sentence.*
fn sammle_spec_fns(items: &[Item], aus: &mut std::collections::HashMap<String, usize>) {
    for item in items {
        match &item.art {
            ItemArt::Funktion(f) if f.klasse == Some(FnKlasse::Spec) => {
                aus.insert(f.name.text.clone(), f.parameter.len());
            }
            ItemArt::Modul(m) => sammle_spec_fns(&m.items, aus),
            _ => {}
        }
    }
}

fn sammle_spezifikationen(items: &[Item], aus: &mut std::collections::HashMap<String, usize>) {
    for item in items {
        match &item.art {
            ItemArt::Funktion(f) if f.klasse == Some(FnKlasse::Spec) => {
                aus.insert(f.name.text.clone(), f.parameter.len());
            }
            // Eine `table`-Invariante ist eine benannte Aussage ueber ihren Traeger --
            // genau das, was `maintains` erhaelt.
            ItemArt::Tabelle(t) => {
                for i in &t.invarianten {
                    aus.insert(i.name.text.clone(), 0);
                }
            }
            ItemArt::Walk(w) => {
                for i in &w.invarianten {
                    aus.insert(i.name.text.clone(), 0);
                }
            }
            // Eine Gruppen-Invariante nennt mindestens zwei Traeger (`U007`) und ist
            // ebenfalls erhaltbar.
            ItemArt::Gruppe(g) => {
                for i in &g.invarianten {
                    aus.insert(i.name.text.clone(), 0);
                }
            }
            ItemArt::Modul(m) => sammle_spezifikationen(&m.items, aus),
            _ => {}
        }
    }
}

struct Pruefer<'a> {
    u: &'a Umgebung,
    absagen: &'a mut Absagen,
    zaehlung: Zaehlung,
    /// **Die erklaerten `spec fn` -- Name auf Parameterzahl.**
    ///
    /// `maintains I` nennt eine davon, und bis zum 2026-08-19 nannte es sie ins Leere:
    /// sieben Korpusstellen, kein Leser. *Dieselbe Bauart wie `ensures` vor `M109`.*
    spezifikationen: std::collections::HashMap<String, usize>,
    /// Only `spec fn`, name -> arity. See `sammle_spec_fns`.
    spec_fns: std::collections::HashMap<String, usize>,
    /// **Die unveraenderlichen Bindungen des laufenden Rumpfes -- «NL.2.1», 2026-08-19.**
    ///
    /// `let x = 1; x = 2;` ging bis dahin mit **0 Fehlern** durch. `pruefe-klauseln.py`
    /// fuehrte `veraenderlich` als ZUSAGE mit dem Satz *„eine Zuweisung an ein
    /// unveraenderliches Band faellt bei keinem Pass -- ein Verbot ohne Biss."*
    ///
    /// *Es ist keine Buchhaltung, sondern eine Sicherheitsluecke: `mut` ist die Zusage, dass
    /// dieser Name sich nicht bewegt, und M1 rechnet mit ihr* -- eine Tatsache ueber `x`
    /// stirbt beim Schreiben, aber ohne Schreibrecht stirbt sie gar nicht erst.
    unveraenderlich: std::collections::HashSet<String>,
    /// **Die `static`-Namen OHNE `mut` -- «M118», Rezension 2026-08-20.**
    ///
    /// `static zaehler : Z = 0;` und dann `zaehler += 1;` gab **null Fehler**. Der Erzeuger
    /// ehrte die Deklaration korrekt (`static const uint32_t zaehler`) und schrieb daneben
    /// `zaehler += 1;` -- erst `gcc` sagte *„Zuweisung der schreibgeschuetzten Variable"*.
    ///
    /// > *Ein Deklarationszeichen, das der Erzeuger ehrt und das kein Pass haelt* -- dieselbe
    /// > Familie, in der `own` eine Woche vorher stand.
    ///
    /// Getrennt von `unveraenderlich`, weil das die Bindungen des LAUFENDEN Rumpfes sind:
    /// eine lokale Bindung darf einen `static` verdecken, und dann gilt sie.
    unveraenderliche_statiken: std::collections::HashMap<String, bool>,
    /// Welche Spannen `M119` schon getroffen hat -- ein Ort wird auf zwei Wegen besucht.
    schon_gemeldet: std::collections::HashSet<(u32, u32)>,
    /// Das Modul, in dem der gerade gepruefte Rumpf steht. **Ohne ihn loest der Pass Namen
    /// im Blindflug auf** -- und ein gleichnamiges `fn` in einem fremden Modul loescht eine
    /// Bereichspruefung, ohne dass jemand es sieht (Gegenpruefung 2026-08-14, U11/U12).
    modul: String,
    /// Der Name des Rumpfes, in dem der Pass gerade steht -- **fuer das Zeugnis, nicht fuer
    /// eine Absage.** Eine Verengung aus einem fremden Vertrag ohne den Rufer daneben waere
    /// eine Zahl ohne Fundstelle.
    rufer: String,
    /// Die Stellen, an denen der Vertrag eines FREMDEN Rumpfes gewirkt hat.
    ///
    /// *Gesammelt wird an genau den zwei Stellen, an denen der Pass aus einem `ensures`
    /// etwas macht* -- `aus_ensures` (Bereich) und `beziehung_aus_ensures` (Beziehung).
    /// Wer eine dritte hinzufuegt und hier nichts eintraegt, macht die Flaeche unsichtbar,
    /// nicht kleiner.
    fremd: Vec<Stelle>,
    /// **The harvested higher-order refinements (lane 177).** One record per
    /// non-trivial implication half where `&f` meets its slot; read out by
    /// `zeigerverfeinerungen` for the obligation register.
    zeigerverf: Vec<ZeigerVerfeinerung>,
    /// **Der Fehlerkanal des laufenden Rumpfes** (Stufe 7, 2026-08-21) -- der `reason` aus
    /// `-> T or R`, voll qualifiziert.
    ///
    /// Er steht hier und nicht als Parameter neben `ergebnis`, weil `block`/`unterblock`/
    /// `anweisung` ihn nur an EINER Stelle brauchen (`return`) und die Kette sonst vier
    /// Signaturen breiter waere.
    fehlerkanal: Option<String>,
    /// **The register table, and it is `m3.rs`'s -- not a second one** (2026-08-30).
    ///
    /// `«B26»` makes a register read FALLIBLE, and then the `else` branch binds a reason.
    /// Which reason stands in the DECLARATION (`requires … else R::C`), so this pass has to
    /// read the declaration to bind `e`. *The table it reads is `m3::geraetetabelle`; a
    /// second one over the same registers would be W7, and the two could drift apart with
    /// nobody the wiser.*
    geraete: std::collections::BTreeMap<String, std::collections::BTreeMap<String, crate::m3::RegInfo>>,
    /// Which local name carries which device, for the body this pass is inside -- again
    /// `m3::griffe_von` and not a second resolution.
    griffe: std::collections::BTreeMap<String, String>,
}

/// Die Bindungen und Fakten eines Blocks. Ein Block erbt beide und gibt keins zurueck.
#[derive(Clone, Default)]
struct Lage {
    lokal: HashMap<String, Typ>,
    fakten: Vec<Fakt>,
    /// **V4 freshness beside the M1 fact set** (`messung/FRISCHE-V4-ENTWURF.md`).
    ///
    /// `frisch` maps a local holding carrier-derived data to its source carriers
    /// (carrier granularity -- never a field path); a killed entry moves to
    /// `veraltet` instead of vanishing, because only a NAMED expiry can be refused
    /// later. Re-binding from a fresh read revalidates. Homed here and not in a new
    /// pass: every kill site is a V1-V3 kill site already (`schreiben_toetet_fakten`,
    /// `rufe_toeten_fakten`, the loop boundary), so the map reuses that machinery
    /// instead of walking the tree a second time.
    frisch: HashMap<String, std::collections::HashSet<String>>,
    /// Locals whose carrier was written since their last fresh read, each with
    /// the source carriers it was tainted with when it expired. Acting on one
    /// (branch/match condition, call argument, return, `narrow` subject, index) is
    /// refused as `M147`; storing or moving one stays allowed. The recorded
    /// carriers are what index-vs-content precision reads: an occurrence inside
    /// an index into a carrier disjoint from them is excused, everything else
    /// refuses as before. An empty set means unknown -- fail-closed, refuse.
    veraltet: HashMap<String, std::collections::HashSet<String>>,
}

impl<'a> Pruefer<'a> {
    fn programm(&mut self, baum: &Programm) {
        // **Ein eigener Durchgang, weil ein Rumpf frueher stehen darf als seine Deklaration.**
        // Wuerde diese Menge im Hauptlauf mitwachsen, haenge die Absage an der Reihenfolge im
        // Quelltext -- und eine Regel, die von der Reihenfolge abhaengt, ist keine.
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            if let ItemArt::Statisch(s) = &item.art {
                if !s.veraenderlich {
                    // **Der Wert `true` heisst: ein ZEIGER, und dann gilt die Regel nur fuer
                    // ihn selbst.** `static tz : ptr<…, rw> T` ohne `mut` sagt, dass der
                    // Zeiger nicht umgehaengt wird -- *ueber das, worauf er zeigt, sagt es
                    // nichts.* Das steht in `ptr<…, rw>`, und `tz.slots[i].a = 5` ist
                    // richtig. Der Erzeuger schreibt dafuer `T *const tz`.
                    let ist_zeiger = matches!(
                        self.u.typ_von_ausdruck_decl(modul, &s.typ),
                        Typ::Zeiger(_)
                    );
                    self.unveraenderliche_statiken
                        .insert(s.name.text.clone(), ist_zeiger);
                }
            }
        });
        crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
            // **M1 sah bis 2026-08-18 NUR Funktionsruempfe.** Das fiel an «F» auf, und zwar
            // an der teuersten denkbaren Stelle: `F002` biss im Rumpf und schwieg in der
            // `const`-Deklaration -- *also genau dort, wo der Bedarfsbeleg herkam.*
            //
            // Die 53 inexakten Literale, die F0 an einem echten Renderer gemessen hat, sind
            // ln 2, 2 pi, Schwellwerte. **Die leben in Konstanten.** Eine Regel, die ueberall
            // beisst ausser am Hauptschauplatz, ist keine Stichprobe -- sie ist umgekehrt
            // gemessen.
            //
            // *Ein Initialisierer wird mit LEERER Lage geprueft: er hat keine Parameter und
            // keine Fakten, nur die Umgebung.*
            // **`M117` -- ein LEERER Bereich, und er hat den Pruefer umgebracht**
            // (2026-08-20).
            //
            // ```gabbro
            // type Verdreht = u32 in 5 .. 0;
            // impl fn teile(a : u32, n : Verdreht) -> u32 { return a / n; }
            // ```
            //
            // gab *„panicked at typen.rs:558: attempt to divide by zero"*. Der Waechter
            // davor ist `enthaelt_null()` = `min <= 0 && max >= 0`; bei `min = 5, max = 0`
            // ist das FALSCH, also lief `a.min / b.max` in die Null.
            //
            // **Aber die Ursache ist nicht die Division.** `type Verdreht = u32 in 5 .. 0;`
            // ging allein mit null Fehlern durch -- und mit `%` statt `/` ging auch die
            // Rechnung still durch. *Ein Typ, der keinen Wert enthaelt, galt damit als
            // Nachweis, dass der Divisor nicht null ist:* aus einem leeren Bereich folgt
            // jede Aussage, und genau darum darf er nicht dastehen duerfen.
            //
            // > Ein Absturz ist besser als ein stilles Ja -- aber beides ist falsch.
            //
            // **Wie weit das reicht:** geprueft wird der Bereich, den die AEUSSERE Typform
            // eines Items traegt (Typdeklaration, Parameter, Rueckgabe, `const`, `static`).
            // Ein Bereich tief in einem Feld eines Verbunds faellt hier NICHT auf -- dagegen
            // steht der Riegel in `typen.rs`, der aus einem leeren Bereich `None` macht
            // statt zu rechnen.
            let mut leer = |u: &Umgebung, modul: &str, tx: &TypExpr, span, was: &str| {
                if let Some(b) = u.typ_von_ausdruck_decl(modul, tx).bereich() {
                    if b.min > b.max {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M117",
                                span,
                                format!("{was} has an EMPTY range: {} .. {}", b.min, b.max),
                            )
                            .mit_notiz(
                                "a range whose lower bound exceeds its upper one contains no value at all \
                                 -- and from that every statement follows: it would \
                                 prove a divisor non-zero, an index in bounds, anything",
                            ),
                        );
                    }
                }
            };
            match &item.art {
                ItemArt::Typ(td) => {
                    if let Some(r) = &td.rumpf {
                        leer(self.u, modul, r, td.name.span, "this type");
                    }
                }
                ItemArt::Konst(k) => leer(self.u, modul, &k.typ, k.name.span, "this constant"),
                ItemArt::Statisch(s) => leer(self.u, modul, &s.typ, s.name.span, "this static"),
                ItemArt::Funktion(f) => {
                    for pa in &f.parameter {
                        leer(self.u, modul, &pa.typ, pa.name.span, "this parameter");
                    }
                    if let Some(e) = &f.ergebnis {
                        leer(self.u, modul, e, f.name.span, "this result");
                    }
                }
                _ => {}
            }
            if let ItemArt::Konst(k) = &item.art {
                self.modul = modul.to_string();
                self.rufer = format!("const {}", k.name.text);
                let ziel = self.u.typ_von_ausdruck_decl(modul, &k.typ);
                let mut lage = Lage::default();
                let quelle = self.ausdruck(&k.wert, &mut lage);
                self.passt(&quelle, &ziel, k.wert.span, "constant");
            }
            // **`F004` -- und der Bedarfsbeleg steht im Korpus, nicht in einer Vorsorge.**
            //
            // «F0»/FF3 zeigt eine Gleitkommareduktion in echtem Code: `a += progress[i]`
            // ueber ein Feld. Genau die Form, fuer die `accumulates` da ist -- und ueber
            // Gleitkomma ist sie REIHENFOLGEABHAENGIG.
            //
            // `accumulates.monoid` ist BEWIESEN, unter der Praemisse, dass die Merge-Menge
            // ein kommutatives Monoid ist. Der Eintrag sagt, warum das mechanisch pruefbar
            // ist: der Wortschatz ist geschlossen. **Das ist die halbe Wahrheit** -- er
            // reicht nur, weil alle Zahlentypen ganzzahlig sind. Ueber `f64` ist `add` nicht
            // assoziativ und `max` mit NaN kein Verband, und
            // `faltung_ist_reihenfolgeunabhaengig` verlangt beides.
            //
            // *Der Satz bliebe wahr und seine Praemisse wuerde falsch.* Also weigert sich der
            // Pruefer, statt eine bewiesene Schablone ueber einen Fall zu spannen, den sie
            // nicht traegt.
            if let ItemArt::Accumulates(a) = &item.art {
                self.modul = modul.to_string();
                let t = self.u.typ_von_ausdruck_decl(modul, &a.typ);
                if matches!(t.durchgreifen(), Typ::Gleitkomma(_)) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F004",
                            a.name.span,
                            format!(
                                "`accumulates {}` over a floating-point type -- the fold \
                                    has no order",
                                a.name.text
                            ),
                        )
                        .mit_notiz(
                            "the lowering folds one cell per core in an order nobody \
                                fixes; `add` is not associative over floating point, and \
                                `max` with NaN is no lattice",
                        )
                        .mit_notiz(
                            "`accumulates.monoid` is PROVED -- under the premise that the \
                                merge set is a commutative monoid. Here it would not be, and \
                                the theorem would have a false premise",
                        ),
                    );
                }
            }
            if let ItemArt::Statisch(st) = &item.art {
                self.modul = modul.to_string();
                self.rufer = format!("static {}", st.name.text);
                let ziel = self.u.typ_von_ausdruck_decl(modul, &st.typ);
                let mut lage = Lage::default();
                let quelle = self.ausdruck(&st.wert, &mut lage);
                self.passt(&quelle, &ziel, st.wert.span, "static value");
            }
            if let ItemArt::Funktion(f) = &item.art {
                self.modul = modul.to_string();
                self.ensures_pruefen(f);
                self.maintains_pruefen(f);
                self.verfeinert_pruefen(f);
            }
            if let ItemArt::Funktion(f) = &item.art {
                // Nur Ruempfe: Praedikate haben keine Laufzeitwirkung.
                if let FnRumpf::Block(b) = &f.rumpf {
                    self.modul = modul.to_string();
                    self.rufer = f.name.text.clone();
                    let mut lage = Lage::default();
                    for prm in &f.parameter {
                        let t = self.u.typ_von_ausdruck_decl(modul, &prm.typ);
                        lage.lokal.insert(prm.name.text.clone(), t);
                    }
                    let ergebnis = f
                        .ergebnis
                        .as_ref()
                        .map(|t| self.u.typ_von_ausdruck_decl(modul, t));
                    // **Der Fehlerkanal reist mit in den Rumpf** (Stufe 7) -- ein
                    // `return HolFehler::Leer;` haengt an ihm.
                    self.fehlerkanal = f
                        .fehler
                        .as_ref()
                        .and_then(|r| self.u.grund(modul, &r.text).map(|(q, _)| q));
                    // **And which local name carries which device**, for the same reason the
                    // error channel travels: a fallible register read binds its reason in the
                    // `else` branch, and the reason stands in the register's declaration.
                    self.griffe = crate::m3::griffe_von(f, &self.geraete);
                    self.block(b, &mut lage, ergebnis.as_ref());
                    self.griffe.clear();
                    self.fehlerkanal = None;
                }
            }
            // **Und der `can_fail`-Rumpf einer Probe** (2026-08-20).
            //
            // Bis heute las M1 ihn nicht. `gabbro pruefe beispiele/06` meldete woertlich
            // *„M1 saw no expression -- this file has no function body"*, waehrend im
            // `can_fail` drei Groessen verrechnet wurden, die nirgends erklaert waren.
            // **Gefunden hat es der Erzeuger**, der dort drei unbekannte Typnamen sah.
            //
            // > Ein `check` ist der ORT, an dem eine falsifizierbare Aussage steht -- und er
            // > war der einzige Rumpf, den kein Typpass gelesen hat. *Dieselbe Klasse fiel am
            // > selben Tag beim Paarungspass, und aus demselben Grund: beide laufen ueber
            // > `ItemArt::Funktion` und sonst nichts.*
            //
            // Der Rumpf hat keine Parameter, also eine leere Lage; sein Ergebnis ist `bool`
            // -- eine Probe faellt oder haelt.
            if let ItemArt::Check(c) = &item.art {
                self.modul = modul.to_string();
                self.rufer = format!("check {}", c.name.text);
                let mut lage = Lage::default();
                let bool_typ = Typ::Wahrheit;
                self.block(&c.can_fail, &mut lage, Some(&bool_typ));
            }
        });
    }

    // -- Anweisungen --------------------------------------------------------------------

    fn block(&mut self, b: &Block, lage: &mut Lage, ergebnis: Option<&Typ>) {
        for s in &b.anweisungen {
            self.anweisung(s, lage, ergebnis);
        }
    }

    /// **U1.** Ein Unterblock bekommt eine Kopie der Lage -- seine Schreibzugriffe muessen
    /// die Fakten des UMGEBENDEN Blocks trotzdem toeten. Sonst ueberlebt ein Fakt jedes
    /// Schreiben, das in einem `if`/`match`/Schleifen-/`locks`-Rumpf steht, und
    /// `SPRACHE.md` §3.2 -- *„stirbt bei jedem Schreiben auf eine beteiligte Stelle"* --
    /// ist an dieser Stelle falsch.
    fn unterblock(&mut self, b: &Block, aussen: &mut Lage, ergebnis: Option<&Typ>) {
        let mut innen = aussen.clone();
        self.block(b, &mut innen, ergebnis);
        self.geschriebenes_toeten(b, aussen);
    }

    fn geschriebenes_toeten(&mut self, b: &Block, aussen: &mut Lage) {
        let mut ziele = Vec::new();
        sammle_schreibziele(b, &mut ziele);
        for z in ziele {
            self.schreiben_toetet_fakten(&z, aussen);
        }
    }

    /// **`M124` -- die STELLUNG eines Grundwerts, und sie ist eng** (Stufe 7, 2026-08-21).
    ///
    /// Gemessen, nachdem der Erzeuger stand und bevor diese Regel geschrieben war: ein
    /// Grundwert ging an **sieben** Stellungen still durch --
    ///
    /// ```text
    /// let g = HolFehler::Leer;              nimm(HolFehler::Leer);
    /// t.slots[HolFehler::Leer].w            z = HolFehler::Leer;
    /// if HolFehler::Leer { … }              !HolFehler::Leer
    /// ensures result == HolFehler::Leer
    /// ```
    ///
    /// *`gabbro pruefe`: 13 Items, 0 Fehler, 0 Hinweise.* Die Typregeln davor sahen jedes
    /// Mal ein `Unbekannt` und schwiegen -- **eine neue Wertart oeffnet jede Stellung, in
    /// der eine Regel `_ =>` schreibt**, und das sind 53 Stellen in diesem Pruefer.
    ///
    /// Deshalb ist die Regel STRUKTURELL und nicht typweise: *ein Grund darf an genau drei
    /// Stellen stehen*, und alles andere faellt, ohne dass irgendeine der 53 davon wissen
    /// muss.
    ///
    /// | erlaubt | |
    /// |---|---|
    /// | `return R::F;` | die Fehlerrueckgabe -- `M122` haelt den Kanal dazu |
    /// | `match e { … }` | die Fallunterscheidung -- `M123`/`M125` halten sie geschlossen |
    /// | `a == b` / `a != b` | der Vergleich -- `M124` (Typhaelfte) haelt die Deklaration |
    /// | `f(R::F)` at `f(x : R)` | **the REPORT, since 2026-08-25** -- and that is exactly what the number in a `reason` line is for |
    ///
    /// Klammern zaehlen nicht mit: `return (R::F);` ist dieselbe Stellung.
    ///
    /// **The fourth door is structural like the three before it.** It does not ask the type
    /// checker; it looks up the callee's signature and requires `Typ::Grund(n)` there with
    /// the same `n`. *`nimm(R::F)` at `nimm(x : u32)` still falls* -- one of the seven
    /// positions of the 2026-08-21 measurement.
    fn grundstellung(&mut self, s: &Stmt, lage: &Lage) {
        // **Ein Grund steht in ZWEI Gestalten da**, und beide muessen erfasst sein:
        // geschrieben als `R::F`, und gebunden als das `e` eines `let … else`. *Die zweite
        // haette man leicht uebersehen -- `e + 1` ist genau die Stellung, die die Messung
        // vom 2026-08-21 als still durchgehend gefunden hat, und dort steht kein `R::F`.*
        let ist_grund = |e: &Expr| match &e.art {
            ExprArt::Grund { .. } => true,
            ExprArt::Ort(o) => {
                o.suffixe.is_empty()
                    && matches!(lage.lokal.get(&o.basis.text), Some(Typ::Grund(_)))
            }
            _ => false,
        };
        /// Steigt in einen Ausdruck ab. `erlaubt` sagt, ob an DIESER Stelle ein Grund
        /// stehen darf; ein Vergleich macht seine beiden Seiten erlaubt, alles andere
        /// not -- **except an argument whose parameter declares EXACTLY this reason**
        /// (the fourth door, `argument_erlaubt`).
        fn steige(
            e: &Expr,
            erlaubt: bool,
            ist_grund: &dyn Fn(&Expr) -> bool,
            argument_erlaubt: &dyn Fn(&Ruf, usize, &Expr) -> bool,
            aus: &mut Vec<Span>,
        ) {
            if ist_grund(e) {
                if !erlaubt {
                    aus.push(e.span);
                }
                return;
            }
            match &e.art {
                ExprArt::Klammer(x) => steige(x, erlaubt, ist_grund, argument_erlaubt, aus),
                ExprArt::Binaer(op, a, b) if op.ist_vergleich() => {
                    steige(a, true, ist_grund, argument_erlaubt, aus);
                    steige(b, true, ist_grund, argument_erlaubt, aus);
                }
                // **Ein Ruf MITTEN in einem Ausdruck** -- `let x = melde(S::Ok) + 1;`. Ohne
                // this arm the fourth door would find only the statement form, and a call
                // at an expression site would stay a false rejection. *Exactly the half one
                // overlooks, because the measurement starts at statements.*
                ExprArt::Ruf(r) => {
                    for (i, a) in r.argumente.iter().enumerate() {
                        steige(a, argument_erlaubt(r, i, a), ist_grund, argument_erlaubt, aus);
                    }
                }
                _ => {
                    for k in crate::unterausdruecke(e) {
                        steige(k, false, ist_grund, argument_erlaubt, aus);
                    }
                }
            }
        }
        // **The FOURTH door, and it stayed STRUCTURAL** (2026-08-25, W22).
        //
        // Gemessen als falsche Ablehnung eines KORREKTEN Programms: `melde(Status::Ok)` an
        // `extern fn melde(st : Status)` fell as `M124`, although the parameter is exactly
        // the `reason` whose value is passed. **Six sites in F3 and F5** -- and this is the
        // position the number in a `reason` line exists for at all: *so that a REPORT can
        // name it.* A reporter IS the report.
        //
        // **And the rule stays structural nonetheless** -- that is where this door differs
        // from the type-wise version the statement `v1.grundwert` expressly rejected (*"a
        // rule that trusted the type checker would have caught five of seven"*). It does
        // **not** ask whether some pass considers the expression compatible; it looks up the
        // callee's DECLARATION and requires `Typ::Grund(n)` there with the same `n`. No `_`
        // arm over `ExprArt` can let anything past it: the answer hangs on the signature,
        // not on the value.
        //
        // *`nimm(HolFehler::Leer)` at `nimm(x : u32)` still falls* -- and that was one of
        // the seven positions the 2026-08-21 measurement found slipping through silently.
        let argument_erlaubt = |r: &Ruf, i: usize, a: &Expr| -> bool {
            let Some(gesucht) = grundname_von(a, lage) else { return false };
            let CallTarget::Path(pf) = &r.ziel else {
                // A call through a `fn` pointer: the signature stands at the place's TYPE,
                // and `N036` carries the effect words there. **Nothing is guessed here.**
                return false;
            };
            let Some(sig) = self.u.funktion(&self.modul, pf) else { return false };
            // **Fully qualify BOTH names before comparing them.** `R::F` names the reason
            // short, `Typ::Grund` carries it long -- *the same trap that has struck three
            // times in this folder: a qualified map, queried with a bare name, always
            // answers no.*
            let voll = self
                .u
                .grund(&self.modul, &gesucht)
                .map(|(k, _)| k)
                .unwrap_or(gesucht);
            matches!(sig.parameter.get(i), Some((_, Typ::Grund(n))) if *n == voll)
        };
        let mut schlecht = Vec::new();
        for e in crate::eigene_ausdruecke(s) {
            // **Nur der DIREKTE Gegenstand ist erlaubt.** `return f(R::F);` ist es
            // nicht -- dort waere der Grund ein Argument.
            let erlaubt = match &s.art {
                StmtArt::Return(Some(r)) => std::ptr::eq(r, e),
                StmtArt::Match(m) => std::ptr::eq(&m.gegenstand, e),
                _ => false,
            };
            steige(e, erlaubt, &ist_grund, &argument_erlaubt, &mut schlecht);
        }
        // **Die Argumente einer ANWEISUNGSform** -- `eigene_ausdruecke` fuehrt sie nicht,
        // weil `StmtArt::Ruf` und `StmtArt::LetSonst` ihren Ruf nicht in einem `Expr`
        // tragen. *Gemessen: ohne diese zwei Zeilen ging `nimm(R::F);` weiter durch, und
        // zwar als einzige der sieben Stellungen* -- die Regel haette sich mit fuenf von
        // sieben richtig angefuehlt.
        let rufe: &[&Ruf] = &match &s.art {
            StmtArt::Ruf(r) => vec![r],
            StmtArt::LetSonst(l) => l.als_ruf().into_iter().collect(),
            _ => Vec::new(),
        };
        for r in rufe {
            for (i, a) in r.argumente.iter().enumerate() {
                steige(a, argument_erlaubt(r, i, a), &ist_grund, &argument_erlaubt, &mut schlecht);
            }
        }
        for span in schlecht {
            self.absagen.schiebe(
                Absage::fehler(
                    "M124",
                    span,
                    "a reason value cannot stand here",
                )
                .mit_notiz(
                    "a reason goes through four doors: `return` in a function that \
                     declares `or <reason>`, the subject of a `match`, a comparison \
                     against a reason of the SAME declaration, and an argument at a \
                     parameter whose DECLARED type is exactly this reason",
                )
                .mit_notiz(
                    "the number in a `reason` line is there so that a REPORT can name it, \
                     not so that it can be computed with, indexed by or assigned",
                ),
            );
        }
    }

    fn anweisung(&mut self, s: &Stmt, lage: &mut Lage, ergebnis: Option<&Typ>) {
        self.grundstellung(s, lage);
        self.frische_gebrauch(s, lage);
        match &s.art {
            StmtArt::Let(l) => {
                let wert = self.ausdruck(&l.wert, lage);
                self.rufe_im_ausdruck(&l.wert, lage);
                let ziel = l.typ.as_ref().map(|t| self.u.typ_von_ausdruck_decl(&self.modul, t));
                if let Some(z) = &ziel {
                    self.passt(&wert, z, l.wert.span, "binding");
                }
                // U2: die neue Bindung verdeckt die alte -- jeder Fakt ueber den Namen
                // stirbt, sonst erbt die Verdeckung die Verengung ihres Vorgaengers.
                lage.fakten
                    .retain(|f| !nennt_namen(f, &l.name.text));
                // **V4 -- the map grows at a `let` with a carrier-read RHS** (spec
                // §1): a direct carrier read, a call's reads-hull, or the taint a
                // moved local already carries. Anything else rebinds the name fresh.
                let mut traeger = std::collections::HashSet::new();
                let veraltet = self.traeger_im_ausdruck(&l.wert, lage, &mut traeger);
                self.frische_wachsen(&l.name.text, traeger, veraltet, lage);
                // **V1 an der Bindung -- «H2.1», 2026-08-19.**
                //
                // `let mut n : u32 in 0 .. NSLOTS = 0;` setzte den Namen bisher auf den
                // DEKLARIERTEN Bereich und warf weg, was der Anfangswert sagt. *Der Wert
                // steht daneben, und niemand las ihn.*
                //
                // Die Tatsache ist sound wie jede andere: unmittelbar nach der Bindung IST
                // der Wert der Anfangswert, und sie stirbt beim ersten Schreiben. **Sie
                // kann nur mehr durchlassen, nie weniger** -- der Korpuspreis ist damit
                // hoechstens null.
                //
                // Gebraucht wird sie fuer den Zaehler einer Traversierung: ohne den
                // Anfangswert hat `n <= c + (B-1)*k` kein `c`.
                if let (Some(w), Some(z)) = (wert.bereich(), ziel.as_ref().and_then(|z| z.bereich())) {
                    if w.min > z.min || w.max < z.max {
                        lage.fakten.push(Fakt::Bereich {
                            schluessel: l.name.text.clone(),
                            indizes: Vec::new(),
                            min: w.min,
                            max: w.max,
                        });
                    }
                }
                // **Punkt 4, zweite Haelfte: die RELATIONALE Nachbedingung (2026-08-19).**
                //
                // `aus_ensures` verengt aus `result <op> <Zahl>`. Die haeufigere Form nennt
                // einen ORT: `ensures result <= s.len`. `FRAGMENTE.md`:1152 sagt es selbst --
                // *„Das kommt durch, weil das `ensures` von `unberuehrt` `<= s.len` sagt: aus
                // dem VERTRAG der gerufenen Funktion, nicht aus einer Flussregel."*
                //
                // **Die Zeile stand da und kam NICHT durch**, weil der Ort im Vertrag den
                // PARAMETER des Gerufenen nennt und der Rufer sein Argument. Uebersetzt wird
                // hier: Parametername -> Argumentort.
                //
                // > *Es ist V2, nicht V1* -- eine Beziehung zweier Stellen, und die
                // > Maschinerie dafuer gibt es seit jeher (`Fakt::Beziehung`).
                if let ExprArt::Ruf(r) = &l.wert.art {
                    self.beziehung_aus_ensures(&l.name.text, r, lage);
                }
                if l.veraenderlich {
                    self.unveraenderlich.remove(&l.name.text);
                } else {
                    self.unveraenderlich.insert(l.name.text.clone());
                }
                lage.lokal
                    .insert(l.name.text.clone(), ziel.unwrap_or(wert));
            }
            StmtArt::LetSonst(l) => {
                // **A `place` source carries a DECLARED type, and until 2026-08-30 nobody
                // read it.**
                //
                // «B14b» (2026-08-17) let `let … else` unpack a `place` as well as a call.
                // The type binding never followed: the call half asked the signature, the
                // place half answered `Unbekannt` outright -- so the bound name had no type,
                // every later mention of it counted as uncovered, and **`M104` went quiet
                // exactly where it had a job**.
                //
                // > *Measured, same body twice.* `let t = hol_tiefe() else (e) { … }` with
                // > `return t + 1;` refuses at `M104` (*`u32 + u8 in 1 .. 1` leaves the width
                // > of the result type*). The same arithmetic over `let t = d.TIEFE else (e)
                // > { … }` passed with 0 errors and booked one expression as untyped. **One
                // > overflow caught, one waved through, and the source of the `let` decided
                // > which.**
                //
                // The option gets unpacked, because that is what the statement DOES -- the
                // same step `match … { Some(i) => … }` takes three hundred lines up. A place
                // that carries no option (a device register behind `requires … else`) keeps
                // its own type, and an unreadable place still answers `Unbekannt`: *unknown
                // falls loud*, as everywhere else here.
                let t = match &l.quelle {
                    LetQuelle::Ruf(r) => self.ruf(r, lage),
                    LetQuelle::Ort(o) => {
                        let roh = self.u.typ_von_ort(&self.modul, o, &lage.lokal);
                        match option_nutzlast(&roh) {
                            Some(nutz) => nutz,
                            None => roh,
                        }
                    }
                };
                lage.fakten.retain(|f| !nennt_namen(f, &l.name.text));
                lage.lokal.insert(l.name.text.clone(), t);
                let pfade = l.als_ruf().map(rufnamen_im_ruf).unwrap_or_default();
                self.rufe_toeten_fakten(&pfade, lage);
                // **V4 -- like `let`** (spec §1): a fallible call's return taint is
                // its reads-hull; a place source taints like any carrier read.
                let mut traeger = std::collections::HashSet::new();
                let mut veraltet = false;
                match &l.quelle {
                    LetQuelle::Ruf(r) => {
                        traeger = self.rueckgabe_traeger(r, lage);
                    }
                    LetQuelle::Ort(o) => {
                        if let Some(c) = self.traeger_von_ort(o, lage) {
                            traeger.insert(c);
                        }
                        if let Some(s) = lage.frisch.get(&o.basis.text).cloned() {
                            traeger.extend(s);
                        }
                        if let Some(s) = lage.veraltet.get(&o.basis.text) {
                            veraltet = true;
                            traeger.extend(s.iter().cloned());
                        }
                        for sx in &o.suffixe {
                            if let OrtSuffix::Index(x) = sx {
                                veraltet |= self.traeger_im_ausdruck(x, lage, &mut traeger);
                            }
                        }
                    }
                }
                self.frische_wachsen(&l.name.text, traeger, veraltet, lage);
                // **`e` bekommt einen TYP** (Stufe 7, 2026-08-21).
                //
                // Bis heute stand `fehlername` in genau EINER Datei des Pruefers -- in
                // `emit.rs`, wo der Erzeuger `HolFehler e; (void)e;` schrieb. **Kein Pass
                // wusste, dass der Name existiert:** `match e { … }` im `else`-Zweig fiel
                // mit `M119` (*„`e` is declared nowhere"*), gemessen am 2026-08-21.
                //
                // > *Eine Klausel ohne Leser* -- dieselbe Lochform wie `@version`,
                // > `nested masked` und `lock … masks irqs`. Der Binder war da, er band
                // > nichts.
                //
                // Der Typ kommt aus dem `or R` des GERUFENEN, nicht aus der Umgebung des
                // Rufers: wer scheitern kann, sagt woran (`SPRACHE.md` 8.1). Steht dort
                // keiner, faellt schon `N028` -- hier bleibt der Name dann ungebunden, und
                // `M119` sagt es ein zweites Mal, statt einen Typ zu erfinden.
                //
                // **And since 2026-08-30 from the REGISTER DECLARATION as well** («B26»).
                //
                // `let t = d.TIEFE else (e) { … }` is the second lowering of one form: the
                // source is a place, not a call, so the line above answered `None` -- and
                // `return e;` fell with `M119` (*"`e` is declared nowhere"*). Measured
                // against the unchanged checker; `beispiele/44` sidesteps the site by
                // writing `return Geraetelug::ZuTief;` instead.
                //
                // > *The clause was there, it bound nothing* -- literally the hole the
                // > paragraph above describes for the call branch, one week later and at the
                // > sister form.
                //
                // The reason comes from `m3::geraetetabelle` and from no second table:
                // whoever can fail says what of, and at a register the declaration says it.
                let grund_typ = l
                    .als_ruf()
                    .and_then(|r| {
                        self.u
                            .fehlerkanal(&self.modul, &r.path()?.teile.last()?.text)
                    })
                    .or_else(|| match &l.quelle {
                        LetQuelle::Ort(o) => {
                            let t = crate::m3::ort_register(o, &self.geraete, &self.griffe)?;
                            let (g, _) = t.info.fehlbar.as_ref()?;
                            self.u.grund(&self.modul, g).map(|(q, _)| q)
                        }
                        LetQuelle::Ruf(_) => None,
                    })
                    .map(Typ::Grund);
                //
                // **Eingetragen und wieder ENTFERNT**, statt in eine eigene Kopie der Lage:
                // `unterblock` kopiert selbst und traegt die getoeteten Fakten in die
                // aeussere Lage zurueck. *Eine zweite Kopie hier haette genau diese
                // Rueckwirkung verschluckt* -- U1, und der Fehler waere ein Fakt gewesen,
                // der jedes Schreiben im `else`-Zweig ueberlebt.
                let vorher = grund_typ
                    .map(|g| lage.lokal.insert(l.fehlername.text.clone(), g));
                self.unterblock(&l.sonst, lage, ergebnis);
                if let Some(alt) = vorher {
                    match alt {
                        Some(t) => lage.lokal.insert(l.fehlername.text.clone(), t),
                        None => lage.lokal.remove(&l.fehlername.text),
                    };
                }
            }
            // **«E4»: `let i = alloc A (v) [else block];`.**
            //
            // The value is held against the arena's element type (`M101`
            // says nothing new here -- it is the ordinary `passt`); the
            // bound name gets type `index into A`, the name the generation
            // travels with (`arena.rs` tracks which generation, `N214` in
            // `arena_ort` holds the belonging at every read). An unknown
            // arena is `N213` in `arena.rs`, so this arm stays silent about
            // it -- unknown falls loud, exactly once.
            StmtArt::Alloc(a) => {
                let wert = self.ausdruck(&a.wert, lage);
                self.rufe_im_ausdruck(&a.wert, lage);
                if let Some(q) = self.u.nennt_arena(&self.modul, &a.tisch.text) {
                    // Cloned out of the map first: `passt` borrows `self`
                    // mutably, and the map lives in it.
                    let element = self.u.arenen.get(&q).map(|s| s.element.clone());
                    if let Some(e) = &element {
                        self.passt(&wert, e, a.wert.span, "arena element");
                    }
                    let index = self.u.indextyp(&self.modul, &a.tisch.text, false);
                    let ziel = a.typ.as_ref().map(|t| self.u.typ_von_ausdruck_decl(&self.modul, t));
                    if let Some(z) = &ziel {
                        self.passt(&index, z, a.wert.span, "arena index");
                    }
                    lage.fakten.retain(|f| !nennt_namen(f, &a.name.text));
                    if a.veraenderlich {
                        self.unveraenderlich.remove(&a.name.text);
                    } else {
                        self.unveraenderlich.insert(a.name.text.clone());
                    }
                    lage.lokal.insert(a.name.text.clone(), ziel.unwrap_or(index));
                }
                if let Some(sonst) = &a.sonst {
                    self.unterblock(sonst, lage, ergebnis);
                }
            }
            // **«E4»: `reset A;`.** No expression, no binding -- the
            // generation moves in `arena.rs`, and nothing here has to move
            // with it. An unknown arena is `N213` there.
            StmtArt::ResetArena(_) => {}
            StmtArt::Zuweisung(z) => {
                // **«E4»:** an arena slot is written by `alloc`, never by
                // assignment -- the counter and the reservation count what
                // `alloc` does (`N214`, third face).
                self.arena_schreibziel(&z.ziel, lage);
                // **`M116` -- eine Zuweisung an ein unveraenderliches Band («NL.2.1»).**
                //
                // `mut` war bis zum 2026-08-19 ein Verbot ohne Biss. *Und M1 rechnet mit ihm:*
                // eine Tatsache ueber `x` stirbt beim Schreiben -- ohne Schreibrecht stirbt
                // sie gar nicht erst, und genau darauf ruht jede Verengung.
                // **`M118` -- ein `static` OHNE `mut` wird geschrieben.**
                //
                // Der Erzeuger ehrt die Deklaration seit jeher: mit `mut` faellt das `const`
                // weg und alles uebersetzt, ohne `mut` steht `static const` da -- *die
                // Unterscheidung existiert also und steuert die Absenkung.* Gehalten hat sie
                // niemand, und `gcc` war die einzige Instanz.
                //
                // Fuer eine Datei ausserhalb von `beispiele/` greift auch Stufe 9 des
                // Emissionswaechters nicht. Dann bleibt gar keine.
                // **Und ein FELD davon zaehlt mit** (nachgezogen 2026-08-20). `punkt.a = 5`
                // auf einem unveraenderlichen `static` ging durch, weil die Bedingung an
                // `suffixe.is_empty()` hing. *Die Regel war eine Zeile kuerzer als die
                // Deklaration.* Ausgenommen bleibt der Zeiger: durch ihn zu schreiben ist
                // erlaubt, ihn UMZUHAENGEN nicht.
                let statisch_unveraenderlich = !lage.lokal.contains_key(&z.ziel.basis.text)
                    && match self.unveraenderliche_statiken.get(&z.ziel.basis.text) {
                        Some(ist_zeiger) => z.ziel.suffixe.is_empty() || !ist_zeiger,
                        None => false,
                    };
                if statisch_unveraenderlich {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M118",
                            z.ziel.span,
                            format!("`{}` is a `static` without `mut`", z.ziel.basis.text),
                        )
                        .mit_notiz(
                            "the emitter honours this: without `mut` it writes `static \
                             const`, and the C compiler then refuses the assignment -- the \
                             refusal belongs here, where the declaration is",
                        ),
                    );
                }
                if z.ziel.suffixe.is_empty()
                    && self.unveraenderlich.contains(&z.ziel.basis.text)
                {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M116",
                            z.ziel.span,
                            format!("`{}` is bound without `mut`", z.ziel.basis.text),
                        )
                        .mit_notiz(
                            "a binding without `mut` promises that the name does not move \
                                -- and M1 counts on that: a fact about it would otherwise be \
                                killed by every write",
                        ),
                    );
                }
                // U9: M4 gilt auf BEIDEN Seiten. Ein Schreiben ausserhalb der Schranken ist
                // die gefaehrlichere Richtung, und sie lief hier am Index vorbei.
                self.index_pruefen(&z.ziel, lage);
                // **`N270` (lane 152) -- a bare store to an `atomic` is not a
                // `publishstmt`, and `SPRACHE.md` §11.3 says every store to an
                // atomic IS one.**
                //
                // Measured: `AT = w;` on `atomic AT : u32 relaxed` checks clean
                // and emits `AT = w;` over `_Atomic uint32_t AT` -- a plain
                // access, which C treats as `seq_cst` while the declaration
                // said `relaxed`, and which the C model (`C-SPEICHERMODELL.md`
                // §1c) makes stuck. Lowering the bare store to an explicit
                // `atomic_store_explicit` is no fix: the store is where the
                // payload promise stands (`publishes { … }` / `publishes
                // nothing`, held by V001-V004), and an explicit store without
                // one would carry the pairing past the checker in silence.
                //
                // It reports and does not return (the M143 shape): the overlap
                // still gets its range comparison, so a second fault there
                // keeps its own refusal.
                //
                // Only the GLOBAL answers: a parameter or `let` of the same
                // name shadows the atomic (`typ_von_ort` reads the local
                // first), and the store is theirs. `publishes` and `exchange`
                // are their own statements and never reach this arm.
                if !lage.lokal.contains_key(&z.ziel.basis.text)
                    && self.u.nennt_atomic(&self.modul, &z.ziel.basis.text)
                {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "N270",
                            z.ziel.span,
                            format!(
                                "`{}` is an `atomic` -- every store to an atomic is a \
                                 `publishstmt`, so a bare store has no form here",
                                z.ziel.basis.text
                            ),
                        )
                        .mit_notiz(
                            "the emitter would write a plain store to an `_Atomic` \
                             object -- C's default (`seq_cst`) instead of the declared \
                             order, and stuck in the C model (`C-SPEICHERMODELL.md` §1c)",
                        )
                        .mit_notiz(
                            "write `A = <value> publishes { … }` (`publishes nothing` \
                             where nothing is handed over), or `exchange` for \
                             read-modify-write",
                        ),
                    );
                }
                let ziel = self.u.typ_von_ort(&self.modul, &z.ziel, &lage.lokal);
                self.buche(&ziel);
                // **`N287` (lane 170) -- a whole array is not a store target.**
                //
                // Measured: `M[i] = M[j]` over `static mut M : [[u32; 4]; 3]`
                // checks clean -- both sides are `[u32; 4]`, and `passt` compares
                // shapes, which agree -- while the emitter writes `M[i] = M[j];`
                // into the C, and `cc` answers *assignment to expression with
                // array type*. The one-dimensional twin (`B = A` over two
                // `[u32; 4]`) is the same silence, one lane older: C has no
                // assignment of one array to another at any depth, so the rule
                // holds the dimension it can see instead of the depth.
                //
                // It reports and does not return (the `N270` shape): the overlap
                // still gets its range comparison, so a second fault there
                // keeps its own refusal.
                if matches!(ziel.durchgreifen(), Typ::Feld { .. }) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "N287",
                            z.ziel.span,
                            format!(
                                "`{}` names a whole array -- C has no assignment of one \
                                 array to another, so a whole array is never a store \
                                 target; write it element by element",
                                z.ziel.text()
                            ),
                        )
                        .mit_notiz(
                            "a row of a nested array is an array too: `M[i]` is \
                             `[u32; 4]`, and only `M[i][j]` is a value",
                        ),
                    );
                }
                let quelle = self.ausdruck(&z.wert, lage);
                self.rufe_im_ausdruck(&z.wert, lage);
                let ergebnis_typ = match z.op {
                    ZuwOp::Setzt => quelle,
                    // `a += b` ist `a = a + b`. Das GELESENE `a` traegt seine Fakten (V1/V2),
                    // das geschriebene seinen deklarierten Bereich -- ohne diese Trennung
                    // sieht `if z >= 1 { z -= 1; }` aus wie `z -= 1`.
                    op => {
                        let gelesen = self.mit_fakt(&z.ziel, ziel.clone(), lage);
                        self.rechnung_zuweisung(&gelesen, &quelle, op, &z.ziel, z.wert.span)
                    }
                };
                // Ein `wrapping`-Slot hat seinen Ueberlauf DEKLARIERT; dort ist er kein Befund.
                if !ziel.laeuft_um() {
                    self.passt_wert(
                        &z.wert,
                        &ergebnis_typ,
                        &ziel,
                        z.wert.span,
                        "the assignment",
                    );
                }
                self.schreiben_toetet_fakten(&z.ziel, lage);
            }
            StmtArt::Publish(p) => {
                // **«E4»:** like an assignment -- no store outside `alloc`.
                self.arena_schreibziel(&p.ziel, lage);
                self.index_pruefen(&p.ziel, lage);
                let ziel = self.u.typ_von_ort(&self.modul, &p.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&p.wert, lage);
                self.rufe_im_ausdruck(&p.wert, lage);
                self.passt(&quelle, &ziel, p.wert.span, "publication");
                self.schreiben_toetet_fakten(&p.ziel, lage);
            }
            StmtArt::Wenn(w) => {
                for (bedingung, rumpf) in &w.zweige {
                    let _ = self.ausdruck(bedingung, lage);
                    self.rufe_im_ausdruck(bedingung, lage);
                    let mut innen = lage.clone();
                    // V1 und V2: die geprueften Stellen sind im Zweig danach enger.
                    self.fakten_aus(bedingung, false, &mut innen);
                    self.block(rumpf, &mut innen, ergebnis);
                    self.geschriebenes_toeten(rumpf, lage);
                }
                if let Some(sonst) = &w.sonst {
                    let mut innen = lage.clone();
                    if let Some((bedingung, _)) = w.zweige.first() {
                        self.fakten_aus(bedingung, true, &mut innen);
                    }
                    self.block(sonst, &mut innen, ergebnis);
                    self.geschriebenes_toeten(sonst, lage);
                }
                // **V1 gilt auch fuer den Weg NACH einem Zweig, der immer verlaesst.**
                // `if a >= b { return a - b; }` -- was danach kommt, ist genau der Fall
                // `a < b`, und zwar syntaktisch, ohne Fixpunkt: der Zweig endet mit
                // `return`, `leave`, `next` oder einem Aufruf nach `never`. Ohne diese
                // Regel braucht der fruehe Rueckstieg ein `narrow`, und die Messlatte
                // („`narrow` <= 24 Fundstellen") faellt an einer Redewendung statt an der
                // Sprache.
                if w.sonst.is_none() && w.zweige.len() == 1 {
                    let (bedingung, rumpf) = &w.zweige[0];
                    if self.endet_immer(rumpf) {
                        self.fakten_aus(bedingung, true, lage);
                    }
                }
            }
            StmtArt::Match(m) => {
                let gegenstand = self.ausdruck(&m.gegenstand, lage);
                // **`M123` -- ein `match` ueber einen GRUND nennt jede Zeile seiner
                // Deklaration** (Stufe 7, 2026-08-21).
                //
                // *Diese Regel schliesst ein Loch, das der Erzeuger von `e` selbst
                // aufgemacht hat.* Vor Stufe 7 fiel `match e { … }` mit `M119` -- `e` war
                // ungebunden, also war die Frage nach den Zweigen nie faellig. Mit dem Typ
                // wurde sie es, und gemessen am 2026-08-21:
                //
                // ```text
                // match e { GibtsGarNicht => { return 1; } }   ->  0 Fehler
                // ```
                //
                // **Genau die Lochform, gegen die `D005` beim `tagged type` steht**, und die
                // Begruendung ist woertlich dieselbe: ein `reason` ist eine ABGESCHLOSSENE
                // Aufzaehlung, und die Sprache kennt keinen Sammelzweig. *Ohne diese Regel
                // waere die Abgeschlossenheit eine Zusage der Grammatik, die kein Pass
                // einloest.*
                //
                // > **Warum hier und nicht bei `D005`:** jener Pass baut seine Lage aus den
                // > PARAMETERN einer Funktion. `e` ist keiner -- es entsteht am `let … else`,
                // > und nur M1 traegt es. *Die Regel dort haette den einzigen Gegenstand
                // > nicht gesehen, ueber den sie spricht.*
                if let Typ::Grund(g) = &gegenstand {
                    // **`M125` -- ein `match` ueber einem Grund OHNE `exhaustive`.**
                    //
                    // `SPRACHE.md`:531 sagt, was das Wort heisst: *„der erzeugte
                    // C-`switch` hat KEIN `default`, und ein neuer Wert bricht die
                    // Uebersetzung"*. Fehlt es, ist die Aufzaehlung offen -- und dann kann
                    // eine Fallunterscheidung darueber nicht vollstaendig sein, waehrend
                    // die Sprache **keinen Sammelzweig kennt** (`SYNTAX.md`:736). *Es
                    // gaebe keine Form, die durchginge.*
                    //
                    // > Bis heute war `erschoepfend` in `pruefe-klauseln.py` als **TOT**
                    // > gefuehrt: das Wort stand da, der Leser fehlte. **Diese Regel und
                    // > der `switch` ohne `default:` sind zusammen sein erster.**
                    if !self.u.erschoepfende_gruende.contains(g) {
                        let kurz = crate::umgebung::kurzname(g).to_string();
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M125",
                                m.gegenstand.span,
                                format!(
                                    "`reason {kurz}` does not say `exhaustive`, so this \
                                     `match` cannot be complete"
                                ),
                            )
                            .mit_notiz(
                                "`exhaustive` means the generated `switch` has no \
                                 `default` and a new value breaks compilation \
                                 (SPRACHE.md) -- without it the enumeration is open",
                            )
                            .mit_notiz(
                                "and there is no catch-all branch in this language, so no \
                                 form of this `match` would go through",
                            ),
                        );
                    }
                    if let Some(faelle) = self.u.gruende.get(g).cloned() {
                        let genannt: Vec<&str> =
                            m.zweige.iter().map(|z| z.variante.text.as_str()).collect();
                        let kurz = crate::umgebung::kurzname(g).to_string();
                        let erfunden: Vec<&str> = genannt
                            .iter()
                            .copied()
                            .filter(|n| !faelle.iter().any(|f| f == n))
                            .collect();
                        if !erfunden.is_empty() {
                            let liste = erfunden
                                .iter()
                                .map(|x| format!("`{x}`"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M123",
                                    m.gegenstand.span,
                                    format!(
                                        "this `match` over `reason {kurz}` names {liste}, \
                                         which it does not declare"
                                    ),
                                )
                                .mit_notiz(format!(
                                    "declared are: {}",
                                    faelle.join(", ")
                                )),
                            );
                        }
                        let fehlt: Vec<&String> = faelle
                            .iter()
                            .filter(|f| !genannt.contains(&f.as_str()))
                            .collect();
                        if !fehlt.is_empty() {
                            let liste = fehlt
                                .iter()
                                .map(|x| format!("`{x}`"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M123",
                                    m.gegenstand.span,
                                    format!(
                                        "this `match` over `reason {kurz}` does not name: \
                                         {liste}"
                                    ),
                                )
                                .mit_notiz(
                                    "a `reason` is a CLOSED enumeration and there is no \
                                     catch-all branch -- the same rule `D005` holds over a \
                                     `tagged type`",
                                ),
                            );
                        }
                    }
                }
                for zweig in &m.zweige {
                    let mut innen = lage.clone();
                    // **V3 gilt auch fuer die Option, und bis zum 2026-08-19 tat sie es
                    // nicht.** Ein `match` ueber `option index into T` band `Some(i)` als
                    // `Unbekannt` -- und damit war `h.slots[i]` im `Some`-Zweig ungeprueft,
                    // obwohl gerade dieser Zweig weiss, dass `i` ein gueltiger Index ist.
                    // *Die Nutzlast von `Some` ist `index into T`, ohne den Sonderwert.*
                    if let (Some(binder), Some(nutz)) =
                        (&zweig.binder, option_nutzlast(&gegenstand))
                    {
                        if zweig.variante.text == "Some" {
                            innen.lokal.insert(binder.text.clone(), nutz);
                            self.block(&zweig.rumpf, &mut innen, ergebnis);
                            self.geschriebenes_toeten(&zweig.rumpf, lage);
                            continue;
                        }
                    }
                    // V3: der Binder traegt die Nutzlast SEINER Variante.
                    if let (Some(binder), Typ::Summe { varianten, .. }) =
                        (&zweig.binder, gegenstand.durchgreifen())
                    {
                        let nutzlast = varianten
                            .iter()
                            .find(|(n, _)| *n == zweig.variante.text)
                            .and_then(|(_, t)| t.clone())
                            .unwrap_or(Typ::Unbekannt);
                        innen.lokal.insert(binder.text.clone(), nutzlast);
                    } else if let Some(binder) = &zweig.binder {
                        innen.lokal.insert(binder.text.clone(), Typ::Unbekannt);
                    }
                    self.block(&zweig.rumpf, &mut innen, ergebnis);
                    self.geschriebenes_toeten(&zweig.rumpf, lage);
                }
            }
            StmtArt::Narrow(n) => {
                let vorher = self.u.typ_von_ort(&self.modul, &n.ort, &lage.lokal);
                self.buche(&vorher);
                let mut innen = lage.clone();
                self.block(&n.sonst, &mut innen, ergebnis);
                self.geschriebenes_toeten(&n.sonst, lage);
                // U6: **der `else`-Zweig MUSS verlassen.** Ohne diese Pruefung installiert
                // ein leeres `else { }` denselben Bereich wie ein `else { return … }` --
                // und die Einengung gilt auf einem Weg, auf dem sie nie geprueft wurde.
                if !self.endet_immer(&n.sonst) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M105",
                            n.sonst.span,
                            "the `else` branch of a `narrow` must return or diverge",
                        )
                        .mit_notiz(
                            "SYNTAX.md §7: `narrow place to range else { … }` is a \
                                checked narrowing with a named exit",
                        ),
                    );
                }
                // Der `else`-Zweig divergiert oder kehrt zurueck; danach gilt die Zusage.
                match &n.ziel {
                    NarrowZiel::Bereich(bereich) => {
                        // **«F»: dieselbe Anweisung, ein anderer Fakt.** Ist die Stelle ein
                        // Gleitkommawert, sind die Grenzen keine ganzen Zahlen -- und ein
                        // ganzzahliger Fakt darueber waere schlicht falsch.
                        let ist_gleit = matches!(
                            self.u
                                .typ_von_ort(&self.modul, &n.ort, &lage.lokal)
                                .durchgreifen(),
                            Typ::Gleitkomma(_)
                        );
                        if ist_gleit {
                            if let (Some(lo), Some(hi), Some((schluessel, indizes))) = (
                                self.u.gleitwert(&bereich.von),
                                self.u.gleitwert(&bereich.bis),
                                schluessel_und_indizes(&n.ort),
                            ) {
                                lage.fakten.push(Fakt::FIntervall {
                                    schluessel,
                                    indizes,
                                    lo,
                                    hi,
                                });
                            }
                            return;
                        }
                        // **Eine WERTGETRAGENE obere Schranke** -- `narrow i to 0 ..< k`.
                        //
                        // `konst_wert` findet dort nichts, denn `k` ist keine Konstante. Die
                        // Aussage ist aber genau die, die M1 seit jeher als `Fakt::Beziehung`
                        // fuehrt: der Vergleich zweier STELLEN. *Es fehlte der Traeger, nicht
                        // die Form.*
                        if self.u.konst_wert(&self.modul, &bereich.bis).is_none() {
                            if let (ExprArt::Ort(ziel), Some((links, indizes))) =
                                (&bereich.bis.art, schluessel_und_indizes(&n.ort))
                            {
                                if let Some((rechts, _)) = schluessel_und_indizes(ziel) {
                                    lage.fakten.push(Fakt::Beziehung {
                                        links,
                                        op: if bereich.exklusiv {
                                            BinOp::Kleiner
                                        } else {
                                            BinOp::KleinerGleich
                                        },
                                        rechts,
                                        indizes,
                                    });
                                }
                            }
                        }
                        let von = self.u.konst_wert(&self.modul, &bereich.von);
                        let bis = self.u.konst_wert(&self.modul, &bereich.bis);
                        if let (Some(lo), Some(hi), Some((schluessel, indizes))) =
                            (von, bis, schluessel_und_indizes(&n.ort))
                        {
                            let hi = if bereich.exklusiv { hi - 1 } else { hi };
                            lage.fakten.push(Fakt::Bereich {
                                schluessel,
                                indizes,
                                min: lo,
                                max: hi,
                            });
                        }
                    }
                    // **«F»: beide Bits auf einmal.** `finite` heisst nicht NaN UND nicht
                    // unendlich -- eine Pruefung, zwei Flanken. *Der `else`-Zweig ist der
                    // NaN-Weg, und damit steht in Gabbro als EINE Anweisung, was der Korpus
                    // von Hand als Disjunktion schreibt.*
                    NarrowZiel::Endlich(_) => {
                        if let Some((schluessel, indizes)) = schluessel_und_indizes(&n.ort) {
                            lage.fakten.push(Fakt::Endlich {
                                schluessel,
                                indizes,
                                nan: true,
                                unendlich: true,
                            });
                        }
                    }
                }
            }
            StmtArt::Bricht(b) => self.unterblock(&b.rumpf, lage, ergebnis),
            StmtArt::Sperrt(l) => self.unterblock(&l.rumpf, lage, ergebnis),
            StmtArt::Observiert(o) => self.unterblock(&o.rumpf, lage, ergebnis),
            StmtArt::Schleife(sch) => {
                // **`M133`: a loop `invariant` has to name something.**
                //
                // `invariant true` is a promise about nothing and looks exactly like a
                // promise about something. *A clause nobody honours is worse than none* --
                // literally the finding that cost `beispiele/05` its `protects` clause
                // (`H007`/`H008`).
                let inv = match sch.as_ref() {
                    Schleife::Traverse(x) => (&x.invariante, x.span),
                    Schleife::Retry(x) => (&x.invariante, x.span),
                    Schleife::Forever(x) => (&x.invariante, x.span),
                };
                if let (Some(pred), span) = (inv.0.as_ref(), inv.1) {
                    let mut namen = Vec::new();
                    sammle_namen_pred(pred, &mut namen);
                    if namen.is_empty() {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M133",
                                span,
                                "this loop `invariant` names nothing".to_string(),
                            )
                            .mit_notiz(
                                "a promise about nothing looks exactly like a promise about \
                                 something -- and the loop then carries a counted duty that \
                                 no prover can fail",
                            ),
                        );
                    }
                }
                // Schleifen tragen keine Fakten hinein -- die Invariante der Traversierung
                // tut das, und die gehoert dem Beweiser.
                // **V4 -- loops carry no taints inward either** (spec §2c): every taint
                // held here expires; a value needed across iterations is re-read
                // inside. Same sentence as V1-V3, same place.
                frische_alle_toeten(lage);
                let mut innen = Lage {
                    lokal: lage.lokal.clone(),
                    fakten: Vec::new(),
                    frisch: HashMap::new(),
                    veraltet: lage.veraltet.clone(),
                };
                let rumpf = match sch.as_ref() {
                    Schleife::Traverse(t) => {
                        let binder = self.binder_typ(t, lage);
                        innen.lokal.insert(t.variable.text.clone(), binder);
                        if let Some(g) = &t.gegenstand {
                            let _ = self.ausdruck(g, lage);
                        }
                        self.zaehler_erbt_die_schranke(t, lage, &mut innen);
                        &t.rumpf
                    }
                    Schleife::Retry(r) => {
                        let _ = self.ausdruck_opt(r.schranke.clone(), lage);
                        &r.rumpf
                    }
                    Schleife::Forever(f) => {
                        let _ = self.ausdruck_opt(f.je_durchgang.clone(), lage);
                        &f.rumpf
                    }
                };
                self.block(rumpf, &mut innen, ergebnis);
                self.geschriebenes_toeten(rumpf, lage);
            }
            StmtArt::Return(Some(e)) => {
                let t = self.ausdruck(e, lage);
                self.rufe_im_ausdruck(e, lage);
                // **Ein `return` eines GRUNDES ist die Fehlerrueckgabe** (Stufe 7,
                // 2026-08-21) -- und sie geht gegen das `or R` der Signatur, nicht gegen
                // den Erfolgstyp.
                //
                // *Es braucht dafuer kein neues Wort und keine neue Anweisung:* ein
                // Grundwert kann nie den Erfolgstyp haben, also ist die Form eindeutig.
                // **Das ist die Bedingung, unter der die Ersparnis erlaubt ist** -- ohne sie
                // waere es ein stiller Verleser, und die kosten in diesem Ordner mehr als
                // eine fehlende Form (`SYNTAX.md`, zum Verbundliteral).
                if let Typ::Grund(g) = &t {
                    let g = g.clone();
                    match self.fehlerkanal.clone() {
                        Some(k) if k == g => {}
                        Some(k) => {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M122",
                                    e.span,
                                    format!(
                                        "this returns a `reason {g}`, but the signature \
                                         declares `or {k}`"
                                    ),
                                )
                                .mit_notiz(
                                    "a function has exactly one error channel, and it \
                                     stands in its signature",
                                ),
                            );
                        }
                        None => {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M122",
                                    e.span,
                                    format!(
                                        "this returns a `reason {g}`, but the signature \
                                         declares no `or <reason>`"
                                    ),
                                )
                                .mit_notiz(
                                    "`-> T or R` is where a function says that it can fail \
                                     and at what -- without it there is no channel to \
                                     return through",
                                ),
                            );
                        }
                    }
                    return;
                }
                if let Some(z) = ergebnis {
                    let z = z.clone();
                    self.passt_wert(e, &t, &z, e.span, "the return value");
                } else {
                    // **`M148` -- a `return` with a value in a function that declares
                    // none.**
                    //
                    // A function without a result lowers to `void`, and a `return e;`
                    // in it becomes `return <e>;` in a `void` function -- refused by
                    // both C families (`-Werror=return-type`). Measured 2026-09-12 on
                    // `beispiele/gift/776`: the checker said 0 errors, the emitter
                    // wrote `return m;` into `static void kreis`, and `cc` and `clang`
                    // refused it line for line. *Three stages passed it, and the
                    // fourth is not part of the language* -- the same shape as
                    // `N044`'s, one construct further out.
                    //
                    // The bare `return;` stays silent: a result-less function ends in
                    // `return;` or falls to its closing brace, which SYNTAX.md reads
                    // as sugar for `return;`. Only a value where none is declared
                    // falls here.
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M148",
                            e.span,
                            format!(
                                "`return` carries `{}`, but this function answers nothing",
                                t.text()
                            ),
                        )
                        .mit_notiz(
                            "a `return <value>;` in a function without `-> T` lowers to \
                             `return <value>;` in a `void` function -- and the two C \
                             families refuse exactly that line, where the checker \
                             before this rule compared the value only against a result \
                             that was never declared",
                        )
                        .mit_notiz(
                            "either declare the result the value answers, or return \
                             without one",
                        ),
                    );
                }
            }
            StmtArt::Ruf(r) => {
                let _ = self.ruf(r, lage);
                self.rufe_toeten_fakten(&rufnamen_im_ruf(r), lage);
            }
            // **Lane E2:** a resolved library call is checked like any call
            // (arity, argument shape and range, `requires`, result
            // narrowing) over the callee's declared signature, and kills
            // facts like one. Unresolved it stays what E1 made it: typed
            // arguments, no callee, `N057` from the name pass.
            StmtArt::LibraryCall(r) => {
                let mut argtypen = Vec::new();
                for a in &r.args {
                    argtypen.push((self.ausdruck(a, lage), a.span));
                    self.rufe_im_ausdruck(a, lage);
                }
                if let Some(z) =
                    self.u.bibliothek(&self.modul, &r.library.text, &r.function.text)
                {
                    if let Some(mut sig) = self.u.funktionen.get(&z.name).cloned() {
                        // **Lane E5:** the region fills the library function's
                        // last parameter (a pointer at the payload table), so
                        // the call passes one argument short and is held
                        // against the shortened signature. `requires` over the
                        // filled parameter goes quiet here (`position` misses
                        // it) -- the translation stage refuses it by name
                        // (`N234`) instead of checking around it.
                        if let Some(n) =
                            crate::uebersetzung::fuell_index(&self.u, &self.modul, r)
                        {
                            sig.parameter.truncate(n);
                            argtypen.truncate(n);
                        }
                        let ziel = format!("@{}#{}", r.library.text, r.function.text);
                        let _ = self.ruf_aufgeloest(&ziel, r.span, false, &argtypen, &sig);
                    }
                    let pfad = gabbro_syntax::ast::Pfad {
                        teile: z
                            .name
                            .split("::")
                            .map(|t| gabbro_syntax::ast::Ident {
                                text: t.to_string(),
                                span: r.span,
                            })
                            .collect(),
                        span: r.span,
                    };
                    self.rufe_toeten_fakten(&[&pfad], lage);
                }
            }
            StmtArt::AwaitLoad(a) => {
                let t = self.u.typ_von_ort(&self.modul, &a.quelle, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(a.name.text.clone(), t);
                // **V4 -- an atomic load rebinds like any non-`let` binding**: the map
                // grows only at `let`, so the name is cleared, never grown.
                lage.frisch.remove(&a.name.text);
                lage.veraltet.remove(&a.name.text);
            }
            // **An `exchange` binds ONE of two things, and until 2026-08-31 it bound the
            // first one twice.**
            //
            // `update(v) { … }` hands back the OLD value of the place, so the name carries
            // the place's type. **`when … returns e` hands back whether the swap
            // HAPPENED** -- the emitter writes `bool genommen; genommen =
            // atomic_compare_exchange_strong_explicit(…)` (`beispiele/35-tausch.gab`), and
            // this pass called it `u32`. *Three stages agreed with each other and the
            // fourth wrote something else* -- found by `M135`, which is the first rule that
            // ever compared the two sides of this binding.
            //
            // And the second half is the RESULT type of the `update` body. A `return` in
            // there yields the NEW value of the place, not the enclosing function's result
            // -- passing `ergebnis` down was right in the corpus by accident
            // (`beispiele/05-nebenlaeufigkeit.gab` counts a `Zaehlerwert` inside a function
            // returning `Zaehlerwert`) and wrong at `beispiele/gift/209`, where the same
            // body sits in a `check` and `M135` read its `return v + 1` against `bool`.
            StmtArt::Exchange(e) => {
                // **«E4»:** an exchange writes -- no RMW outside `alloc`.
                self.arena_schreibziel(&e.ort, lage);
                let t = self.u.typ_von_ort(&self.modul, &e.ort, &lage.lokal);
                self.buche(&t);
                let gebunden = match &e.form {
                    XForm::Vergleich { .. } => Typ::Wahrheit,
                    XForm::Update { .. } => t.clone(),
                };
                lage.lokal.insert(e.name.text.clone(), gebunden);
                if let XForm::Update { binder, rumpf, .. } = &e.form {
                    let mut innen = lage.clone();
                    innen.lokal.insert(binder.text.clone(), t.clone());
                    self.block(rumpf, &mut innen, Some(&t));
                }
                // **V4 -- like `await`: a non-`let` binding rebinds, never grows.**
                lage.frisch.remove(&e.name.text);
                lage.veraltet.remove(&e.name.text);
                self.schreiben_toetet_fakten(&e.ort, lage);
            }
            StmtArt::Return(None) | StmtArt::Leave(_) | StmtArt::Next(_) => {}
        }
    }

    /// Verlaesst dieser Block seinen Weg immer? Rein syntaktisch, ohne Fixpunkt.
    fn endet_immer(&self, b: &Block) -> bool {
        let Some(letzte) = b.anweisungen.last() else {
            return false;
        };
        match &letzte.art {
            StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
            // Ein Aufruf einer Funktion nach `never` kehrt nicht zurueck.
            StmtArt::Ruf(r) => {
                // **An indirect call does not end a body.** `-> never` is read off the
                // callee's declared result, and a `fn(…)` type can name `never` as its result
                // too -- but this rule asks whether CONTROL returns, and the passes that live
                // on that answer (divergence, `S002`) all resolve by name. *Answering `false`
                // here is the safe direction: a body that does not obviously end must still
                // end properly, and the rule that says so keeps firing.*
                let name = r
                    .path()
                    .and_then(|p| p.teile.last())
                    .map(|i| i.text.as_str())
                    .unwrap_or_default();
                matches!(
                    self.u.funktionen.get(name).and_then(|s| s.ergebnis.clone()),
                    Some(Typ::Nie)
                )
            }
            StmtArt::Wenn(w) => {
                w.sonst.as_ref().is_some_and(|s| self.endet_immer(s))
                    && w.zweige.iter().all(|(_, r)| self.endet_immer(r))
            }
            StmtArt::Match(m) => m.zweige.iter().all(|z| self.endet_immer(&z.rumpf)),
            _ => false,
        }
    }

    /// `a += b` rechnet im Bereich von `a` -- und genau dort faellt der Ueberlauf.
    fn rechnung_zuweisung(
        &mut self,
        ziel: &Typ,
        quelle: &Typ,
        op: ZuwOp,
        ort: &Ort,
        span: Span,
    ) -> Typ {
        let (Some(a), Some(b)) = (ziel.bereich(), quelle.bereich()) else {
            return Typ::Unbekannt;
        };
        let r = match op {
            ZuwOp::Plus => typen::addiere(&a, &b),
            ZuwOp::Minus => typen::subtrahiere(&a, &b),
            ZuwOp::Und => typen::bitweise(&a, &b, typen::BitOpArt::Und),
            ZuwOp::Oder => typen::bitweise(&a, &b, typen::BitOpArt::Oder),
            ZuwOp::Setzt => return quelle.clone(),
        };
        if r.laeuft_ueber && !ziel.laeuft_um() {
            self.ueberlauf(span, &a, &b, op_wort(op), ort);
        }
        match r.bereich {
            Some(b) => Typ::Ganzzahl(b),
            None => Typ::Unbekannt,
        }
    }

    // -- Ausdruecke ---------------------------------------------------------------------

    fn ausdruck_opt(&mut self, e: Expr, lage: &Lage) -> Typ {
        self.ausdruck(&e, lage)
    }

    fn ausdruck(&mut self, e: &Expr, lage: &Lage) -> Typ {
        let t = self.ausdruck_roh(e, lage);
        self.buche(&t);
        t
    }

    fn ausdruck_roh(&mut self, e: &Expr, lage: &Lage) -> Typ {
        match &e.art {
            // **`&f` -- and `M127`, the rule the whole contract rests on** (2026-08-21).
            //
            // The type of `&f` is the contract of `f` itself, read off `f`'s declaration and
            // turned into a `Typ::FnPtr`. **That is what makes the contract at the pointer
            // type sound rather than decorative:** the assignment to a `fn(…)`-typed field is
            // an ordinary type comparison, and `M104` then holds the promise the producer
            // makes against the promise the type demands.
            //
            // > *Without this line the contract would be a wish.* A field could declare
            // > `effects { pure }` and be filled with a function that writes the world, and
            // > every pass downstream would compute with the wish.
            //
            // `M127` fires where `&` names something that is not a declared function at all --
            // a variable, a type, a typo. **Not `M119`:** `M119` says "declared nowhere", and
            // the fix there is a declaration; here the name may well exist and simply not be
            // a function, and the fix is a different one.
            ExprArt::FnWert(p) => {
                let Some(sig) = self.u.funktion(&self.modul, p) else {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M127",
                            e.span,
                            format!("`&{}` does not name a function", p.text()),
                        )
                        .mit_notiz(
                            "`&` makes a FUNCTION into a value; there is no address-of for a \
                             variable or a type in Gabbro",
                        ),
                    );
                    return Typ::Unbekannt;
                };
                Typ::FnPtr(Box::new(crate::typen::FnPtrContract {
                    // A DECLARATION always names its parameters -- so `Some`, always. The
                    // `None` case comes only from a pointer TYPE (`fn(u8)`).
                    parameters: sig
                        .parameter
                        .iter()
                        .map(|(n, t)| (Some(n.clone()), t.clone()))
                        .collect(),
                    result: sig.ergebnis.clone().map(Box::new),
                    effects: sig.effect_list.clone(),
                    has_effects: !sig.effect_list.is_empty(),
                    costs: sig.cost_bound,
                    has_costs: sig.cost_bound.is_some(),
                    // **Lane 177: the producer's LOGIC rides along.** The `requires` and
                    // `ensures` of `f` itself travel in the value's type, so that the
                    // assignment to a `fn(…)` slot can be held against the slot's
                    // contract -- contravariant in `requires`, covariant in `ensures`.
                    // The `producer` names `f`: without it the slot comparison sees two
                    // contracts and cannot say whose refinement it is.
                    requires: sig.requires.clone(),
                    ensures: sig.ensures.clone(),
                    producer: Some(p.text()),
                }))
            }
            // **`M139` -- a literal so wide that the TYPE falls away, and with it every rule
            // that would have judged it.**
            //
            // Gabbro's literals are `u128`; `IntBereich` is `i128`, because it has to hold a
            // signed and an unsigned 64-bit range in one shape. The conversion between the
            // two is exact up to `i128::MAX` and impossible above it -- and until 2026-09-02
            // the impossible case answered `Typ::Unbekannt`.
            //
            // *`Unbekannt` is not a refusal. It is an acquittal that reads like caution.*
            // Every downstream rule asks the type first and says nothing when there is none,
            // so ONE lossy conversion silenced the whole ladder at once. Measured, on a
            // `table T count 8`:
            //
            // ```text
            // T.slots[170141183460469231731687303715884105727]   -- i128::MAX
            //   -> error: [M103] the index has `i64 in ... `, the array has 8 elements
            // T.slots[170141183460469231731687303715884105728]   -- i128::MAX + 1
            //   -> 3 items, 0 errors, 0 hints
            //   -> emitted as `T_speicher.slots[3402823669...455].a` over `T_slot slots[8];`
            // ```
            //
            // **The bound holds for every index up to `2^127 - 1` and then stops holding**,
            // and the C that comes out reads out of bounds. `M101` (width), `M104` (range)
            // and `M117` go quiet in the same step and for the same reason.
            //
            // > **The fence, and not the widening** -- the fork `N050` already stood at.
            // > Making `IntBereich` wider moves the hole from `2^127` to wherever the next
            // > type ends and buys nothing: **the widest integer type Gabbro HAS is 64 bits**,
            // > so a literal above `i128::MAX` is not a value any expression can take. There
            // > is nothing here to compute more carefully -- there is a number to refuse.
            //
            // Found by `instrumente/fuzze-grenzen.py`, in the sweep that took the ladder to
            // every rule of the grammar that has a literal slot.
            // **«SG-24»: a count is a number between nothing and everything.**
            //
            // At most every entry satisfies the predicate, at fewest none -- so the
            // result is `0 ..= N` with `N` the domain bound the declaration names
            // (`domaenenschranke`, the SAME reader `kosten.rs` and «H2.1» use). Where
            // the declaration names no bound there is no narrowing either (W10: a
            // bound that is not proved is not narrowed) -- and the domain itself was
            // already refused by `domaene.rs` (`D025`), so one fault keeps one refusal.
            ExprArt::Zaehle { domaene, .. } => {
                let sicht = crate::domaene::Sicht {
                    u: self.u,
                    modul: &self.modul,
                    lokal: &lage.lokal,
                };
                match sicht.domaenenschranke(domaene) {
                    Some(n) => Typ::Ganzzahl(IntBereich::genau(64, false, 0, n)),
                    None => Typ::Unbekannt,
                }
            }
            ExprArt::Zahl(v) => match i128::try_from(*v) {
                Ok(w) => Typ::Ganzzahl(IntBereich::konstante(w)),
                Err(_) => {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M139",
                            e.span,
                            format!(
                                "the literal {v} is wider than `i128`, so it has no type -- \
                                 and a value without a type is judged by no rule"
                            ),
                        )
                        .mit_notiz(
                            "the widest integer type Gabbro has is 64 bits; this literal is \
                             above `i128::MAX` and can be the value of no expression",
                        )
                        .mit_notiz(
                            "without this refusal the index bound `M103` goes silent on it, \
                             and the emitter writes the number into C as an array subscript",
                        ),
                    );
                    Typ::Unbekannt
                }
            },
            // **«F»: ein Literal ist bekannt ENDLICH und nicht NaN.** Das ist der
            // Unterschied zu einem deklarierten Wert, und er ist der Grund, warum `narrow …
            // to finite` nur dort noetig ist, wo etwas GERECHNET oder UEBERGEBEN wurde.
            ExprArt::Gleitkomma {
                bits,
                dyadisch,
                gerundet,
            } => {
                // **`F002` -- und die Regel kam aus dem Korpus, nicht aus dem Entwurf.**
                //
                // Die geplante Fassung hiess „exakt darstellbar, sonst Absage". An 340
                // Literalen eines echten Renderers gemessen waeren damit 53 gefallen,
                // darunter ln 2 und 2 pi (`FRAGMENTE.md`, «F0»/FF4). Eine transzendente
                // Konstante ist in KEINER binaeren Breite exakt; ihre Dezimalform ist schon
                // eine Naeherung.
                //
                // *Verboten ist darum nicht das Inexakte, sondern das STILLSCHWEIGEND
                // Inexakte* -- genau der Satz, den `wrapping` ueber den Ueberlauf sagt.
                if !dyadisch && !gerundet {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F002",
                            e.span,
                            "this literal is not exactly representable in binary",
                        )
                        .mit_notiz(
                            "write `rounded` after it if the rounding is meant -- what is \
                                forbidden is not the inexact but the SILENTLY inexact",
                        ),
                    );
                }
                let mut b = crate::typen::FBereich::punkt(f64::from_bits(*bits));
                b.gerundet = *gerundet;
                Typ::Gleitkomma(b)
            }
            ExprArt::Wahr | ExprArt::Falsch => Typ::Wahrheit,
            ExprArt::Ergebnis => Typ::Unbekannt,
            // **`R::F` -- der Grundwert bekommt hier seinen Typ** (Stufe 7, 2026-08-21).
            //
            // Bis heute war dieselbe Zeichenfolge ein `Ort` namens `R` mit einem Feld `F`,
            // und M1 sagte `M119` (*„`R` is declared nowhere"*). **Der Fehlerkanal hatte
            // damit eine Deklaration und keine Schreibform** -- «B9» ein zweites Mal.
            //
            // Zwei Absagen, und sie sind getrennt, weil sie zwei verschiedene Fehler sind:
            // `M120` sagt, dass es den GRUND nicht gibt, `M121`, dass es den FALL nicht
            // gibt. *Eine gemeinsame Meldung haette den Tippfehler im Fallnamen wie eine
            // fehlende Deklaration aussehen lassen.*
            ExprArt::Grund { grund, fall } => {
                let Some((voll, faelle)) = self.u.grund(&self.modul, &grund.text) else {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M126",
                            grund.span,
                            format!("`{}` is not a declared `reason`", grund.text),
                        )
                        .mit_notiz(
                            "`R::F` is the value of a reason -- the only form in which a \
                             body produces one",
                        ),
                    );
                    return Typ::Unbekannt;
                };
                if !faelle.contains(&fall.text) {
                    let liste = faelle.join(", ");
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M121",
                            fall.span,
                            format!("`{}` is not a case of `reason {}`", fall.text, grund.text),
                        )
                        .mit_notiz(format!("declared are: {liste}")),
                    );
                    return Typ::Unbekannt;
                }
                Typ::Grund(voll)
            }
            ExprArt::Klammer(i) => self.ausdruck_roh(i, lage),
            ExprArt::Ort(o) => {
                // **`u32::max` is a NUMBER, and until 2026-09-01 M1 did not know it.**
                //
                // «G5» put both segments into the vocabulary and the constant folder has read
                // the pair ever since -- `const G : u32 = u32::max;` lowers to
                // `#define G 4294967295u`, correctly. **In an EXPRESSION nobody asked it.**
                // Measured: `return w ^ u32::max;` with `w : u16` passed with 0 errors and                // booked two of three expressions as untyped, while the same mask spelled
                // `4294967295` falls at `M104` *(`u16 ^ u32 in 4294967295 .. 4294967295`
                // leaves the width of the result type)* and at `M101`.
                //
                // > *Two spellings of one number, one of them checked.* The named limit is
                // > the form this language offers instead of a magic constant -- and it was
                // > the one that escaped the width rule.
                //
                // It stands BEFORE `name_aufloesen`, because `u32` is not a name a body
                // declares and asking that question first is how the form got treated as a
                // place. The value comes from `umgebung::grenzwort`, the same reader the
                // folder uses (W7).
                //
                // PLAN-BITS §1: a sugared limit (`u13::max`) answers the SUGAR's
                // exact bound (8191), in the storage word's width -- the same
                // shape the desugared range gives the type itself.
                if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&o.basis.text) {
                    if o.suffixe.len() == 1 {
                        if let Some(OrtSuffix::Feld(f)) = o.suffixe.first() {
                            let speicher = gabbro_syntax::zucker_speicher(&o.basis.text)
                                .and_then(crate::umgebung::breite_von);
                            if let (Some((breite, vz)), Some(w)) = (
                                speicher,
                                match f.text.as_str() {
                                    "max" => Some(hi),
                                    "min" => Some(lo),
                                    _ => None,
                                },
                            ) {
                                return Typ::Ganzzahl(IntBereich::genau(breite, vz, w, w));
                            }
                        }
                    }
                }
                if let Some((breite, vz, w)) = crate::umgebung::grenzwort(o) {
                    return Typ::Ganzzahl(IntBereich::genau(breite, vz, w, w));
                }
                // **And a MISSPELLED limit is the same defect, one field name over.**
                //
                // `u32::gross` measured on the repaired binary: 0 errors, 0 hints, two of
                // three expressions untyped -- and `gabbro emit` writes `u32->gross`.
                // *Repairing `max` and `min` alone would have closed the two spellings
                // somebody happened to try and left the family open.*
                //
                // An integer word has exactly two members, and neither a declaration nor a
                // `let` can give it a third: `u32` is a WORD, not a name a body binds. So
                // this is not `M119` ("declared nowhere", fixed by a declaration) -- there
                // is no declaration that would fix it.
                //
                // PLAN-BITS §1: a sugared width has the same two members. `u13::gross`
                // is refused here, beside `u32::gross` -- the sugar spelling is a
                // word where a type is read, and words have no third member.
                if let (Some(kw), 1, Some(OrtSuffix::Feld(f))) =
                    (gabbro_syntax::kw::Kw::suche(&o.basis.text), o.suffixe.len(), o.suffixe.first())
                {
                    if kw.ist_intty() {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M138",
                                e.span,
                                format!(
                                    "`{}::{}` -- an integer word has `max` and `min`, and \
                                     nothing else",
                                    o.basis.text, f.text
                                ),
                            )
                            .mit_notiz(
                                "`u32` is a word of the closed vocabulary, not a name a \
                                 declaration could give another member",
                            ),
                        );
                        return Typ::Unbekannt;
                    }
                }
                if o.suffixe.len() == 1
                    && gabbro_syntax::zucker_speicher(&o.basis.text).is_some()
                {
                    if let Some(OrtSuffix::Feld(f)) = o.suffixe.first() {
                        if f.text != "max" && f.text != "min" {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M138",
                                    e.span,
                                    format!(
                                        "`{}::{}` -- an integer word has `max` and `min`, \
                                         and nothing else",
                                        o.basis.text, f.text
                                    ),
                                )
                                .mit_notiz(
                                    "`u13` is sugar for the storage width plus the exact \
                                     range -- a word where a type is read, with no third \
                                     member",
                                ),
                            );
                            return Typ::Unbekannt;
                        }
                    }
                }
                // **Lane 167: a bare nullary case -- `Leer` where the type is the sum.**
                //
                // A case without a payload needs no call to carry it, so it stands as a
                // bare name -- the model's `fall` with an empty payload, the same value
                // `Leer()` builds. It stands BEFORE `name_aufloesen`: a case is declared
                // nowhere as a VALUE, so `M119` would refuse exactly the form this rule
                // gives a type. Anything the value namespace already binds (a local, a
                // global, a function, a table, an arena) wins -- the mirror of the
                // function-wins rule at the call form, and for the same reason: no
                // behaviour change where a name already means something. Integer words
                // and their sugar never name a case here either: `return u13;` stays
                // `M119`'s, even where a perverse declaration spells a case `u13`.
                if o.suffixe.is_empty() && !o.text().contains("::") {
                    let n = o.basis.text.clone();
                    let ist_wort = gabbro_syntax::kw::Kw::suche(&n).is_some_and(|k| k.ist_intty())
                        || gabbro_syntax::zucker_speicher(&n).is_some();
                    // **The function question is asked module-aware, not bare-keyed.**
                    // `name_aufloesen` below reads `funktionen` by its bare name and sees
                    // only root functions; a same-module function of the case's name must
                    // still win here, or the bare form and the call form of one name would
                    // answer different declarations.
                    let pfad = gabbro_syntax::ast::Pfad {
                        teile: vec![o.basis.clone()],
                        span: o.basis.span,
                    };
                    let bekannt = ist_wort
                        || lage.lokal.contains_key(&n)
                        || self.u.suche_global(&self.modul, &n).is_some()
                        || self.u.funktion(&self.modul, &pfad).is_some()
                        || self.u.tabellen.keys().any(|k| k == &n || k.rsplit("::").next() == Some(n.as_str()))
                        || self.u.arenen.keys().any(|k| k == &n || k.rsplit("::").next() == Some(n.as_str()));
                    if !bekannt {
                        // **A function of this name stands elsewhere in the unit.**
                        // Same reading as at the call form: the emitter lowers a call
                        // of this name as the function, so a construction here would
                        // miscompile. Refused instead of miscompiled.
                        if self.u.funktionsname_belegt(&n) {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "N280",
                                    e.span,
                                    format!(
                                        "`{n}` shares its name with a declared function -- \
                                         a construction names its case, and a use of this \
                                         name lowers as the function"
                                    ),
                                )
                                .mit_notiz(
                                    "the emitter reads callees by their bare name across the \
                                     whole unit; which of the two readings the C carries cannot \
                                     be told apart there",
                                ),
                            );
                        } else {
                        match self.u.variante(&self.modul, &n) {
                            crate::umgebung::VariantenFund::Eine(t) => {
                                if t.nutzlast.is_some() {
                                    let kurz = crate::umgebung::kurzname(&t.summe);
                                    self.absagen.schiebe(
                                        Absage::fehler(
                                            "N283",
                                            e.span,
                                            format!(
                                                "`{n}` is a case of `{kurz}` with a payload -- \
                                                 a bare name carries none"
                                            ),
                                        )
                                        .mit_notiz(
                                            "a case with a payload constructs as \
                                             `Case(payload)`; the bare name is the nullary \
                                             form, and it stands only where there is nothing \
                                             to carry",
                                        ),
                                    );
                                    return Typ::Unbekannt;
                                }
                                self.buche(&t.summe_typ);
                                return t.summe_typ.clone();
                            }
                            crate::umgebung::VariantenFund::Mehrere(summen) => {
                                let liste = summen
                                    .iter()
                                    .map(|s| format!("`{}`", crate::umgebung::kurzname(s)))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "N280",
                                        e.span,
                                        format!(
                                            "`{n}` names a case of several `tagged` types \
                                             ({liste}) -- and a construction names its case, \
                                             not its type"
                                        ),
                                    )
                                    .mit_notiz(
                                        "the case index the model carries (`Expr.fall cs i \
                                         nutz`) is read off ONE case list; with two lists \
                                         there is no index",
                                    ),
                                );
                                return Typ::Unbekannt;
                            }
                            crate::umgebung::VariantenFund::Keine => {
                                if self.u.hat_markierte() {
                                    self.absagen.schiebe(
                                        Absage::fehler(
                                            "N280",
                                            e.span,
                                            format!(
                                                "`{n}` names no value and no case of the \
                                                 `tagged` types declared here"
                                            ),
                                        )
                                        .mit_notiz(
                                            "a nullary case stands as its bare name -- this \
                                             name is neither a bound value nor such a case",
                                        ),
                                    );
                                }
                            }
                        }
                        }
                    }
                }
                self.name_aufloesen(o, lage);
                // **`N271` (lane 152) -- a suffixed place over an `atomic` names
                // nothing: an atomic is a scalar.**
                //
                // Measured: `let x : u32 = AT[0];` on `atomic AT : u32 relaxed`
                // checks clean (the indexed type falls out as untyped, and every
                // downstream rule steps aside) and emits `uint32_t x = AT[0];`
                // over `_Atomic uint32_t AT` -- an index into a scalar, which
                // `cc` rejects, and a plain access to an atomic either way.
                // The legal indexed atomics (`FP_OWNER[core]` at `publishes`,
                // `awaits`, `exchange`) never reach this arm: all three read
                // their source through `typ_von_ort` directly. What reaches it
                // is the bare expression read, and there the atomic is its bare
                // name (lowered to an explicit load) -- a suffix on it is no
                // form. Like `M138` above it answers `Unbekannt`, so no second
                // rule reports on the same fault.
                if !o.suffixe.is_empty()
                    && !lage.lokal.contains_key(&o.basis.text)
                    && self.u.nennt_atomic(&self.modul, &o.basis.text)
                {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "N271",
                            e.span,
                            format!(
                                "`{}` is an `atomic`, a scalar -- `{}` names no \
                                 element or field",
                                o.basis.text,
                                o.text()
                            ),
                        )
                        .mit_notiz(
                            "reads go through the bare name (an explicit load in \
                             the declared order) or through `awaits`; an indexed \
                             atomic at `publishes`/`awaits`/`exchange` is its own \
                             statement and never stands here",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                // **Die INDIZES sind Ausdruecke, und M1 zaehlte sie nicht.** `t.slots[j].x`
                // mit unbekanntem `j` galt als *ein* Ausdruck mit 100 % Deckung.
                // `index_pruefen` wertet sie fuer die Schranke aus; hier werden sie GEZAEHLT,
                // damit die Quote nicht das Gesehene misst statt der Deckung.
                for ix in crate::ausdruecke_im_ort(o) {
                    let t = self.ausdruck_roh(ix, lage);
                    self.buche(&t);
                }
                self.index_pruefen(o, lage);
                let grund = self.u.typ_von_ort(&self.modul, o, &lage.lokal);
                // **Eine benannte Konstante behaelt ihren WERT** (Rezension 2026-08-20).
                //
                // `return x + 8;` ging durch, `const RESERVE : u32 = 8; return x + RESERVE;`
                // fiel an `M104`: der Ort loeste auf den DEKLARIERTEN Typ auf (`u32`, volle
                // Breite), nicht auf die Zahl. *Der Auswerter stand die ganze Zeit daneben
                // und wird fuer Typschranken schon benutzt.*
                //
                // > Eine Konstante zu benennen ist die Gegenbewegung zur magischen Zahl.
                // > Ein Pruefer, der sie dafuer bestraft, erzieht zur magischen Zahl.
                //
                // Nur ohne Suffixe und nur, wenn der Grundtyp ganzzahlig ist -- ein Feld
                // einer Konstanten ist eine andere Frage.
                if o.suffixe.is_empty() && !lage.lokal.contains_key(&o.basis.text) {
                    if let (Some(b), Some(w)) = (
                        grund.bereich(),
                        self.u.konst_wert_von_namen(&self.modul, &o.basis.text),
                    ) {
                        return Typ::Ganzzahl(IntBereich::genau(b.breite, b.vorzeichen, w, w));
                    }
                }
                self.mit_fakt(o, grund, lage)
            }
            // `old(x)` ist ein Geisterausdruck: er steht in `ensures`, nicht im Rumpf.
            ExprArt::Alt(_) => Typ::Unbekannt,
            ExprArt::Ruf(r) => self.ruf_roh(r, lage),
            // **Lane E2:** a resolved library call answers its declared
            // result, checked like any call; unresolved it stays untyped.
            // The call itself is refused (`N057` unresolved, `N069`
            // resolved) by the name pass.
            ExprArt::LibraryCall(r) => {
                let mut argtypen = Vec::new();
                for a in &r.args {
                    argtypen.push((self.ausdruck(a, lage), a.span));
                }
                if let Some(z) =
                    self.u.bibliothek(&self.modul, &r.library.text, &r.function.text)
                {
                    if let Some(mut sig) = self.u.funktionen.get(&z.name).cloned() {
                        // **Lane E5:** same shortened signature as at the
                        // statement form -- the region fills the last
                        // parameter, so the binding call passes one short.
                        // The bypassed slot draws no second diagnostic here;
                        // the stage refuses it (`N233`) where it stands.
                        if let Some(n) =
                            crate::uebersetzung::fuell_index(&self.u, &self.modul, r)
                        {
                            sig.parameter.truncate(n);
                            argtypen.truncate(n);
                        }
                        let ziel = format!("@{}#{}", r.library.text, r.function.text);
                        return self.ruf_aufgeloest(&ziel, r.span, false, &argtypen, &sig);
                    }
                }
                Typ::Unbekannt
            }
            ExprArt::Eingebaut(_) => Typ::Unbekannt,
            ExprArt::Unaer(UnOp::Nicht, i) => {
                let _ = self.ausdruck(i, lage);
                Typ::Wahrheit
            }
            ExprArt::Unaer(UnOp::Negativ, i) => {
                let t = self.ausdruck(i, lage);
                let Some(b) = t.bereich() else { return Typ::Unbekannt };
                // **`M150` -- the negation leaves the width, and no rule said so.**
                //
                // Every binary operator refuses an out-of-width result at the
                // operation (`M104`); unary minus built the same out-of-width
                // range and stayed silent. Measured over the unchanged checker:
                // `return -x;` with `x : i32` into `i64` passed with 0 errors,
                // because `M101` only compares intervals and never widths -- the
                // computed type then claims a value (`-INT_MIN`) that fits no
                // `i32` and is undefined behaviour in the C it lowers to.
                //
                // The check mirrors `M104`: the mathematical range `-max .. -min`
                // has to fit the operand's own width, at this node and not at
                // the assignment. A `wrapping` operand stays exempt for the same
                // reason it is at `M104` -- its overflow is declared, not found.
                // A narrowed operand stays silent too -- the range is read with
                // its V1/V2 facts (`mit_fakt` ran inside `ausdruck`), not off
                // the declaration.
                let (Some(lo), Some(hi)) = (b.max.checked_neg(), b.min.checked_neg()) else {
                    // Outside `i128` -- and therefore outside every width Gabbro
                    // has. Only a literal at `i128::MIN` reaches here; refusing
                    // is the only direction that does not invent a type.
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M150",
                            e.span,
                            "this negation has no counterpart in any integer width",
                        )
                        .mit_notiz(
                            "SYNTAX.md §4: if the result range does not fit, it is a compile error \
                             and not a wrap-around",
                        ),
                    );
                    return Typ::Unbekannt;
                };
                let r = IntBereich::genau(b.breite, true, lo, hi);
                if !r.passt_in_die_breite() && !t.laeuft_um() {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M150",
                            e.span,
                            format!(
                                "`-` over `{}` leaves the width of the operand type",
                                b.text()
                            ),
                        )
                        .mit_notiz(
                            "SYNTAX.md §4: if the result range does not fit, it is a compile error \
                             and not a wrap-around -- negating the smallest value of a signed \
                             width has no counterpart left in it",
                        )
                        .mit_notiz(
                            "a check before it narrows the range (V1), otherwise `narrow x to … \
                             else { … }`",
                        ),
                    );
                }
                Typ::Ganzzahl(r)
            }
            // **`~x` -- and the operand's WIDTH is the whole rule.**
            //
            // The complement over `n` bits is `MAX - x`, and it is order-reversing and
            // bijective: the range of `~x` is exactly `MAX - x.max .. MAX - x.min`. *No
            // widening, no approximation* -- unlike `+` or `*`, the complement can never
            // leave the width it is taken in, so `M104` has nothing to say about this node
            // and everything to say about the one above it.
            //
            // **Two operands are refused by name rather than guessed at:**
            //
            // * A LITERAL has no width (`IntBereich::konstante` gives it the smallest one it
            //   fits into, marked `literal`). `~5` would then be `250` over `u8` and
            //   `4294967290` over `u32`, and nothing in the source says which. *C answers
            //   this question with the integer promotion, and that answer is the trap this
            //   whole construct stands against.* The named limit is the form for the
            //   all-ones constant: `u32::max`.
            // * A SIGNED operand. `~x` on `i32` is `-x-1` in C -- a perfectly defined
            //   operation and a different one from "invert the bits of a word". Zero corpus
            //   sites ask for it, and Rule A says a construct without a measured need does
            //   not get built.
            ExprArt::Unaer(UnOp::BitNicht, i) => {
                let t = self.ausdruck(i, lage);
                let Some(b) = t.bereich() else { return Typ::Unbekannt };
                if b.literal {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M137",
                            e.span,
                            format!(
                                "`~` over a literal -- `{}` carries no width, and the \
                                 complement is a different number in every one",
                                b.text()
                            ),
                        )
                        .mit_notiz(
                            "the all-ones constant of a width has its own form: `u32::max`",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                if b.vorzeichen {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M137",
                            e.span,
                            format!("`~` over the signed `{}`", b.text()),
                        )
                        .mit_notiz(
                            "`~` inverts the bits of an unsigned word; on a signed one C \
                             computes `-x-1`, and that is a different operation with no \
                             corpus site asking for it",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                let (_, hi) = typen::grenzen(b.breite, false);
                Typ::Ganzzahl(IntBereich::genau(b.breite, false, hi - b.max, hi - b.min))
            }
            ExprArt::Binaer(op, a, b) => self.binaer(*op, a, b, e.span, lage),
            // **Lane 111:** a const-table literal is not typed here.
            // `konstanten.rs` holds it element-wise (`K190`-`K194`), and a
            // second typing here would be the second register over the same
            // fact (W7). `Unbekannt` is compatible with everything, so the
            // `passt` at the `const` stays silent by construction.
            ExprArt::ArrayLit(_) => Typ::Unbekannt,
        }
    }

    /// **`M136` -- the same text, and it means something else in C.**
    ///
    /// `parse.rs::bitexpr` holds `<< >> & ^ |` in ONE flat left-associative level. C grades
    /// them into four: `<< >>` above `&` above `^` above `|`. So `a & b << c` is
    /// `(a & b) << c` here and `a & (b << c)` there -- **the same characters, two programs.**
    ///
    /// Measured on 2026-08-31, compiled and run over all 25 pairs
    /// (`messung/proben/VORRANG-BITSTUFEN.md`): nine of them compute a different value, and
    /// two of the four comparison forms as well. The emitter now writes the parenthesis
    /// (`emit.rs::geklammert`), so **the shipped program computes what the checker proved.**
    ///
    /// > This refusal is not about the program. It is about the READER. A parenthesis in the
    /// > generated file cannot say what the author meant, and the trap belongs to anyone who
    /// > reads both languages.
    ///
    /// **What it does NOT refuse, and why** -- Rule A, no refusal without a measured defect:
    /// where the left operator binds at least as tightly as the right, C groups exactly as
    /// Gabbro does. `a << b & c`, `a & b ^ c`, `a & b & c` are all refused by nobody here.
    /// gcc's `-Wparentheses` is wider and warns on three of those; it is also SILENT on six
    /// of the nine that are wrong. Measured, both directions.
    ///
    /// **And a shift beside a comparison is fine**: C puts `<< >>` above the comparisons,
    /// same as Gabbro. Only `& ^ |` sit on the other side of that line -- Ritchie's
    /// precedence, and the reason this pass does not simply adopt C's table.
    fn vorrangfalle(&mut self, op: BinOp, a: &Expr, b: &Expr) {
        /// C's level for the five operators Gabbro holds in one. Higher binds tighter.
        fn stufe(op: BinOp) -> Option<u8> {
            Some(match op {
                BinOp::SchiebLinks | BinOp::SchiebRechts => 3,
                BinOp::BitUnd => 2,
                BinOp::BitXor => 1,
                BinOp::BitOder => 0,
                _ => return None,
            })
        }
        /// The operator of a child, but only where the author wrote NO parenthesis --
        /// an `ExprArt::Klammer` says the grouping out loud and nothing is ambiguous.
        fn blanker_op(e: &Expr) -> Option<BinOp> {
            match &e.art {
                ExprArt::Binaer(q, _, _) => Some(*q),
                _ => None,
            }
        }

        // **Case one: the flat level against itself.**
        //
        // The tree is always `(a op1 b) op2 c` -- so the node carries `op2` at the root and
        // `op1` as its LEFT child. C regroups exactly when the left one binds LOOSER.
        //
        // The mirrored shape (a bare bit node on the RIGHT) cannot be built: `bitexpr` reads
        // its right operand with `addexpr`, which never yields a bit operator. A parenthesis
        // is the only way to get one there, and then it is an `ExprArt::Klammer`. *No branch
        // is written for a shape the grammar cannot produce* -- it would be code no probe
        // could reach.
        if let (Some(p), Some(q)) = (stufe(op), blanker_op(a).and_then(stufe)) {
            if q < p {
                let (l, r) = (op_zeichen(blanker_op(a).unwrap_or(op)), op_zeichen(op));
                self.absagen.schiebe(
                    Absage::fehler(
                        "M136",
                        a.span,
                        format!(
                            "`x {l} y {r} z` groups as `(x {l} y) {r} z` here and as \
                             `x {l} (y {r} z)` in C -- write the parenthesis you mean"
                        ),
                    )
                    .mit_notiz(
                        "SYNTAX.md: Gabbro holds `<< >> & ^ |` in ONE level, C grades them \
                         into four -- the same characters are two programs",
                    )
                    .mit_notiz(
                        "the generated C carries the parenthesis and computes THIS reading; \
                         the refusal is about the reader, not the program",
                    ),
                );
            }
        }

        // **Case two: the bit level against the comparisons.**
        //
        // `cmpexpr = bitexpr [ cmp bitexpr ]` puts the whole bit level BELOW the comparison;
        // C puts `& ^ |` above it. Both operands are read as `bitexpr`, so unlike case one
        // this shape is reachable on either side.
        if op.ist_vergleich() {
            for seite in [a, b] {
                let Some(q) = blanker_op(seite) else { continue };
                if !matches!(q, BinOp::BitUnd | BinOp::BitXor | BinOp::BitOder) {
                    continue;
                }
                let (l, r) = (op_zeichen(q), op_zeichen(op));
                self.absagen.schiebe(
                    Absage::fehler(
                        "M136",
                        seite.span,
                        format!(
                            "`x {l} y {r} z` groups as `(x {l} y) {r} z` here and as \
                             `x {l} (y {r} z)` in C -- write the parenthesis you mean"
                        ),
                    )
                    .mit_notiz(
                        "SYNTAX.md: `& ^ |` bind TIGHTER than a comparison here and looser \
                         in C -- a shift does not, in either language",
                    )
                    .mit_notiz(
                        "the generated C carries the parenthesis and computes THIS reading; \
                         the refusal is about the reader, not the program",
                    ),
                );
            }
        }
    }

    fn binaer(&mut self, op: BinOp, a: &Expr, b: &Expr, span: Span, lage: &Lage) -> Typ {
        self.vorrangfalle(op, a, b);
        let ta = self.ausdruck(a, lage);
        let tb = self.ausdruck(b, lage);
        if op == BinOp::Und || op == BinOp::Oder {
            return Typ::Wahrheit;
        }
        // **`M124` -- ein Grund wird nur gegen einen Grund DERSELBEN Deklaration
        // verglichen** (Stufe 7, 2026-08-21).
        //
        // Hier steht nur die Haelfte, die die TYPEN sieht; dass ein Grund ueberhaupt an
        // dieser Stelle stehen darf, entscheidet `grundstellung` weiter unten. *Die
        // Trennung ist noetig, weil die Arithmetik hier auf `Unbekannt` zurueckfiele und
        // `Unbekannt` schweigt* -- ein Riegel ist keine Absage, derselbe Satz, den `M117`
        // ueber `IntBereich::ist_leer()` stehen hat.
        let grund_seite = |t: &Typ| matches!(t, Typ::Grund(_));
        if grund_seite(&ta) || grund_seite(&tb) {
            if !op.ist_vergleich() {
                // Die Stellung ist verboten; `grundstellung` sagt es mit der Begruendung,
                // die zu ihr gehoert. Hier nur der Typ, und der ist keiner.
                return Typ::Unbekannt;
            }
            if matches!((&ta, &tb), (Typ::Grund(x), Typ::Grund(y)) if x == y) {
                return Typ::Wahrheit;
            }
            self.absagen.schiebe(
                Absage::fehler(
                    "M124",
                    span,
                    format!(
                        "`{}` and `{}` are not comparable",
                        ta.text(),
                        tb.text()
                    ),
                )
                .mit_notiz(
                    "a reason compares against a reason of the SAME declaration and \
                     against nothing else -- two declarations may hand out the same \
                     number for different things",
                ),
            );
            return Typ::Wahrheit;
        }
        // **«F»: Gleitkommaarithmetik antwortet heute mit dem VOLLEN Bereich.**
        //
        // Keine Fortpflanzung heisst nicht „keine Aussage", sondern die weiteste -- sonst
        // waere das Schweigen eine Zusage. `[0,1] + [0,1]` liegt in `[0,2]`, und ohne
        // Rechnung ist die einzige ehrliche Antwort: alles, NaN eingeschlossen.
        //
        // *Die Fortpflanzung muss NACH AUSSEN runden, wenn sie kommt* (`PLAN.md`, F3):
        // `[a,b] + [c,d]` ist `[RD(a+c), RU(b+d)]`. Mit Wirtsdoubles in RNE gerechnet waeren
        // die Schranken um bis zu ein Ulp zu ENG -- unsound in der Richtung, die nichts
        // meldet.
        if !op.ist_vergleich() {
            match (ta.durchgreifen().clone(), tb.durchgreifen().clone()) {
                (Typ::Gleitkomma(x), Typ::Gleitkomma(y)) => {
                    return match op {
                        BinOp::Plus => Typ::Gleitkomma(x.plus(y)),
                        BinOp::Minus => Typ::Gleitkomma(x.minus(y)),
                        BinOp::Mal => Typ::Gleitkomma(x.mal(y)),
                        BinOp::Geteilt => Typ::Gleitkomma(x.geteilt(y)),
                        // **`F005`: eine Verknuepfung, die es fuer Gleitkomma nicht gibt.**
                        // Sie stillschweigend mit dem vollen Bereich zu beantworten waere
                        // eine Erlaubnis -- dieselbe Bauart wie `opaque` vor `D003`.
                        _ => {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "F005",
                                    span,
                                    "this operation does not exist for floating point",
                                )
                                .mit_notiz(
                                    "bitwise operations, shifts and remainder are \
                                        statements about a BIT PATTERN, and a floating-point \
                                        number is not one",
                                ),
                            );
                            Typ::Unbekannt
                        }
                    };
                }
                // **Breitenmischung mit einer Ganzzahl gibt es nicht ohne Umwandlung** -- und
                // eine Umwandlungsform steht noch nicht da.
                (Typ::Gleitkomma(x), _) | (_, Typ::Gleitkomma(x)) => {
                    let _ = x;
                    self.absagen.schiebe(
                        Absage::fehler(
                            "F005",
                            span,
                            "floating point and integer in one operation",
                        )
                        .mit_notiz(
                            "there is no conversion form; a silent one would be exactly \
                                the hidden rounding this language refuses",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                _ => {}
            }
        }
        if op.ist_vergleich() {
            return Typ::Wahrheit;
        }
        // **`D003` -- ein undurchsichtiger Typ hat KEINE Rechnung seines Traegers.**
        //
        // Gemessen am 2026-08-18, und der Fund ist groesser als sein Anlass:
        //
        // ```gabbro
        // opaque type F32 = u32;
        // impl fn unsinn(a : F32, b : F32) -> F32 { return a & b; }
        // -> 3 Items, 0 Fehler, 0 Hinweise
        // ```
        //
        // Bitweises Und behaelt die Breite, also schwieg die Ueberlaufregel -- und der
        // undurchsichtige Typ wurde als sein TRAEGER gerechnet. **Dass `a + b` fiel, war
        // Zufall:** es fiel an `M104`, nicht an der Undurchsichtigkeit. *Wo die Breiten
        // aufgehen, ging der Unsinn durch.*
        //
        // > **Und es trifft nicht nur `F32`, sondern jeden Zeugen- und Neutyp der Sprache**:
        // > `Pa` gegen `Va`, zwei `index into` verschiedener Instanzen, einen Rang mit einer
        // > Zellenzahl. Dieselbe Klasse wie `protects`, das deklariert war und nie geprueft
        // > wurde.
        //
        // **VERGLEICHE bleiben zulaessig** (der `return` oben steht davor, mit Absicht): zwei
        // Adressen zu vergleichen deutet den Traeger nicht um, es ordnet Werte desselben
        // Typs. *Was verboten ist, ist das RECHNEN* -- eine Summe zweier Adressen ist keine
        // Adresse, und ein bitweises Und zweier Gleitkommazahlen ist gar nichts.
        for (t, e) in [(&ta, a), (&tb, b)] {
            if let Typ::Benannt { name, undurchsichtig: true, .. } = t {
                self.absagen.schiebe(
                    Absage::fehler(
                        "D003",
                        e.span,
                        format!("`{name}` is opaque -- it does not have the arithmetic of its carrier"),
                    )
                    .mit_notiz(
                        "an `opaque type` says: this type IS not its carrier. Whoever \
                            wants to compute needs a conversion, and there is none",
                    )
                    .mit_notiz(
                        "comparisons stay allowed: they order values of the same type and \
                            produce no new one",
                    ),
                );
                return Typ::Unbekannt;
            }
        }
        let (Some(ba), Some(bb)) = (ta.bereich(), tb.bereich()) else {
            return Typ::Unbekannt;
        };

        // V2: unter `a >= b` faengt `a - b` bei 0 an, unter `a > b` bei 1.
        // The narrowed range still has to fit the width it is computed in --
        // asking that question HERE, at the operation, and not at the
        // assignment (`M101`), is the `M150` lesson one door down: under
        // `a >= b` with two open `i32` the range below is `0 .. 4294967295`,
        // and into an `i64` result even `M101` stays silent (measured
        // 2026-09-11, 0 errors over the unchanged checker), while the C this
        // lowers to overflows on `INT_MAX - INT_MIN`. A `wrapping` left side
        // stays exempt, as at the tail below -- its overflow is declared, and
        // the emitter computes it unsigned.
        if op == BinOp::Minus {
            if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
                if let Some(untergrenze) = self.beziehung(oa, ob, lage) {
                    let eng = IntBereich::genau(
                        ba.breite,
                        ba.vorzeichen,
                        untergrenze,
                        (ba.max - bb.min).max(untergrenze),
                    );
                    if !eng.passt_in_die_breite() && !ta.laeuft_um() {
                        self.ueberlauf_ausdruck(span, &ba, &bb, op_zeichen(op));
                    }
                    return Typ::Ganzzahl(eng);
                }
            }
        }

        // **PLAN-BITS section 4 (lane 88): the overflow operators never take
        // the width-overflow path below.** Wrapping is defined modulo 2^N on an
        // exact unsigned range and saturating clamps into the shared operand
        // range by construction -- there is no `M104` for either of them, only
        // the exactness refusals `M153`/`M154` inside.
        if matches!(
            op,
            BinOp::PlusWrap
                | BinOp::MinusWrap
                | BinOp::MalWrap
                | BinOp::SchiebLinksWrap
                | BinOp::PlusSat
        ) {
            return self.wrapping_or_saturating(op, &ba, &bb, span);
        }

        let r = match op {
            BinOp::Plus => typen::addiere(&ba, &bb),
            BinOp::Minus => typen::subtrahiere(&ba, &bb),
            BinOp::Mal => typen::multipliziere(&ba, &bb),
            BinOp::Geteilt | BinOp::Rest => {
                if bb.enthaelt_null() {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M102",
                            b.span,
                            format!(
                                "the denominator has range `{}` and does not exclude zero",
                                bb.text()
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §3: division and remainder require a denominator \
                                whose range excludes zero",
                        )
                        .mit_notiz(
                            "a check `if n >= 1 { … }` narrows it (V1), otherwise `narrow \
                                n to 1 .. … else { … }`",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                if op == BinOp::Geteilt {
                    typen::teile(&ba, &bb)
                } else {
                    let r = typen::rest(&ba, &bb);
                    // **`M152` -- the remainder at `INT_MIN % -1` traps, and no rule said so.**
                    //
                    // Division got this right long ago: `INT_MIN / -1` leaves the
                    // width through `teile` and falls at `M104`. The remainder
                    // over the same inputs claims a range that FITS (`|a % b| <=
                    // |b| - 1`), so `M104` has nothing to say -- yet the C the
                    // emitter writes (`a % b`, signed) traps exactly where the
                    // division does: `INT_MIN % -1` raises SIGFPE on x86-64
                    // (measured 2026-09-11, exit 136), because C defines `%`
                    // through `/` (C11 6.5.5). Measured over the unchanged
                    // checker: `x % y` with `x : i32` open and `y : i32 in
                    // -1 .. -1` passed with 0 errors, and the emitter wrote
                    // `return x % y;` straight into the C.
                    //
                    // The check mirrors `M150`: it fires at the operation, with
                    // the `SPRACHE.md §3` note (compile error, not a trap) and
                    // the V1 remedy note. The ranges are read WITH their V1/V2
                    // facts, so a divisor narrowed away from `-1` and a
                    // dividend narrowed away from the smallest value stay
                    // silent. Unsigned operands stay silent too: `%` over
                    // unsigned C is defined for every nonzero divisor.
                    //
                    // No `wrapping` exemption, unlike `M104`/`M150`: the
                    // unsigned lowering that exempts them covers only
                    // `+ - * <<` (`emit.rs::rechnet`), so a `wrapping`
                    // remainder still lowers to signed C `%` and still traps.
                    if r.bereich.is_some() && ba.vorzeichen && bb.vorzeichen {
                        let (kleinste, _) = typen::grenzen(ba.breite, true);
                        if ba.min == kleinste && bb.min <= -1 && -1 <= bb.max {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M152",
                                    span,
                                    format!(
                                        "`{} % {}` traps at the smallest value over `-1`",
                                        ba.text(),
                                        bb.text()
                                    ),
                                )
                                .mit_notiz(
                                    "SPRACHE.md §3: if the result range does not fit, it is a compile error \
                                     and not a wrap-around -- `INT_MIN % -1` traps in the C this lowers to, \
                                     because C defines `%` through `/`",
                                )
                                .mit_notiz(
                                    "a check before it narrows the range (V1), otherwise `narrow … to … \
                                     else { … }` -- away from `-1` on the divisor or away from the \
                                     smallest value on the dividend",
                                ),
                            );
                        }
                    }
                    r
                }
            }
            BinOp::BitUnd => typen::bitweise(&ba, &bb, typen::BitOpArt::Und),
            BinOp::BitOder => typen::bitweise(&ba, &bb, typen::BitOpArt::Oder),
            BinOp::BitXor => typen::bitweise(&ba, &bb, typen::BitOpArt::Xor),
            BinOp::SchiebLinks => typen::schiebe_links(&ba, &bb),
            BinOp::SchiebRechts => typen::schiebe_rechts(&ba, &bb),
            _ => return Typ::Unbekannt,
        };
        if r.laeuft_ueber && !ta.laeuft_um() {
            self.ueberlauf_ausdruck(span, &ba, &bb, op_zeichen(op));
        }
        match r.bereich {
            Some(x) => Typ::Ganzzahl(x),
            None => Typ::Unbekannt,
        }
    }

    fn ruf(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        let t = self.ruf_roh(r, lage);
        self.buche(&t);
        t
    }

    fn ruf_roh(&mut self, r: &Ruf, lage: &Lage) -> Typ {
        // **Bit intrinsics (PLAN-BITS §3): seven single-segment call names the
        // language claims.** Like the integer conversions below they are typed
        // here rather than looked up as functions: there is no declaration, and
        // a lookup would answer `Unbekannt` -- the compatible-with-everything
        // exit that hid «B8». A labelled call (`clz(x: v)`) is NOT one: it falls
        // through to `marken_pruefen`, which refuses labels at non-constructors
        // (`M107`), the same sentence a labelled conversion gets.
        if !r.ist_verbundwert() {
            if let Some(einfach) = r.path().and_then(|p| p.einfach()) {
                if crate::ist_bitintrinsik(&einfach.text) {
                    return self.intrinsik_ruf(&einfach.text, r, lage);
                }
            }
        }
        // **G9, repaired 2026-09-04 -- a call whose path names an integer type IS the
        // conversion.** `SYNTAX.md`:588 marks `primary` with `G9` -- no `cast` production -- and :656-659
        // gives the reason in full: *"a call whose path names a type IS the conversion --
        // the distinction is a name resolution, not a syntax question."* Until today the
        // reader refused the token before this pass ever ran (`P002`, `parse.rs`); the parser
        // repair lets `u64(a)` reach here as an ordinary `Ruf` over the one-segment path
        // `u64`, and this is where it is typed rather than looked up as a function.
        //
        // Found by «K3» (`messung/K3-BEFUND.md` §4.1): `test_func`'s two most ordinary lines
        // -- `(u64) ktime_us_delta(...)`, `(u64) test_repeat_count` -- have no Gabbro form,
        // and `grep` over the whole corpus at the time found zero sites that would have
        // exercised the gap.
        if let Some(pfad) = r.path() {
            if let Some(ziel) = pfad
                .einfach()
                .and_then(|i| gabbro_syntax::kw::Kw::suche(&i.text))
                .filter(|k| k.ist_intty())
            {
                return self.umwandlung_ruf(r, ziel, lage);
            }
            // PLAN-BITS §1: `u13(a)` converts to the sugar's storage word. The
            // path names the sugar spelling; `umwandlung` answers the storage
            // word's full range, the same conservative answer a narrowing
            // conversion to the longhand gives. The sugar spelling never
            // reaches the graph or the cost pass as a callee: both read the
            // rewritten name (see `aufrufgraph::zucker_umschreiben` and the
            // `kosten.rs` conversion arm), so neither mistakes it for a call.
            if let Some(einfach) = pfad.einfach() {
                if let Some(speicher) = gabbro_syntax::zucker_speicher(&einfach.text) {
                    return self.umwandlung_ruf(r, speicher, lage);
                }
            }
        }
        // **An indirect call is typed from the CONTRACT at the place's type** («B8»,
        // 2026-08-21) -- the result type and the parameter types both.
        //
        // This is what closes the measured hole: `probe/p8.gab` assigned `t->bereit` to a
        // `u32`, a `bool` and a pointer in one file with **0 errors**, because `fn(…)` became
        // `Typ::Unbekannt` and `Unbekannt` is compatible with everything. *An untyped
        // expression is not a neutral one.*
        //
        // A place whose type is NOT a function pointer gets `M129`. **Not silence and not
        // `Unbekannt`:** `Unbekannt` is precisely what made the old hole invisible, and the
        // run only counted it (`M1 saw 4 expressions, 3 of them without a type`).
        if let Some(o) = r.place() {
            let mut argtypen = Vec::new();
            for a in &r.argumente {
                argtypen.push((self.ausdruck(a, lage), a.span));
            }
            let Typ::FnPtr(v) = self.u.typ_von_ort(&self.modul, o, &lage.lokal) else {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M129",
                        r.span,
                        format!("`{}` is not a function pointer, so it cannot be called", o.text()),
                    )
                    .mit_notiz(
                        "a call through a place needs a `fn(…)` type at that place -- that \
                         type is where the callee's contract stands",
                    ),
                );
                return Typ::Unbekannt;
            };
            for (i, ((t, span), (pname, pt))) in
                argtypen.iter().zip(v.parameters.iter()).enumerate()
            {
                // **A pointer type need not name its parameters** (`fn(u8)`), and then the
                // message says the POSITION. *Naming a slot the author left unnamed would
                // put a word in their mouth.*
                let was = match pname {
                    Some(n) => format!("argument `{n}`"),
                    None => format!("argument no. {}", i + 1),
                };
                self.passt(t, pt, *span, &was);
            }
            // **`N296` -- the arity of an INDIRECT call (lane 177).** The loop above is a
            // truncating `zip`: a missing argument is a parameter nobody compares and a
            // surplus one a value nobody reads -- the same shape `M143` closed for direct
            // calls on 2026-09-03, one file per direction. **It reports and does not
            // return**, like `M143`: the overlap still gets its per-position comparison.
            if argtypen.len() != v.parameters.len() {
                let (n, m) = (v.parameters.len(), argtypen.len());
                self.absagen.schiebe(
                    Absage::fehler(
                        "N296",
                        r.span,
                        format!(
                            "`{}` declares {n} parameter(s), this call passes {m}",
                            o.text()
                        ),
                    )
                    .mit_notiz(
                        "nothing converts at an indirect call: the caller pushes what the \
                         SLOT's type says, so a missing argument is a parameter nobody \
                         checks and a surplus one a value nobody reads",
                    )
                    .mit_notiz(
                        "the comparison above runs on the OVERLAP and stops at the shorter \
                         list, so without this line the count is held by neither side",
                    ),
                );
            }
            // **Lane 177: the TYPE's contract is checked like a callee's.** The slot's
            // parameter names stand where a declaration's would (`None` becomes the
            // empty name, which no clause can address -- the same reticence as at a
            // direct call). `N295` is the weak `M115` reading at an indirect site: it
            // refuses where the argument's RANGE excludes the condition, and the
            // `V`-less silence otherwise is the user's, counted nowhere here.
            let slot = crate::umgebung::Signatur {
                parameter: v
                    .parameters
                    .iter()
                    .map(|(n, t)| (n.clone().unwrap_or_default(), t.clone()))
                    .collect(),
                ergebnis: v.result.clone().map(|b| *b),
                ensures: v.ensures.clone(),
                requires: v.requires.clone(),
                rumpf_da: true,
                effect_list: v.effects.clone(),
                cost_bound: v.costs,
                span: r.span,
            };
            self.requires_pruefen(&o.text(), "N295", &slot, &argtypen);
            // **The result is known to satisfy `ensures` afterwards -- as for a direct
            // call.** The narrowing is the same function (`bereich_aus_ensures`); what
            // differs is whose promise it is: the slot's, which every producer refines
            // (the `C` obligation). It is NOT booked as a foreign narrowing: the
            // candidates behind the pointer include bodies Gabbro sees, and the
            // refinement is counted, not assumed.
            let roh = v.result.clone().map(|x| *x).unwrap_or(Typ::Unbekannt);
            let eng = crate::fremdverengung::bereich_aus_ensures(&roh, &v.ensures);
            // **A call with no result stays untyped -- exactly as a direct one does.**
            // The line below is `sig.ergebnis.clone().unwrap_or(Typ::Unbekannt)` with the
            // contract in place of the signature, and it is deliberately the same: Gabbro has
            // no unit type, and inventing one here would make the indirect call differ from
            // the direct call in a way no rule asked for. *The coverage number counts it, in
            // both paths, and that is a property of `void`, not of this construct.*
            return eng.typ;
        }
        // **Aufgeloest wird im Modul des Aufrufs**, nicht ueber den blanken Namen.
        let signatur = r.path().and_then(|p| self.u.funktion(&self.modul, p)).cloned();
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
        }
        // **Lane 167: `Variant(payload)` -- a `tagged` case construction, not a call.**
        //
        // The shape parses as a `Ruf` because the parser knows no declarations; the
        // resolution stands here, before `marken_pruefen` (labels belong to record
        // constructors, `M107`, never to a case) and before the function lookup
        // below. What it answers is the model's `Expr.fall cs i nutz`: the case
        // index `i` is the declaration order, `cs` the whole case list carried by
        // the answered sum type, and the payload is held against the case's type
        // with the ordinary range rule (`M101`) -- a payload out of range is a
        // range refusal, not a constructor refusal. A function of the same name
        // wins: the decision lives in `Umgebung::variante`/`ist_variantenkonstruktor`,
        // the one predicate every pass asks, so no pass reads a constructor where
        // another reads a call.
        if let Some(pfad) = r.path() {
            if pfad.teile.len() == 1 {
                let name = pfad.teile[0].text.clone();
                let ist_builtin = name == "Some" || name == "None" || name == "old" || name == "result"
                    || gabbro_syntax::kw::Kw::suche(&name).is_some_and(|k| k.ist_intty())
                    || gabbro_syntax::zucker_speicher(&name).is_some()
                    || crate::ist_bitintrinsik(&name);
                if !ist_builtin
                    && self.u.funktion(&self.modul, pfad).is_none()
                    && !self.u.ist_uebergang(&self.modul, pfad)
                    && !self.u.nennt_kopf(&self.modul, &name)
                {
                    // **A KNOWN case is a constructor attempt, labelled or not.**
                    // Labels never stand at a case (`N284` owns them, inside
                    // `variantenkonstruktor`), so the known case is resolved
                    // before the `ist_verbundwert` gate below could hand it to
                    // `marken_pruefen` as a record. An unknown or ambiguous name
                    // WITH labels stays `M107`'s: a label claims a record, and
                    // only a known case rebuts that reading.
                    if let crate::umgebung::VariantenFund::Eine(t) =
                        self.u.variante(&self.modul, &name)
                    {
                        if !self.u.funktionsname_belegt(&name) {
                            return self.variantenkonstruktor(r, &name, &t, &argtypen);
                        }
                    }
                    if !r.ist_verbundwert() {
                    // **A function of this name stands elsewhere in the unit.**
                    // The visible resolution is not the function (checked above),
                    // but the emitter reads callees unit-wide, so it would lower
                    // the call while this arm typed a construction. Refused instead
                    // of miscompiled; there is no qualified case syntax that could
                    // name the case past the function.
                    if self.u.funktionsname_belegt(&name) {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "N280",
                                r.span,
                                format!(
                                    "`{name}` shares its name with a declared function -- \
                                     a construction names its case, and a call of this \
                                     name lowers as the function"
                                ),
                            )
                            .mit_notiz(
                                "the emitter reads callees by their bare name across the \
                                 whole unit; which of the two readings the C carries cannot \
                                 be told apart there",
                            ),
                        );
                    } else {
                    match self.u.variante(&self.modul, &name) {
                        crate::umgebung::VariantenFund::Eine(t) => {
                            return self.variantenkonstruktor(r, &name, &t, &argtypen);
                        }
                        crate::umgebung::VariantenFund::Mehrere(summen) => {
                            let liste = summen
                                .iter()
                                .map(|s| format!("`{}`", crate::umgebung::kurzname(s)))
                                .collect::<Vec<_>>()
                                .join(", ");
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "N280",
                                    r.span,
                                    format!(
                                        "`{name}` names a case of several `tagged` types ({liste}) -- \
                                         and a construction names its case, not its type"
                                    ),
                                )
                                .mit_notiz(
                                    "the case index the model carries (`Expr.fall cs i nutz`) \
                                     is read off ONE case list; with two lists there is no index",
                                ),
                            );
                            return Typ::Unbekannt;
                        }
                        crate::umgebung::VariantenFund::Keine => {
                            if self.u.hat_markierte() {
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "N280",
                                        r.span,
                                        format!(
                                            "`{name}` names no function and no case of the `tagged` \
                                             types declared here"
                                        ),
                                    )
                                    .mit_notiz(
                                        "a `tagged` case constructs as `Case(payload)` for a case \
                                         with payload and as `Case` or `Case()` without one -- \
                                         this spelling is neither a call nor a construction",
                                    ),
                                );
                            }
                        }
                    }
                    }
                    }
                }
            }
        }
        self.marken_pruefen(r);
        // **`Some(i)` TRAEGT den Typ seines Arguments -- und ohne diese Zeile hatte der
        // Sonderwert keinen Waechter.**
        //
        // Gemessen 2026-08-19: `frei = Some(8)` auf einer `table … count 8` ging mit **null
        // Fehlern** durch. Der Wert `8` ist aber genau der Sonderwert, zu dem `None`
        // absenkt (`beweise/Option_Sonderwert.thy`, `sonderwert_ausserhalb`) -- *damit waere
        // `None` von einem gueltigen Index nicht mehr zu unterscheiden, und
        // `kodiere_injektiv` haette keine Praemisse mehr.*
        //
        // > **Der Beweis lag seit dem 2026-08-17 da; geprueft hat seine Bedingung niemand.**
        // > Das ist genau die Haelfte, die «NL» beklagt -- ein Satz ohne Leser.
        //
        // `Some` und `None` sind reservierte Woerter (`kw.rs`), also kann diese Zeile keine
        // benutzerdeklarierte Funktion treffen. `None` bleibt ohne Typ: es IST der
        // Sonderwert und liegt bauartbedingt ausserhalb.
        if r.heisst("Some") {
            return argtypen.first().map(|(t, _)| t.clone()).unwrap_or(Typ::Unbekannt);
        }
        let Some(sig) = signatur else {
            return Typ::Unbekannt;
        };
        // **`M143` -- the arity of a DIRECT call, which every pass believed another one held.**
        //
        // The line that stood here assigned the arity to the NAME PASS and left this one
        // only the range. (It said so in German; the original is in the commit that removes
        // it, where the history belongs.) **The name pass does not hold it.** Measured
        // 2026-09-03 against the unchanged checker, one file per direction:
        //
        // ```gabbro
        // extern fn zwei(a : u32, b : u32) -> u32 effects { pure } costs <= 1 ops;
        // impl fn ruf(x : u32) -> u32 … { return zwei(x); }        /* ONE argument */
        // ```
        //
        //     gabbro pruefe  ->  3 items, 0 errors, 0 hints      (and the same for zwei too MANY)
        //     gabbro emit    ->  exit 0, and the unit carries
        //                        uint32_t zwei(uint32_t a, uint32_t b);
        //                        return zwei(x);
        //     cc             ->  error: too few arguments to function 'zwei'
        //
        // This is the `zip` below saying it: `argtypen.iter().zip(sig.parameter.iter())`
        // stops at the SHORTER list, so a missing argument is a parameter nobody compares
        // and a surplus one is a value nobody reads. *A truncating zip is a silent `else`
        // with a different spelling* -- the same shape as `M139`'s, one line further up.
        //
        // > **Arity was already held in three places, and a direct call was none of them:**
        // > `M128` at a function POINTER, `M132` at `refines`, `M106` at a record
        // > constructor. The commonest call in the language had the check that the three
        // > rarer ones carry.
        //
        // **It reports and does not return.** The overlap still gets its per-position
        // comparison: where a call passes two of three arguments, the two it does pass can
        // still be the wrong shape, and refusing to say so would trade one silence for
        // another. *`cc` catches this one -- and that is exactly the sentence `M140`'s own
        // note refuses to accept as an answer.*
        // **A `transition` is exempt, and it is the one exemption.** Its `Signatur` is
        // entered with `parameter: Vec::new()` because the grammar gives a transition no
        // parameter list at all, while `wurzel_setzen(v)` passes the carrier -- so the empty
        // list is a PLACEHOLDER and comparing against it reads `declares 0`. It did, over
        // `beispiele/02-geraet.gab`:64 and :71, at the first corpus run of this rule.
        // *What the arity of a transition call ought to be is a question this rule does not
        // answer* -- see the register's reservation.
        let uebergang = r.path().is_some_and(|p| self.u.ist_uebergang(&self.modul, p));
        let ziel = r.target_text();
        self.ruf_aufgeloest(&ziel, r.span, uebergang, &argtypen, &sig)
    }

    /// **Lane E2: a resolved call, whoever spelled it.**
    ///
    /// The tail of `ruf_roh`'s direct path -- arity (`M143`), per-argument
    /// shape and range (`passt`), `requires` (`M115`), and the
    /// `ensures`-narrowing with its foreign booking -- over an already
    /// resolved signature. A library call (`@lib#f`) resolves through
    /// `Umgebung::bibliothek` instead of `Umgebung::funktion` and lands
    /// here with the same signature; what it reports and what it answers
    /// are the same by construction, not by parallel code. `uebergang` is
    /// always false across a library edge: the resolved name stands for a
    /// `library fn`, never for a transition placeholder.
    fn ruf_aufgeloest(
        &mut self,
        ziel: &str,
        span: Span,
        uebergang: bool,
        argtypen: &[(Typ, Span)],
        sig: &crate::umgebung::Signatur,
    ) -> Typ {
        if !uebergang && argtypen.len() != sig.parameter.len() {
            let (n, m) = (sig.parameter.len(), argtypen.len());
            self.absagen.schiebe(
                Absage::fehler(
                    "M143",
                    span,
                    format!("`{ziel}` declares {n} parameter(s), this call passes {m}"),
                )
                .mit_notiz(
                    "a parameter with no argument is a slot every pass behind this one still \
                     computes with -- the effect hull reads what the caller may touch through \
                     it and the range facts after the call are the callee's, and neither is a \
                     statement about anything the caller wrote",
                )
                .mit_notiz(
                    "the comparison below runs on the OVERLAP and stops at the shorter list, \
                     so without this line a missing argument is a parameter nobody checks",
                ),
            );
        }
        // Only the range falls here; the shape is `M139`/`M140`'s and the count is `M143`'s.
        for ((t, span), (pname, pt)) in argtypen.iter().zip(sig.parameter.iter()) {
            self.passt(t, pt, *span, &format!("argument `{pname}`"));
        }
        self.requires_pruefen(ziel, "M115", &sig, &argtypen);
        let roh = sig.ergebnis.clone().unwrap_or(Typ::Unbekannt);
        let v = crate::fremdverengung::bereich_aus_ensures(&roh, &sig.ensures);
        // **Und hier wird die Annahme GEBUCHT statt still zu wirken (2026-08-21).**
        //
        // Bis heute stand an dieser Stelle nur der Ruf; `sig.rumpf_da` wurde nicht gefragt,
        // obwohl das Feld in seinem eigenen Kopfkommentar sagt, wozu es da ist: *„Ohne ihn
        // ist jede Verengung aus `ensures` eine ANNAHME ueber fremden Code und gehoert ins
        // Zeugnis."* **Die Verengung bleibt** -- ein Vertrag an einem fremden Rumpf SOLL
        // wirken, das ist sein Zweck. Was sich aendert, ist ihre Sichtbarkeit.
        //
        // > Gebucht wird die WIRKSAME Verengung: `schritte` ist leer, wenn keine Grenze sich
        // > bewegt hat. *Eine Klausel, die nichts verengt, ist eine Zeile, die niemanden
        // > bindet* -- und genau diese Unterscheidung ist der Gegenstand des Postens.
        if !sig.rumpf_da {
            for s in &v.schritte {
                self.fremd.push(Stelle {
                    rufer: self.rufer.clone(),
                    gerufener: ziel.to_string(),
                    span,
                    klausel: s.klausel.clone(),
                    wirkung: Wirkung::Bereich {
                        vorher: s.vorher.clone(),
                        nachher: s.nachher.clone(),
                    },
                });
            }
        }
        v.typ
    }

    /// **`u64(a)` and its seven siblings -- an integer conversion, typed.**
    ///
    /// **What a conversion does to a proved range, decided before this was wired in:** the
    /// conversion may narrow OR widen the representation, and a narrowing conversion can
    /// throw bits away the source range says nothing about losing -- carrying the source
    /// range through UNCONDITIONALLY would be a GUESS dressed as a proof, the same shape
    /// `M1` already refuses for float arithmetic that mixes widths (`F005`, above) and for
    /// an `opaque` carrier's hidden representation (`D003`). Where the source range does NOT
    /// provably fit the target, the answer is the FULL declared range of the target type --
    /// the tail of this function draws the line and says why the other branch (source fits,
    /// so keep it exactly) is not the same guess. A later `requires`/`ensures` on the
    /// surrounding call may narrow either answer further, exactly as an ordinary function
    /// result does; nothing here forecloses that.
    ///
    /// `marken_pruefen` still runs: a labelled conversion (`u64(a: 1)`) is not a struct and
    /// `M107` already says so correctly, without a second rule that repeats it.
    fn umwandlung_ruf(&mut self, r: &Ruf, ziel: gabbro_syntax::kw::Kw, lage: &Lage) -> Typ {
        self.marken_pruefen(r);
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
        }
        // **`M144` -- a conversion takes exactly one value.** Framed like `M143`'s arity
        // message on purpose: both answer "how many did the declaration want, how many did
        // the call pass", and a conversion's "declaration" is the built-in unary form
        // `SYNTAX.md` describes.
        if argtypen.len() != 1 {
            self.absagen.schiebe(
                Absage::fehler(
                    "M144",
                    r.span,
                    format!(
                        "`{}` converts one value, this call passes {} -- a conversion is a promise \
                         about ONE value's range on every path, and there is no rule for \
                         what the others would mean",
                        ziel.text(),
                        argtypen.len()
                    ),
                )
                .mit_notiz(
                    "a call whose path names a type IS the conversion (`SYNTAX.md` G9) -- \
                     the same shape as `(u64) x` in C, and C's cast is unary too",
                ),
            );
            return Typ::Unbekannt;
        }
        let (quelltyp, span) = &argtypen[0];
        // **`M145` -- the argument must itself be an integer.** A conversion between integer
        // widths is the one form «K3» needed and the one this repair builds; a pointer, a
        // float or a `bool` argument is a DIFFERENT conversion that C's `(T)` spells the same
        // way and this language does not build here, so the refusal names the gap instead of
        // guessing a lowering for it.
        if !matches!(quelltyp.durchgreifen(), Typ::Ganzzahl(_) | Typ::Unbekannt) {
            self.absagen.schiebe(
                Absage::fehler(
                    "M145",
                    *span,
                    format!(
                        "`{}(...)` converts an integer, and the argument has type `{}` -- the \
                         promise a conversion carries is over an integer RANGE, and the \
                         caller relies on it holding on every path",
                        ziel.text(),
                        quelltyp.text()
                    ),
                )
                .mit_notiz(
                    "only integer-to-integer conversion is built -- a pointer, a float or a \
                     `bool` argument needs a form this language does not have yet",
                ),
            );
            return Typ::Unbekannt;
        }
        let (breite, vorzeichen) = crate::umgebung::breite_von(ziel)
            .expect("ziel came from Kw::ist_intty(), and breite_von covers exactly that set");
        // **A conversion that cannot lose information keeps the PROVED range instead of
        // widening it to the full type.** «K3»'s own `test_repeat_count : u32 in 1 ..
        // 4294967295` divides a `u64` on the line right after `u64(test_repeat_count)`
        // (`K08-test-func.gab`) -- measured against a throwaway copy with the vocabulary
        // collision on `index` renamed out of the way: answering with the full `u64` range
        // here throws the declared lower bound away and `M102` fires on a denominator that
        // provably excludes zero. *A WIDENING (or same-width, same-sign) conversion drops no
        // value the source range did not already promise, so narrowing to it is not a guess
        // -- it is the same value, in a wider type.* A conversion that could lose bits still
        // gets the conservative answer, unchanged: the same one `F005`'s float mixing and
        // `D003`'s opaque carrier already give, and for the same reason.
        let (ziel_min, ziel_max) = typen::grenzen(breite, vorzeichen);
        let bereich = match quelltyp.durchgreifen() {
            Typ::Ganzzahl(q) if q.min >= ziel_min && q.max <= ziel_max => {
                IntBereich::genau(breite, vorzeichen, q.min, q.max)
            }
            _ => IntBereich::voll(breite, vorzeichen),
        };
        Typ::Ganzzahl(bereich)
    }

    /// **Bit intrinsics (PLAN-BITS §3): typing of the seven claimed calls.**
    ///
    /// The surface spells them per width until generics exist; the width here is
    /// the operand's OWN `breite`, so no width is named twice and none can
    /// disagree with the declaration. Ranges follow `PLAN-BITS.md` §3: the
    /// nonzero group (`clz`, `ctz`, `log2_floor`) needs `1 ..` (`M157`, with the
    /// `narrow` remedy the task asks for); every operand must be an unsigned
    /// standard width (`M158`/`M159`/`M160`); rotation needs the EXACT full
    /// range and an amount in `0 .. w-1` (`M159`); `bswap` needs `u16`/`u32`/`u64`
    /// (`M160`). Results are exact, never widened: `0 .. w-1` for the nonzero
    /// group, `0 .. w` for `popcount`, the full range for rotation and swap.
    ///
    /// An `Unbekannt` (or `never`) operand stays silent: there is nothing to
    /// hold against it, and inventing a width would be the `U10` defect again.
    /// An EMPTY range does the same -- `M117` owns it at the declaration.
    fn intrinsik_ruf(&mut self, name: &str, r: &Ruf, lage: &Lage) -> Typ {
        let will = match name {
            "rotl" | "rotr" => 2,
            _ => 1,
        };
        if r.argumente.len() != will {
            let code = match name {
                "rotl" | "rotr" => "M159",
                "bswap" => "M160",
                _ => "M158",
            };
            self.absagen.schiebe(
                Absage::fehler(
                    code,
                    r.span,
                    format!(
                        "`{name}` takes {will} argument(s), this call passes {}",
                        r.argumente.len()
                    ),
                )
                .mit_notiz(
                    "an intrinsic is a fixed form, not a declared function -- the form counts its \
                     operands, and a value beyond them is a statement about nothing the lowering \
                     could keep",
                ),
            );
            return Typ::Unbekannt;
        }
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
        }
        let code = match name {
            "rotl" | "rotr" => "M159",
            "bswap" => "M160",
            _ => "M158",
        };
        let (b, _span) = match self.intrinsik_bereich(&argtypen[0].0, argtypen[0].1, name, code, "operand") {
            Some(x) => x,
            None => return Typ::Unbekannt,
        };
        let w = b.breite;
        match name {
            "clz" | "ctz" | "log2_floor" => {
                if b.min < 1 {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M157",
                            argtypen[0].1,
                            format!(
                                "`{name}` needs an operand whose range excludes zero, \
                                 and `{}` does not",
                                b.text()
                            ),
                        )
                        .mit_notiz(
                            "SPRACHE.md §3: like a divisor, the argument must exclude \
                             zero -- the lowering reaches `__builtin_clz/ctz`, whose \
                             zero case is undefined",
                        )
                        .mit_notiz(
                            "the caller relies on the result lying in `0 .. w-1` -- \
                             with zero admitted, `31 - clz(x)` leaves the range the \
                             checker promised, and the index derivation breaks on \
                             exactly that case",
                        )
                        .mit_notiz(
                            "a check `if x >= 1 { … }` narrows it (V1), otherwise \
                             `narrow x to 1 .. … else { … }`",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                Typ::Ganzzahl(IntBereich::genau(w, false, 0, w as i128 - 1))
            }
            "popcount" => Typ::Ganzzahl(IntBereich::genau(w, false, 0, w as i128)),
            "rotl" | "rotr" => {
                if b.min != 0 || b.max != (1i128 << w) - 1 {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M159",
                            argtypen[0].1,
                            format!(
                                "`{name}` rotates a whole word and needs the exact \
                                 full range `u{w} in 0 .. {}, and `{}` is not it",
                                (1i128 << w) - 1,
                                b.text()
                            ),
                        )
                        .mit_notiz(
                            "rotation has no width except the operand's own -- on a \
                             narrowed range the wrap point is ambiguous, and an \
                             ambiguous wrap is a guess dressed as a proof; the \
                             caller relies on getting the whole word back",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                let (c, cspan) =
                    match self.intrinsik_bereich(&argtypen[1].0, argtypen[1].1, name, "M159", "amount") {
                        Some(x) => x,
                        None => return Typ::Unbekannt,
                    };
                if c.min < 0 || c.max > w as i128 - 1 {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M159",
                            cspan,
                            format!(
                                "`{name}` needs an amount in `0 .. {}`, and `{}` is not",
                                w as i128 - 1,
                                c.text()
                            ),
                        )
                        .mit_notiz(
                            "a shift by the width or more is undefined in C -- the \
                             amount is typed like a divisor, and `narrow` narrows it",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                Typ::Ganzzahl(IntBereich::voll(w, false))
            }
            _ => {
                if !matches!(w, 16 | 32 | 64) {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M160",
                            argtypen[0].1,
                            format!(
                                "`bswap` reverses whole bytes and needs `u16`, `u32` \
                                 or `u64`, and `{}` is none of them",
                                b.text()
                            ),
                        )
                        .mit_notiz(
                            "a one-byte value has no byte order to reverse -- write \
                             the value itself",
                        ),
                    );
                    return Typ::Unbekannt;
                }
                Typ::Ganzzahl(IntBereich::voll(w, false))
            }
        }
    }

    /// The integer range of an intrinsic operand: unsigned, standard width, known.
    ///
    /// Returns the range and the span it was read at. `None` is the honest exit:
    /// `Unbekannt`/`never` stay silent (nothing to hold), an empty range is
    /// `M117`'s at the declaration, and every other shape falls at `code`.
    fn intrinsik_bereich(
        &mut self,
        t: &Typ,
        span: Span,
        name: &str,
        code: &'static str,
        was: &str,
    ) -> Option<(IntBereich, Span)> {
        if let Typ::Benannt { undurchsichtig: true, name: bn, .. } = t.durchgreifen() {
            self.absagen.schiebe(
                Absage::fehler(
                    "D003",
                    span,
                    format!("`{bn}` is opaque -- it does not have the arithmetic of its carrier"),
                )
                .mit_notiz(
                    "bit intrinsics read the carrier's bits, and an `opaque type` \
                     says exactly that its carrier is hidden",
                ),
            );
            return None;
        }
        let Some(b) = t.bereich() else {
            if !matches!(t.durchgreifen(), Typ::Unbekannt | Typ::Nie) {
                self.absagen.schiebe(
                    Absage::fehler(
                        code,
                        span,
                        format!(
                            "`{name}` takes an unsigned integer {was}, and this one \
                             has type `{}`",
                            t.text()
                        ),
                    )
                    .mit_notiz(
                        "only `u8`, `u16`, `u32` and `u64` (or the `uN` sugar over them) carry bits -- \
                         a truth value, a pointer or a float has none to count, and counting is a \
                         statement about the operand's bit pattern",
                    ),
                );
            }
            return None;
        };
        if b.ist_leer() {
            return None;
        }
        if b.vorzeichen || !matches!(b.breite, 8 | 16 | 32 | 64) {
            self.absagen.schiebe(
                Absage::fehler(
                    code,
                    span,
                    format!(
                        "`{name}` takes an unsigned standard width (`u8`, `u16`, \
                         `u32`, `u64`), and `{}` is not one",
                        b.text()
                    ),
                )
                .mit_notiz(
                    "a signed operand has no unsigned bit pattern to read -- convert \
                     it first, where the conversion's own rule (`M144`/`M145`) holds",
                ),
            );
            return None;
        }
        Some((b, span))
    }

    /// **`M115` -- eine Vorbedingung, die am Rufort NACHWEISLICH falsch ist (2026-08-19).**
    ///
    /// Gemessen am selben Tag: `extern fn nimm(x : u32) requires bereit == 1;` gerufen mit
    /// unerfuelltem `bereit` -- **0 Fehler.** Der Vertrag kostete den Rufer nichts.
    ///
    /// ## Warum nur „nachweislich falsch" und nicht „nachweislich wahr"
    ///
    /// Die starke Fassung -- *der Rufer BEWEIST die Vorbedingung* -- braucht eine
    /// Entscheidungsprozedur ueber Tatsachen, und M1 hat keine: er stellt Fakten HER
    /// (`fakten_aus`), er entscheidet keine Praedikate. **Und sie zerlegte den Korpus**, denn
    /// an keiner der 51 fremden Deklarationen steht heute eine Vorbedingung, die ein Rufer
    /// hergeleitet haette.
    ///
    /// > **W10: nicht abgewiesen ist nicht bestaetigt.** Diese Regel weist ab, wo der Bereich
    /// > des Arguments die Bedingung AUSSCHLIESST, und schweigt sonst. *Eine untere Schranke,
    /// > und sie steht als solche da.*
    ///
    /// Gedeckt ist die Form `<parameter> <op> <zahl>` -- dieselbe, die `aus_ensures` in der
    /// Gegenrichtung liest. Alles Uebrige (Weltzustand, Quantoren) bleibt liegen und ist im
    /// TODO als die staerkere Haelfte gebucht.
    fn requires_pruefen(
        &mut self,
        ziel: &str,
        code: &'static str,
        sig: &crate::umgebung::Signatur,
        argtypen: &[(Typ, Span)],
    ) {
        for p in &sig.requires {
            let PredArt::Vergleich(e) = &p.art else { continue };
            let ExprArt::Binaer(op, a, c) = &e.art else { continue };
            let (name, op, zahl) = match (&a.art, &c.art) {
                (ExprArt::Ort(o), ExprArt::Zahl(n)) if o.suffixe.is_empty() => {
                    (o.basis.text.clone(), *op, *n as i128)
                }
                (ExprArt::Zahl(n), ExprArt::Ort(o)) if o.suffixe.is_empty() => {
                    (o.basis.text.clone(), gespiegelt(*op), *n as i128)
                }
                _ => continue,
            };
            let Some(i) = sig.parameter.iter().position(|(pn, _)| *pn == name) else { continue };
            let Some((t, span)) = argtypen.get(i) else { continue };
            let Some(b) = t.bereich() else { continue };
            // **Unmoeglich heisst: KEIN Wert des Bereichs erfuellt sie.**
            let unmoeglich = match op {
                BinOp::Kleiner => b.min >= zahl,
                BinOp::KleinerGleich => b.min > zahl,
                BinOp::Groesser => b.max <= zahl,
                BinOp::GroesserGleich => b.max < zahl,
                BinOp::Gleich => zahl < b.min || zahl > b.max,
                _ => false,
            };
            if unmoeglich {
                self.absagen.schiebe(
                    Absage::fehler(
                        code,
                        *span,
                        format!(
                            "`{}` requires `{name} {} {zahl}`, and the argument lies in \
                                {} .. {}",
                            ziel,
                            zeichen(op),
                            b.min,
                            b.max
                        ),
                    )
                    .mit_notiz(
                        "the callee's precondition is not merely unproved at this site \
                            but EXCLUDED by the range of the argument",
                    ),
                );
            }
        }
    }

    /// **`Variant(payload)` / `Variant()` -- the `tagged` case construction (lane 167).**
    ///
    /// Answers the owning sum type: the model's `Expr.fall cs i nutz` with `i` the
    /// declaration order and `nutz` the payload held against the case's type. The
    /// arity is the constructor's own (`N281`/`N282`); the payload RANGE is `M101`'s
    /// and its SHAPE `M140`'s, through the ordinary `passt` -- the same split the
    /// record constructor draws (`M106` for the shape, the range rules for the
    /// values). Labels never stand here (`N284`): a case takes its payload
    /// positionally, like `Some(x)` -- the one name a label could carry is the
    /// case itself, and it already stands in front.
    fn variantenkonstruktor(
        &mut self,
        r: &Ruf,
        name: &str,
        t: &crate::umgebung::VariantenTreffer,
        argtypen: &[(Typ, Span)],
    ) -> Typ {
        let kurz = crate::umgebung::kurzname(&t.summe);
        if !r.marken.is_empty() {
            self.absagen.schiebe(
                Absage::fehler(
                    "N284",
                    r.span,
                    format!(
                        "`{name}` is a case of the `tagged` type `{kurz}`, not a struct; \
                         its payload is positional"
                    ),
                )
                .mit_notiz(
                    "labels exist only at a record constructor (`M106`/`M107`) -- a case \
                     carries at most one payload, and the case name already says which",
                ),
            );
            self.buche(&t.summe_typ);
            return t.summe_typ.clone();
        }
        match (&t.nutzlast, argtypen.len()) {
            (None, 0) => {}
            (None, n) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "N282",
                        r.span,
                        format!(
                            "`{name}` is a case of `{kurz}` without a payload, but this \
                             construction passes {n} argument(s)"
                        ),
                    )
                    .mit_notiz(
                        "a nullary case constructs as `Case` or `Case()` -- an argument \
                         has no case type to stand against",
                    ),
                );
            }
            (Some(erwartet), 1) => {
                let (gegeben, span) = &argtypen[0];
                self.passt(gegeben, erwartet, *span, &format!("payload of variant `{name}`"));
            }
            (Some(_), n) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "N281",
                        r.span,
                        format!(
                            "`{name}` is a case of `{kurz}` with a payload, but this \
                             construction passes {n} argument(s)"
                        ),
                    )
                    .mit_notiz(
                        "a case carries exactly one payload -- `Case(payload)`; nothing \
                         stands beside it",
                    ),
                );
            }
        }
        self.buche(&t.summe_typ);
        t.summe_typ.clone()
    }

    /// **`M106` IST `deckt` aus `beweise/Verbund_Konstruktor.thy`, und `M107` ist die Frage,
    /// ob die Zuordnungsliste ueberhaupt eine ist.**
    ///
    /// Die Schablone `verbund.konstruktor` sagt: *„setzt jedes Feld genau einmal und laesst
    /// keins uninitialisiert."* Der Beweis fuehrt das auf eine Zeile zurueck --
    ///
    /// ```text
    /// deckt fs zs  ⟷  map fst zs = fs
    /// ```
    ///
    /// -- und die Zeile darunter ist genau dieser `!=`-Vergleich. *Beide Haelften der Zusage
    /// fallen zusammen, sobald die Deklaration wohlgeformt ist* (`deckt_setzt_jedes_genau_einmal`);
    /// deshalb steht hier **eine** Pruefung und nicht zwei.
    ///
    /// > Der Beweis fuehrt unter M-2 seine eigene Grenze: *nicht gezeigt ist, dass der
    /// > ERZEUGER `deckt` herstellt.* Das ist diese Funktion. Sie ist die Bruecke, und die
    /// > Mutation `verbundmarken-egal` ist ihre Sprechprobe.
    ///
    /// **Warum die REIHENFOLGE und nicht nur die Menge:** der Beweis waehlt `map fst zs = fs`
    /// bewusst gegen `set (map fst zs) = set fs` -- *eine Zuordnung, die nur die Menge trifft,
    /// sieht beim Leser aus wie die Deklaration und ist es nicht.*
    fn marken_pruefen(&mut self, r: &Ruf) {
        let gefunden = r.path().and_then(|p| self.u.verbundfelder(&self.modul, p)).cloned();
        let felder = gefunden.clone().unwrap_or_default();
        match (gefunden.is_some(), r.ist_verbundwert()) {
            // Ein Verbund mit Marken: der Schluesselstrom gegen die Felderliste.
            (true, true) => {
                let gegeben: Vec<String> = r.marken.iter().map(|m| m.text.clone()).collect();
                if gegeben != felder {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M106",
                            r.span,
                            format!(
                                "`{}` has the fields ({}), the constructor names ({})",
                                r.target_text(),
                                felder.join(", "),
                                gegeben.join(", ")
                            ),
                        )
                        .mit_notiz(
                            "the labels must be the field list -- in order, each exactly \
                                once, none left out",
                        )
                        .mit_notiz(
                            "Schablone `verbund.konstruktor`, bewiesen: \
                             `deckt fs zs ⟷ map fst zs = fs`",
                        ),
                    );
                }
            }
            // **Ein Verbund ohne Marken ist der stille Fall, gegen den die Entscheidung
            // steht.** `Punkt(x, y)` mit zwei `u32` laesst sich vertauschen, ohne dass ein
            // Typ dagegen spricht -- und ein Feldname ist das einzige, was die beiden
            // unterscheidet.
            (true, false) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M107",
                        r.span,
                        format!(
                            "`{}` is a struct; its constructor names its fields",
                            r.target_text()
                        ),
                    )
                    .mit_notiz(format!(
                        "`{}({})`",
                        r.target_text(),
                        felder
                            .iter()
                            .map(|f| format!("{f}: …"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .mit_notiz(
                        "two fields of the same type in sequence are interchangeable \
                            without a label, and nothing would say so",
                    ),
                );
            }
            // Marken an etwas, das kein Verbund ist. Eine Funktion hat Parameter, keine
            // Felder; eine Marke dort behauptet eine Zuordnung, die es nicht gibt.
            (false, true) => {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M107",
                        r.span,
                        format!("`{}` is not a struct; labels exist only at a constructor", r.target_text()),
                    )
                    .mit_notiz(
                        "the order of a function's parameters stands in its declaration; \
                            a second, labelled order would be a second truth",
                    ),
                );
            }
            (false, false) => {}
        }
    }

    // -- Fakten -------------------------------------------------------------------------

    /// V1/V2 aus einer geprueften Bedingung. `negiert` gilt fuer den `else`-Zweig.
    ///
    /// **VORBEDINGUNG, aufgeschrieben 2026-08-18 -- sie war immer da und stand nirgends:**
    /// der `negiert`-Zweig setzt voraus, dass die Negation einer Vergleichsbedingung selbst
    /// eine Vergleichsbedingung ist -- also eine **totale Ordnung ohne unvergleichbare
    /// Elemente**. Ueber ganzen Zahlen gibt `!(x < y)` das Faktum `x >= y`; das ist
    /// Trichotomie.
    ///
    /// > **Gleitkomma waere ihr erster Verletzer, nicht ihr einziger.** Ist ein Operand NaN,
    /// > sind ALLE Vergleiche falsch, und der `else`-Zweig gibt nichts -- vier Ausgaenge statt
    /// > drei. *Jeder partiell geordnete Traeger braeche dieselbe Maschinerie, und dies hier
    /// > ist die Stelle.*
    ///
    /// Heute traegt jeder Typ dieser Sprache eine totale Ordnung (`IntBereich`, `bool`), also
    /// gilt die Vorbedingung. **Sie steht hier, damit ein kuenftiger Traeger sie BRICHT statt
    /// sie stillschweigend zu unterlaufen** -- `SPRACHE.md` §3.2 fuehrt sie ausgeschrieben.
    fn fakten_aus(&mut self, bedingung: &Expr, negiert: bool, lage: &mut Lage) {
        match &bedingung.art {
            ExprArt::Klammer(i) => self.fakten_aus(i, negiert, lage),
            // `a && b` gibt im Ja-Zweig beide Fakten; im Nein-Zweig keinen (es reicht, dass
            // einer faellt, und welcher steht nicht fest).
            ExprArt::Binaer(BinOp::Und, a, b) if !negiert => {
                self.fakten_aus(a, false, lage);
                self.fakten_aus(b, false, lage);
            }
            ExprArt::Binaer(BinOp::Oder, a, b) if negiert => {
                self.fakten_aus(a, true, lage);
                self.fakten_aus(b, true, lage);
            }
            ExprArt::Binaer(op, a, b) if op.ist_vergleich() => {
                // **«F» -- das Herzstueck: die Negation ist BEDINGT, nicht abgeschaltet.**
                //
                // Ist ein Operand NaN, sind ALLE Vergleiche falsch, und aus `!(x < y)` folgt
                // `x >= y` nicht. Die Tatsache faellt darum genau dann an, wenn beide Seiten
                // als nicht-NaN bekannt sind -- und bekannt werden sie durch
                // `narrow … to finite` oder dadurch, dass sie Literale sind.
                //
                // *Damit ist Gleitkomma nicht faktenlos, sondern gewoehnlich: man wird NaN
                // einmal los und rechnet danach weiter.*
                if negiert && (self.nan_moeglich(a, lage) || self.nan_moeglich(b, lage)) {
                    return;
                }
                // **Ein GEGLUECKTER Vergleich impliziert Nicht-NaN auf BEIDEN Seiten.**
                //
                // Im Dann-Zweig von `if x < y` sind beide Operanden nan-frei, ohne jedes
                // `narrow` -- bei `<`, `<=`, `>`, `>=` und `==` gleichermassen. **Nur `!=`
                // gibt nichts her**, denn `NaN != NaN` ist wahr.
                //
                // *Genau darum waren zwei Bits richtig:* der Vergleich loescht EINS,
                // `narrow … to finite` loescht beide. Waere Endlichkeit ein Praedikat,
                // haette der Vergleich nichts beitragen koennen.
                //
                // Und `x == x` faellt damit von selbst in seine Rolle -- im Korpus die
                // Handschrift fuer `isnan`, hier ein Vergleich, dessen Dann-Zweig das
                // NaN-Bit loescht. **Er muss nicht als Idiom erkannt werden.**
                if !negiert && *op != BinOp::Ungleich {
                    for seite in [a, b] {
                        if let ExprArt::Ort(o) = &seite.art {
                            if matches!(
                                self.ausdruck(seite, lage).durchgreifen(),
                                Typ::Gleitkomma(_)
                            ) {
                                if let Some((schluessel, indizes)) = schluessel_und_indizes(o) {
                                    lage.fakten.push(Fakt::Endlich {
                                        schluessel,
                                        indizes,
                                        nan: true,
                                        unendlich: false,
                                    });
                                }
                            }
                        }
                    }
                }
                let op = if negiert { negiere(*op) } else { *op };
                self.vergleichsfakt(op, a, b, lage);
            }
            _ => {}
        }
    }

    /// **«F»: kann dieser Ausdruck NaN sein?**
    ///
    /// Nur Gleitkomma kann es. Ein Ganzzahlausdruck gibt `false`, und damit bleibt die
    /// Verengungsmaschinerie fuer den ganzen bisherigen Bestand unveraendert -- *die
    /// Erweiterung darf den gemessenen Pfad nicht anfassen* (Tor P-F1).
    /// **A QUESTION asked with the answering walk -- and it printed the answer twice**
    /// (measured 2026-09-03).
    ///
    /// `ausdruck` is the REFUSING walk: it types an expression and files every refusal that
    /// expression carries, and it books each sub-expression into the coverage count. This
    /// function wants one bit out of it -- *can this operand be NaN* -- and paid for it with
    /// a second copy of everything the operand had to say.
    ///
    /// ```gabbro
    /// let a = nimmt(x);          -- M140 once
    /// if nimmt(x) == 0 { … }     -- M140 TWICE, byte-identical
    /// ```
    ///
    /// Both halves are needed to reproduce it, and that is why it went unseen: an `if` over a
    /// bare call gives one (`fakten_aus` reaches no comparison arm), and a comparison outside
    /// an `if` gives one (nobody asks the negated question). *An `if` whose condition is a
    /// comparison and whose branch always leaves* is the cell where the `Wenn` arm walks the
    /// condition at `self.ausdruck(bedingung, lage)` and then walks it again from
    /// `fakten_aus(bedingung, true, …)`, through here.
    ///
    /// **Nothing is lost by staying quiet.** All three callers of `fakten_aus` hand it the
    /// same `bedingung` the arm typed one line earlier, so every refusal reachable from here
    /// has already been filed by that walk -- what this one adds is only the duplicate.
    ///
    /// > **The count is the other half, and it is the worse one.** `buche` runs on every
    /// > sub-expression of the second walk too, so `M1 saw N expressions, k of them without a
    /// > type` counted a stretch of the file twice -- *a coverage figure inflated by the
    /// > checker's own second look.* Both are restored here, and for the same reason.
    fn nan_moeglich(&mut self, e: &Expr, lage: &Lage) -> bool {
        let (gefuehrt, gezaehlt) = (self.absagen.absagen.len(), self.zaehlung);
        let t = self.ausdruck(e, lage);
        self.absagen.absagen.truncate(gefuehrt);
        self.zaehlung = gezaehlt;
        match t {
            Typ::Gleitkomma(f) => f.kann_nan,
            _ => false,
        }
    }

    fn vergleichsfakt(&mut self, op: BinOp, a: &Expr, b: &Expr, lage: &mut Lage) {
        // **«F»: derselbe Satz, andere Zahlen.** Bis 2026-08-18 lief hier nur `konst_wert`,
        // und das ist ganzzahlig -- ein Gleitkommavergleich loeschte das NaN-Bit und liess
        // die SCHRANKE offen. *Damit war `narrow … to <fbereich>` die einzige Quelle eines
        // Intervalls, und `if x < 1.0` sagte nichts ueber `x`.*
        if let (ExprArt::Ort(o), Some(w)) = (&a.art, self.u.gleitwert(b)) {
            if self.ist_gleitort(o, lage) {
                self.fintervallfakt(o, op, w, lage);
            }
        }
        if let (Some(w), ExprArt::Ort(o)) = (self.u.gleitwert(a), &b.art) {
            if self.ist_gleitort(o, lage) {
                self.fintervallfakt(o, spiegle(op), w, lage);
            }
        }
        // **«B33»: eine FLUECHTIGE Stelle traegt keine Tatsache.**
        //
        // Ein Geraeteregister senkt zu `*(volatile T *)(basis + versatz)` ab, und `volatile`
        // ist genau die Aussage *„zwischen zwei Lesungen darf sich das aendern."* Der
        // Vergleich liest einmal, die Verwendung liest ein zweites Mal -- die Schranke der
        // ersten Lesung gilt fuer die zweite nicht. Bis 2026-08-20 gab V1 sie trotzdem, und
        // `T.slots[d.ST.IDX]` ging mit null Fehlern durch.
        //
        // *Der Ausweg ist keine neue Grammatik, sondern die gewoehnliche Form: einmal in eine
        // lokale Bindung lesen und die Bindung verengen.*
        let fluechtig = |m1: &Self, e: &Expr| match &e.art {
            ExprArt::Ort(o) => m1.u.ist_registerort(&m1.modul, o, &lage.lokal),
            _ => false,
        };
        let (fa, fb) = (fluechtig(self, a), fluechtig(self, b));
        // V1 -- Stelle gegen Konstante, in beiden Schreibrichtungen.
        if let (ExprArt::Ort(o), Some(wert)) = (&a.art, self.u.konst_wert(&self.modul, b)) {
            if !fa {
                let _ = self.bereichsfakt(o, op, wert, lage);
            }
        }
        if let (Some(wert), ExprArt::Ort(o)) = (self.u.konst_wert(&self.modul, a), &b.art) {
            if !fb {
                let _ = self.bereichsfakt(o, spiegle(op), wert, lage);
            }
        }
        // V2 -- Stelle gegen Stelle, ausschliesslich als Vergleichsfakt.
        if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
            if fa || fb {
                return;
            }
            if let (Some((links, mut ia)), Some((rechts, ib))) =
                (schluessel_und_indizes(oa), schluessel_und_indizes(ob))
            {
                ia.extend(ib);
                lage.fakten.push(Fakt::Beziehung {
                    links,
                    op,
                    rechts,
                    indizes: ia,
                });
            }
        }
    }

    fn ist_gleitort(&self, o: &Ort, lage: &Lage) -> bool {
        matches!(
            self.u
                .typ_von_ort(&self.modul, o, &lage.lokal)
                .durchgreifen(),
            Typ::Gleitkomma(_)
        )
    }

    /// **Die Schranke aus einem Gleitkommavergleich.**
    ///
    /// `x < w` heisst `x <= vorheriger(w)` -- und *das* ist die Stelle, an der die
    /// Nachbarschaft der Gleitkommazahlen zaehlt: eine offene Schranke ist hier keine
    /// Naeherung, sondern ein benannter Nachbar.
    ///
    /// **Die Null bleibt die Ausnahme, die sie ist:** `nextDown(+0)` ist die groesste
    /// negative Zahl und nicht `-0.0`, denn `-0.0` ist nicht KLEINER als `+0.0`, sondern
    /// gleich. Damit faellt `x < 0.0` fuer `-0.0` zu Recht aus.
    fn fintervallfakt(&mut self, o: &Ort, op: BinOp, wert: f64, lage: &mut Lage) {
        let Some((schluessel, indizes)) = schluessel_und_indizes(o) else {
            return;
        };
        let (lo, hi) = match op {
            BinOp::GroesserGleich => (wert, f64::INFINITY),
            BinOp::Groesser => (wert.next_up(), f64::INFINITY),
            BinOp::KleinerGleich => (f64::NEG_INFINITY, wert),
            BinOp::Kleiner => (f64::NEG_INFINITY, wert.next_down()),
            BinOp::Gleich => (wert, wert),
            _ => return,
        };
        lage.fakten.push(Fakt::FIntervall {
            schluessel,
            indizes,
            lo,
            hi,
        });
    }

    fn bereichsfakt(&mut self, o: &Ort, op: BinOp, wert: i128, lage: &mut Lage) -> Option<()> {
        let (schluessel, indizes) = schluessel_und_indizes(o)?;
        let (min, max) = match op {
            BinOp::GroesserGleich => (wert, i128::MAX),
            BinOp::Groesser => (wert + 1, i128::MAX),
            BinOp::KleinerGleich => (i128::MIN, wert),
            BinOp::Kleiner => (i128::MIN, wert - 1),
            BinOp::Gleich => (wert, wert),
            // **Eine UNGLEICHHEIT an der Bereichsgrenze verengt** (2026-08-19).
            //
            // Bis hierher stand `!=` im `_`-Zweig, und der haeufigste Wachtposten der Sprache
            // kam nicht durch:
            //
            // ```gabbro
            // if n == 0 { return 0; }
            // return n - 1;              -- `M104`: verlaesst die Breite
            // ```
            //
            // *Die Negation floss laengst durch* -- `if n < 1 { return 0; }` war sauber. Was
            // fehlte, war der Schritt von `n != 0` auf `n >= 1`, und der ist **nur an einem
            // RAND** moeglich: ein Loch in der Mitte eines Intervalls ist kein Intervall.
            // Genau darum steht hier eine Fallunterscheidung und keine Verallgemeinerung --
            // *was nicht als Bereich gesagt werden kann, sagt dieser Pass nicht.*
            BinOp::Ungleich => {
                let grund = self.u.typ_von_ort(&self.modul, o, &lage.lokal);
                let b = self.mit_fakt(o, grund, lage).bereich()?;
                if wert == b.min {
                    (wert + 1, i128::MAX)
                } else if wert == b.max {
                    (i128::MIN, wert - 1)
                } else {
                    return None;
                }
            }
            _ => return None,
        };
        lage.fakten.push(Fakt::Bereich {
            schluessel,
            indizes,
            min,
            max,
        });
        Some(())
    }

    /// Der Typ eines Ortes, verengt durch die Fakten, die ueber ihn gelten.
    fn mit_fakt(&self, o: &Ort, grund: Typ, lage: &Lage) -> Typ {
        // **«F»: die zwei Bits zuerst** -- sie haengen an keinem Bereich, und ein
        // Gleitkommatyp hat gar keinen `bereich()` im Ganzzahlsinn.
        if let Typ::Gleitkomma(mut f) = grund {
            if let Some(schluessel) = schluessel_von(o) {
                for fk in &lage.fakten {
                    if let Fakt::Endlich {
                        schluessel: s,
                        nan,
                        unendlich,
                        ..
                    } = fk
                    {
                        if *s == schluessel {
                            if *nan {
                                f.kann_nan = false;
                            }
                            if *unendlich {
                                f.kann_unendlich = false;
                            }
                        }
                    }
                    if let Fakt::FIntervall {
                        schluessel: s,
                        lo,
                        hi,
                        ..
                    } = fk
                    {
                        if *s == schluessel {
                            f.lo = f.lo.max(*lo);
                            f.hi = f.hi.min(*hi);
                        }
                    }
                }
                // **Am SCHNITT, nicht je Fakt.** `x >= 0.0 && x <= 1.0` gibt zwei Fakten,
                // und jeder fuer sich ist halboffen -- erst zusammen sind sie endlich.
                // *Die erste Fassung pruefte je Fakt und liess die Bits stehen, obwohl das
                // Ergebnis sie ausschloss.*
                //
                // Und die Aussage ist scharf: **NaN liegt in KEINEM Intervall**, weil jeder
                // Vergleich mit ihm falsch ist, und unendlich liegt in keinem endlichen.
                if f.lo.is_finite() && f.hi.is_finite() {
                    f.kann_nan = false;
                    f.kann_unendlich = false;
                }
            }
            return Typ::Gleitkomma(f);
        }
        let Some(b) = grund.bereich() else {
            return grund;
        };
        let Some(schluessel) = schluessel_von(o) else {
            return grund;
        };
        let mut min = b.min;
        let mut max = b.max;
        for f in &lage.fakten {
            if let Fakt::Bereich {
                schluessel: s,
                min: lo,
                max: hi,
                ..
            } = f
            {
                if *s == schluessel {
                    min = min.max(*lo);
                    max = max.min(*hi);
                }
            }
        }
        if min == b.min && max == b.max {
            return grund;
        }
        Typ::Ganzzahl(IntBereich::genau(b.breite, b.vorzeichen, min, max))
    }

    /// V2 -- gibt die Untergrenze von `a - b`, wenn ein Vergleichsfakt sie traegt.
    fn beziehung(&self, a: &Ort, b: &Ort, lage: &Lage) -> Option<i128> {
        let (ka, kb) = (schluessel_von(a)?, schluessel_von(b)?);
        for f in &lage.fakten {
            if let Fakt::Beziehung {
                links, op, rechts, ..
            } = f
            {
                if *links == ka && *rechts == kb {
                    match op {
                        BinOp::GroesserGleich => return Some(0),
                        BinOp::Groesser => return Some(1),
                        _ => {}
                    }
                }
                if *links == kb && *rechts == ka {
                    match op {
                        BinOp::KleinerGleich => return Some(0),
                        BinOp::Kleiner => return Some(1),
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// *„bei jedem Schreiben auf eine beteiligte Stelle stirbt der Fakt"*.
    fn schreiben_toetet_fakten(&self, ziel: &Ort, lage: &mut Lage) {
        let Some(k) = schluessel_von(ziel) else {
            lage.fakten.clear();
            frische_alle_toeten(lage);
            return;
        };
        lage.fakten.retain(|f| match f {
            // **«F»: dieselbe Regel wie fuer den Bereich.** Wird die Stelle beschrieben,
            // faellt auch die Endlichkeitszusage -- *ein Fakt ueber einen Wert ueberlebt
            // dessen Ueberschreiben nicht.*
            Fakt::Endlich {
                schluessel,
                indizes,
                ..
            }
            | Fakt::FIntervall {
                schluessel,
                indizes,
                ..
            }
            | Fakt::Bereich {
                schluessel,
                indizes,
                ..
            } => !beruehrt(schluessel, &k) && !indizes.iter().any(|i| *i == k),
            Fakt::Beziehung {
                links,
                rechts,
                indizes,
                ..
            } => {
                !beruehrt(links, &k)
                    && !beruehrt(rechts, &k)
                    && !indizes.iter().any(|i| *i == k)
            }
        });
        // Ein Schreiben durch einen Zeiger kann alles Nichtlokale treffen -- ohne M3 gibt es
        // keine Aliasaussage, also faellt hier alles Nichtlokale mit.
        //
        // **Mit EINER Ausnahme, seit 2026-08-19: zwei verschiedene Felder desselben Objekts.**
        //
        // ```gabbro
        // narrow s.len to 0 ..< KAP else { … }
        // s.bytes[s.len] = b;      -- toetete bis dahin die Tatsache ueber `s.len`
        // s.len += 1;              -- und damit fiel M101
        // ```
        //
        // *Das ist die gewoehnlichste Form, die es gibt -- ein Puffer mit einer Laenge
        // daneben* -- und der Ordner fuehrte „allgemeine Zeichenketten" darum als nicht
        // schreibbar. **Der Grund war nicht die Sprache, sondern diese Vergroeberung.**
        //
        // `s.bytes` und `s.len` liegen im SELBEN Objekt an verschiedenen Versaetzen; ein
        // Schreiben auf das eine kann das andere nicht treffen. *Ein zweiter Zeiger auf
        // dasselbe `Text` aendert daran nichts -- er traefe `t.len`, und dessen Basis ist ein
        // anderer Name.*
        //
        // > **Die Ausnahme gilt NICHT fuer Varianten.** Bei einem `tagged` liegen die Felder
        // > uebereinander, und genau dann ist die grobe Regel die richtige.
        if k.contains('.') || k.contains("->") || k.contains('[') {
            let lage_kopie = &Lage {
                lokal: lage.lokal.clone(),
                fakten: Vec::new(),
                frisch: HashMap::new(),
                veraltet: HashMap::new(),
            };
            lage.fakten.retain(|f| match f {
                Fakt::Endlich { schluessel, .. }
            | Fakt::FIntervall { schluessel, .. }
            | Fakt::Bereich { schluessel, .. } => {
                    self.ist_lokal(schluessel) || self.getrenntes_feld(schluessel, &k, lage_kopie)
                }
                Fakt::Beziehung { links, rechts, .. } => {
                    (self.ist_lokal(links) || self.getrenntes_feld(links, &k, lage_kopie))
                        && (self.ist_lokal(rechts) || self.getrenntes_feld(rechts, &k, lage_kopie))
                }
            });
        }
        // **V4 freshness dies at the same writes** (spec §1-2, carrier granularity
        // §2a -- no path overlap, syntax only; own writes kill, §2b). A bare write
        // rebinds its own name instead: the old value is gone, taint and expiry
        // with it. Reached through `geschriebenes_toeten` for sub-blocks too.
        frische_toeten_schreiben(&ziel.basis.text, ziel.suffixe.is_empty(), lage);
    }

    /// Ein Aufruf toetet die Fakten ueber alles **Nichtlokale**. Lokale Groessen kann er
    /// nicht aendern: Gabbro hat keinen Adressoperator.
    /// **U5.** Ein Aufruf steht selten allein: `let t = nuller(z);` ist derselbe Aufruf wie
    /// `nuller(z);`. Vorher toetete nur die zweite Form Fakten -- ein Zeichen Unterschied
    /// entschied ueber die Zusage.
    fn rufe_im_ausdruck(&self, e: &Expr, lage: &mut Lage) {
        if enthaelt_ruf(e) {
            let mut pfade = Vec::new();
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    pfade.extend(rufnamen_im_ruf(r));
                }
            }
            self.rufe_toeten_fakten(&pfade, lage);
        }
    }

    /// **A call kills only what the callee can TOUCH** (2026-08-25).
    ///
    /// `aufruf_toetet_fakten` below deletes every non-local fact at EVERY call -- even at a
    /// `pure` one. Measured over a table with `backed`:
    ///
    /// ```gabbro
    /// narrow i to 0 ..< hinterlegt else { return 0; }
    /// rein();                        -- effects { pure }
    /// return h.slots[i].kopf;        -- M108: „nothing shows it is BACKED"
    /// ```
    ///
    /// **Three of four cases were false rejections** -- `pure`, a foreign `writes`, and only
    /// the fourth, which really writes `hinterlegt`, fired rightly. *Whoever has to narrow
    /// again after every call writes the narrowing until it is ceremony.*
    ///
    /// **The upper bound already stands there:** the callee's `effects`, which `E008`
    /// reconciles against its hull. What is not declared as a write cannot be written.
    ///
    /// > **And this precision rests on `E010`.** Its reach is a DRAWN line -- known world
    /// > state, and reads over parameters are missing. So the refinement applies **only**
    /// > when every written place is a known world name; otherwise the rule falls back to
    /// > the coarse one. *Incompleteness costs precision here, not soundness.*
    fn rufe_toeten_fakten(&self, pfade: &[&Pfad], lage: &mut Lage) {
        let Some(geschrieben) = self.geschriebene_orte(pfade) else {
            // **V4 -- the coarse path expires taints too** (2026-09-10). An
            // indirect call (`t->f()`) names no hull, so `pfade` is empty and
            // this early return ran before the V4 kill below: every non-local
            // V1 fact died while every taint lived on, and a stale decision
            // after an indirect call passed. An unknown callee can touch
            // anything, so every taint dies -- the same direction as V1-V3's
            // coarse rule. Pinned by `beispiele/gift/715`--`/717`.
            frische_alle_toeten(lage);
            return self.aufruf_toetet_fakten(lage);
        };
        let touches = |k: &str| {
            geschrieben.iter().any(|w| {
                k == w
                    || k.starts_with(&format!("{w}."))
                    || k.starts_with(&format!("{w}["))
                    || w.starts_with(&format!("{k}."))
                    || w.starts_with(&format!("{k}["))
            })
        };
        lage.fakten.retain(|f| {
            let schluessel: Vec<&String> = match f {
                Fakt::Endlich { schluessel, .. }
                | Fakt::FIntervall { schluessel, .. }
                | Fakt::Bereich { schluessel, .. } => vec![schluessel],
                Fakt::Beziehung { links, rechts, .. } => vec![links, rechts],
            };
            schluessel
                .iter()
                .all(|k| self.ist_lokal(k) || !touches(k))
        });
        // **V4 -- a call expires what its callee can touch** (spec §2d): the taints
        // of carriers in the callee's writes-hull (`effects` is mandatory, so the
        // hull is there to read). Without a readable hull every taint dies -- the
        // coarse rule, same direction as V1-V3's. No call, no kill.
        if !pfade.is_empty() {
            match self.geschriebene_orte(pfade) {
                Some(geschrieben) => {
                    for w in &geschrieben {
                        let traeger = w.split(['.', '[']).next().unwrap_or(w);
                        frische_toeten_traeger(lage, traeger);
                    }
                }
                None => frische_alle_toeten(lage),
            }
        }
    }

    /// The places these callees can write -- or `None` when the question cannot be
    /// answered safely and the coarse rule has to apply.
    fn geschriebene_orte(&self, pfade: &[&Pfad]) -> Option<Vec<String>> {
        if pfade.is_empty() {
            return None;
        }
        let mut aus: Vec<String> = Vec::new();
        for pf in pfade {
            // **The keys are QUALIFIED** (`a::b::f`), the call name is not --
            // `u.funktion` resolves module-aware. A `funktionen.get(name)` with the bare
            // name NEVER hits inside a `module` block and falls back silently to the coarse
            // rule: the refinement would have been there and done **nothing**. *Exactly the
            // kind of error that looks like „no finding" -- the same one `M103` already had
            // at `globale.get`.*
            let sig = self.u.funktion(&self.modul, pf)?;
            if sig.effect_list.is_empty() {
                return None;
            }
            for e in &sig.effect_list {
                if let Some(o) = ["writes ", "allocs ", "consumes ", "publishes ", "masks "]
                    .iter()
                    .find_map(|pfx| e.strip_prefix(pfx))
                {
                    // Only a KNOWN world name may be treated finely -- for everything
                    // else `E008` compares only the KIND, and there `writes a` covers
                    // `writes b`.
                    let basis = o.split(['.', '[']).next().unwrap_or(o);
                    // **The effect list names the CALLEE's parameter names.** A
                    // `writes h.slots` speaks about ITS `h`, not about an `h` out here --
                    // and if a parameter name happened to match a world name, this rule
                    // would judge the wrong place. *Then the coarse one applies.*
                    if sig.parameter.iter().any(|(n, _)| n == basis) {
                        return None;
                    }
                    if !self.u.ist_weltname(&self.modul, basis) {
                        return None;
                    }
                    aus.push(o.to_string());
                } else if !e.starts_with("reads ")
                    && !e.starts_with("locks ")
                    && e != "diverges"
                    && e != "pure"
                {
                    return None; // an effect kind this rule does not know
                }
            }
        }
        Some(aus)
    }

    fn aufruf_toetet_fakten(&self, lage: &mut Lage) {
        lage.fakten.retain(|f| match f {
            Fakt::Endlich { schluessel, .. }
            | Fakt::FIntervall { schluessel, .. }
            | Fakt::Bereich { schluessel, .. } => self.ist_lokal(schluessel),
            Fakt::Beziehung { links, rechts, .. } => {
                self.ist_lokal(links) && self.ist_lokal(rechts)
            }
        });
    }

    /// **U4.** Eine Stelle ist lokal, wenn sie weder Feld noch Index traegt **und kein
    /// globaler Name ist**. `static mut g` erfuellt die erste Haelfte -- ohne die zweite
    /// ueberlebt jeder Fakt ueber einen globalen Zaehler jeden Aufruf.
    /// **Liegen zwei Schluessel in verschiedenen Feldern DESSELBEN Objekts?**
    ///
    /// `s.bytes[i]` und `s.len` tun es: gleiche Basis, verschiedene erste Felder. Sie koennen
    /// einander nicht treffen, denn sie liegen an verschiedenen Versaetzen im selben Objekt.
    ///
    /// **Nicht fuer Varianten:** bei einem `tagged` liegen die Felder uebereinander. Der Typ
    /// der Basis muss ein Verbund sein, sonst gilt die grobe Regel.
    fn getrenntes_feld(&self, fakt: &str, geschrieben: &str, lage: &Lage) -> bool {
        let (fb, ff) = erstes_feld(fakt);
        let (gb, gf) = erstes_feld(geschrieben);
        match (ff, gf) {
            (Some(a), Some(b)) if fb == gb && a != b => {
                let ort = Ort {
                    basis: gabbro_syntax::ast::Ident {
                        text: fb.to_string(),
                        span: gabbro_syntax::span::Span::neu(0, 0),
                    },
                    suffixe: Vec::new(),
                    span: gabbro_syntax::span::Span::neu(0, 0),
                };
                matches!(
                    self.u.typ_von_ort(&self.modul, &ort, &lage.lokal).durchgreifen(),
                    Typ::Verbund(_)
                )
            }
            _ => false,
        }
    }

    /// **Ist dieser Ort LOKAL -- also einer, den ein fremder Ruf nicht anfassen kann?**
    ///
    /// Davon haengt `aufruf_toetet_fakten` ab: ein Fakt ueber einen lokalen Namen ueberlebt
    /// einen Ruf, ein Fakt ueber eine globale Groesse nicht.
    ///
    /// **Bis 2026-08-20 fragte diese Zeile `globale.contains_key(schluessel)` UNQUALIFIZIERT,
    /// und die Karte ist modulqualifiziert.** Also galt in jeder Datei mit `module` jede
    /// globale Groesse als lokal, und geloescht wurde nie.
    ///
    /// Die eigene Giftprobe dafuer steht seit jeher da -- `gift/22-globaler-fakt-nach-aufruf`,
    /// mit der Notiz *„damit das Loch nicht zurueckkehrt"* -- und war gruen: sie hat **kein**
    /// `module`. Dieselbe Datei gewickelt gab drei Fehler weniger. *Alle 38 sauberen
    /// Beispiele haben ein `module`.*
    ///
    /// > Die Umstellung auf qualifizierte Namen wurde am 2026-08-19 in `m2`, `phasen` und
    /// > `geteilt` gemacht. Diese Stelle blieb stehen -- **die Klasse war benannt und eine
    /// > Instanz behoben.**
    fn ist_lokal(&self, schluessel: &str) -> bool {
        if schluessel.contains('.') || schluessel.contains('[') || schluessel.contains("->") {
            return false;
        }
        self.u.suche_global(&self.modul, schluessel).is_none()
    }

    /// **V4 -- the carrier this place reads, if any** (spec §1-2).
    ///
    /// A device register read never taints (§2e -- asked of `m3`'s table, never a
    /// second one). A suffixed read through a plain local value (record, array) is
    /// no carrier read either (§2a: table/static/world names only -- a `ptr`
    /// parameter reads the world, a local record reads itself). A bare name reads
    /// its carrier only when no local binding covers it.
    fn traeger_von_ort(&self, o: &Ort, lage: &Lage) -> Option<String> {
        if crate::m3::ort_register(o, &self.geraete, &self.griffe).is_some() {
            return None;
        }
        if o.suffixe.is_empty() {
            if lage.lokal.contains_key(&o.basis.text) || self.ist_lokal(&o.basis.text) {
                return None;
            }
            // Immutable globals never go stale, so they taint nothing (§1: the map
            // holds table/static carriers only): a `const` or type name, and a
            // `static` without `mut` (M1's own map). Only a `static mut` -- and the
            // world behind a pointer -- can move under a held value.
            if self.u.nennt_typ_oder_konstante(&self.modul, &o.basis.text)
                || self.unveraenderliche_statiken.contains_key(&o.basis.text)
            {
                return None;
            }
            return Some(o.basis.text.clone());
        }
        // A suffixed read through a `ptr` reaches the world; through a plain local
        // value (record, array) it reads the local itself. NOTE: `durchgreifen`
        // sees THROUGH pointers (it answers the pointee for field access), so the
        // question here is asked of the type as stored, chasing aliases only.
        if let Some(t) = lage.lokal.get(&o.basis.text) {
            if !ist_zeiger(t) {
                return None;
            }
        }
        Some(o.basis.text.clone())
    }

    /// Carriers read DIRECTLY by this expression. Call arguments are NOT descended
    /// into: a call's return taint is its callee's reads-hull (spec §1), never its
    /// arguments'. Taints of mentioned locals flow through (a move changes no
    /// belief), and so does expiry. Answers whether an EXPIRED local was mentioned.
    fn traeger_im_ausdruck(
        &self,
        e: &Expr,
        lage: &Lage,
        aus: &mut std::collections::HashSet<String>,
    ) -> bool {
        let mut veraltet = false;
        match &e.art {
            ExprArt::Ruf(r) => {
                // **Lane 167: a construction carries its payload's taint.** A case
                // is no callee, so `rueckgabe_traeger` below answers nothing for
                // one -- but `let m = Kurz(stale)` binds the stale value itself,
                // and a copy holds the same snapshot (see the `veraltet` arm
                // below). Descending into the arguments keeps V4 precise; before
                // this lane no valid construction existed, so no clean program
                // changes its taint by it.
                if self.u.ist_variantenkonstruktor(&self.modul, r) {
                    for k in crate::unterausdruecke(e) {
                        veraltet |= self.traeger_im_ausdruck(k, lage, aus);
                    }
                } else {
                    aus.extend(self.rueckgabe_traeger(r, lage));
                }
            }
            ExprArt::Ort(o) | ExprArt::Alt(o) => {
                if let Some(c) = self.traeger_von_ort(o, lage) {
                    aus.insert(c);
                }
                if let Some(s) = lage.frisch.get(&o.basis.text) {
                    aus.extend(s.iter().cloned());
                }
                // An expired local's source carriers flow through a move with the
                // expiry itself: a copy holds the same snapshot value, so it is
                // stale against the same carriers. Without this a copy would
                // expire against nothing and read as disjoint from everything.
                if let Some(s) = lage.veraltet.get(&o.basis.text) {
                    veraltet = true;
                    aus.extend(s.iter().cloned());
                }
                for sx in &o.suffixe {
                    if let OrtSuffix::Index(x) = sx {
                        veraltet |= self.traeger_im_ausdruck(x, lage, aus);
                    }
                }
            }
            _ => {
                for k in crate::unterausdruecke(e) {
                    veraltet |= self.traeger_im_ausdruck(k, lage, aus);
                }
            }
        }
        veraltet
    }

    /// **V4 -- return taint is the callee's reads-hull** (spec §1).
    ///
    /// Hull entries naming a callee parameter are mapped through the caller's
    /// argument at that position; world names (tables, statics) stand as they are.
    /// An indirect call names no hull and taints nothing.
    fn rueckgabe_traeger(
        &self,
        r: &Ruf,
        lage: &Lage,
    ) -> std::collections::HashSet<String> {
        let mut aus = std::collections::HashSet::new();
        let Some(pf) = r.path() else {
            return aus;
        };
        let Some(sig) = self.u.funktion(&self.modul, pf) else {
            return aus;
        };
        for e in &sig.effect_list {
            let Some(rest) = e.strip_prefix("reads ") else {
                continue;
            };
            let basis = rest.split(['.', '[']).next().unwrap_or(rest);
            if let Some(i) = sig.parameter.iter().position(|(n, _)| n == basis) {
                if let Some(arg) = r.argumente.get(i) {
                    let mut tiefe = std::collections::HashSet::new();
                    self.traeger_im_ausdruck(arg, lage, &mut tiefe);
                    aus.extend(tiefe);
                }
            } else {
                aus.insert(basis.to_string());
            }
        }
        aus
    }

    /// **V4 -- the map grows at exactly one place: a `let`** (spec §1). A tainted
    /// move-in marks the name expired; a fresh carrier read taints it; anything
    /// else rebinds it clean. An expired name keeps the carriers the value was
    /// read or moved from -- including the expired carriers a moved local
    /// already carried -- so a later use can tell a disjoint index from a
    /// decision on the stale value itself.
    fn frische_wachsen(
        &self,
        name: &str,
        wert_traeger: std::collections::HashSet<String>,
        wert_veraltet: bool,
        lage: &mut Lage,
    ) {
        lage.frisch.remove(name);
        lage.veraltet.remove(name);
        if wert_veraltet {
            lage.veraltet.insert(name.to_string(), wert_traeger);
        } else if !wert_traeger.is_empty() {
            lage.frisch.insert(name.to_string(), wert_traeger);
        }
    }

    /// **V4 -- refusal at decision-use positions only** (spec §1).
    ///
    /// Branch/match condition, call argument, return value, `narrow` subject,
    /// index: acting on an expired local falls as `M147` -- with index-vs-content
    /// precision since lane 60: an occurrence inside an index into a carrier
    /// disjoint from the name's recorded sources is excused (see
    /// `frische_verweigere`). Store/move positions (write RHS, `let`
    /// re-binding) stay silent -- and so does every use of a local that was
    /// never tainted.
    fn frische_gebrauch(&mut self, s: &Stmt, lage: &Lage) {
        if lage.veraltet.is_empty() {
            return;
        }
        match &s.art {
            StmtArt::Wenn(w) => {
                for (b, _) in &w.zweige {
                    self.frische_verweigere(b, lage);
                }
            }
            StmtArt::Match(m) => self.frische_verweigere(&m.gegenstand, lage),
            StmtArt::Narrow(n) => {
                if lage.veraltet.contains_key(&n.ort.basis.text) {
                    self.frische_absage(&n.ort.basis.text, n.ort.span);
                }
            }
            StmtArt::Return(Some(e)) => self.frische_verweigere(e, lage),
            _ => {}
        }
        // Call arguments, wherever the call stands.
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    for a in &r.argumente {
                        self.frische_verweigere(a, lage);
                    }
                }
            }
        }
        if let StmtArt::Ruf(r) = &s.art {
            for a in &r.argumente {
                self.frische_verweigere(a, lage);
            }
        }
        if let StmtArt::LetSonst(l) = &s.art {
            if let Some(r) = l.als_ruf() {
                for a in &r.argumente {
                    self.frische_verweigere(a, lage);
                }
            }
        }
        // **Lane E1:** the arguments of a library call decide like any call's.
        if let StmtArt::LibraryCall(r) = &s.art {
            for a in &r.args {
                self.frische_verweigere(a, lage);
            }
        }
        // An index decides which cell is meant -- everywhere, including stores.
        // The indexed place's own basis travels as the enclosing index carrier,
        // so an index into a disjoint carrier is excused here exactly as it is
        // inside conditions and returns.
        let ziele: Vec<&Ort> = match &s.art {
            StmtArt::Zuweisung(z) => vec![&z.ziel],
            StmtArt::Publish(p) => vec![&p.ziel],
            StmtArt::Exchange(e) => vec![&e.ort],
            StmtArt::Narrow(n) => vec![&n.ort],
            StmtArt::LetSonst(l) => match &l.quelle {
                LetQuelle::Ort(o) => vec![o],
                LetQuelle::Ruf(_) => vec![],
            },
            StmtArt::AwaitLoad(a) => vec![&a.quelle],
            _ => vec![],
        };
        for o in ziele {
            let schutz = vec![o.basis.text.clone()];
            for sx in &o.suffixe {
                if let OrtSuffix::Index(x) = sx {
                    self.frische_verweigere_mit_schutz(x, lage, &schutz);
                }
            }
        }
    }

    /// Every expired local mentioned in this expression is refused, once per name --
    /// EXCEPT inside an index into a disjoint carrier (index-vs-content precision).
    ///
    /// An index value is a copied snapshot: writes to the carrier it was read from
    /// cannot change the copy, and where it is never re-compared against that
    /// carrier but only selects a cell of a DIFFERENT, disjoint carrier, the value
    /// is still the right id for that purpose. That is F01's teardown idiom
    /// (`let obj = c.slots[s].object; unlink(c, s); release_slot(c, s);` then
    /// `o.slots[obj]`): the prescribed remedy -- re-reading `c.slots[s].object`
    /// after `release_slot` -- would read a FREED slot, so a refusal whose remedy
    /// is wrong is worse than silence there. A decision on the value itself
    /// (branch condition, call argument, return, `narrow` subject, an index into
    /// its OWN carrier) still refuses -- that is what gift 702/703/709/715-717 pin.
    ///
    /// The walk covers exactly what `alle_ausdruecke` covers: every arm descends
    /// through `unterausdruecke` except `Ort` (basis plus index subtrees, the same
    /// two `alle_ausdruecke` sees) and `Ruf` (arguments, which decide -- never
    /// excused, even inside an index). The place BASIS itself is never excused:
    /// dereferencing through an expired handle decides which table is meant.
    fn frische_verweigere(&mut self, e: &Expr, lage: &Lage) {
        self.frische_verweigere_mit_schutz(e, lage, &[]);
    }

    /// Same refusal with an enclosing index context: `schutz` holds the bases of
    /// the index positions around `e`, outermost first. The statement-index loop
    /// passes its place's basis here; every other position starts unprotected.
    fn frische_verweigere_mit_schutz(&mut self, e: &Expr, lage: &Lage, schutz: &[String]) {
        let mut faellig: Vec<(String, Span)> = Vec::new();
        self.frische_sammle(e, lage, schutz, &mut faellig);
        let mut gemeldet = std::collections::HashSet::new();
        for (name, span) in faellig {
            if gemeldet.insert(name.clone()) {
                self.frische_absage(&name, span);
            }
        }
    }

    /// Collects the (name, span) pairs `frische_verweigere` refuses. `schutz`
    /// holds the bases of the enclosing index positions, outermost first: an
    /// occurrence is excused only when its recorded source set is non-empty and
    /// disjoint from every one of them. Unknown sources (empty set) and direct
    /// occurrences (empty `schutz`) refuse -- fail-closed, as before.
    fn frische_sammle(
        &self,
        e: &Expr,
        lage: &Lage,
        schutz: &[String],
        aus: &mut Vec<(String, Span)>,
    ) {
        match &e.art {
            ExprArt::Ort(o) | ExprArt::Alt(o) => {
                if let Some(quellen) = lage.veraltet.get(&o.basis.text) {
                    if quellen.is_empty()
                        || schutz.is_empty()
                        || schutz.iter().any(|b| quellen.contains(b))
                    {
                        aus.push((o.basis.text.clone(), o.span));
                    }
                }
                let mut tiefer = schutz.to_vec();
                tiefer.push(o.basis.text.clone());
                for sx in &o.suffixe {
                    if let OrtSuffix::Index(x) = sx {
                        self.frische_sammle(x, lage, &tiefer, aus);
                    }
                }
            }
            ExprArt::Ruf(r) => {
                for a in &r.argumente {
                    self.frische_sammle(a, lage, &[], aus);
                }
            }
            _ => {
                for k in crate::unterausdruecke(e) {
                    self.frische_sammle(k, lage, schutz, aus);
                }
            }
        }
    }

    fn frische_absage(&mut self, name: &str, span: Span) {
        self.absagen.schiebe(
            Absage::fehler(
                "M147",
                span,
                format!(
                    "`{name}` may be stale here: its carrier was written since `{name}` was read"
                ),
            )
            .mit_notiz(
                "re-read the carrier into this name after the write -- the re-read IS the \
                 refresh; storing or moving the name needs none, acting on it does",
            ),
        );
    }

    // -- Absagen ------------------------------------------------------------------------

    /// **What `100 % coverage` counts, and what it does not** (written down 2026-09-02).
    ///
    /// It counts expressions that RECEIVED a type -- one tick per `ausdruck` that did not
    /// answer `Unbekannt`. **It says nothing about how many CHECKS ran on them.** The line
    /// `gabbro pruefe` prints reads as a guarantee and measures the denominator of a
    /// different question, and that is a `W25` inside the type checker.
    ///
    /// > Measured that day: a pointer to the WRONG record at a call gave
    /// > `6 items, 0 errors, 0 hints` **and** `M1 saw 4 expressions, 0 of them without a
    /// > type (100 % coverage)`. All four expressions had a type. Nothing compared two of
    /// > them. *The number was true.*
    ///
    /// The folder has said the same thing twice from the other side -- `M119`
    /// (`tests/rechenwerk.rs`: *"M1 skips silently what it cannot type -- and printed
    /// `100 % coverage` for it, because it never saw the expression"*) and
    /// `messung/ZWEI-BLINDSTELLEN.md` (*"a coverage figure is not a refusal"*). Both are
    /// about the UNTYPED side; this note is about the typed one, and it is the side that
    /// reads as reassurance.
    ///
    /// **The wording is deliberately NOT changed.** Ten transcripts quote the line verbatim
    /// -- `messung/FNPTR.md`, `ERZEUGER.md`, `OPS-RELABEL.md`, `C-NAMEN.md`,
    /// `UEBERSETZUNGSREICHWEITE.md`, `TUTORIAL.md`, two probe headers under
    /// `messung/proben/` and two poison probes -- and each of them is a MEASUREMENT of a
    /// past run. *Renaming the field would falsify a record instead of correcting a
    /// statement.* What was missing was the statement, and it stands here.
    fn buche(&mut self, t: &Typ) {
        if t.ist_unbekannt() {
            self.zaehlung.unbekannt += 1;
        } else {
            self.zaehlung.typisiert += 1;
        }
    }

    /// **`D004`: die Wand vor der Tuer.**
    ///
    /// `opaque` biss seit `5e9f31e` an der RECHNUNG (`D003`) -- und die implizite Umwandlung
    /// ging in BEIDE Richtungen still durch. Gemessen 2026-08-18:
    ///
    /// ```gabbro
    /// opaque type Pa = u64;
    /// impl fn hinein(x : u64) -> Pa { return x; }   -- 0 Fehler
    /// impl fn hinaus(p : Pa) -> u64 { return p; }   -- 0 Fehler
    /// ```
    ///
    /// **Damit war D1 -- der erste der beiden Deklarationsregeln -- gar nicht durchgesetzt.**
    /// Es fehlte nicht die Tuer, sondern die Wand; eine Tuer in einer Wand, die es nicht
    /// gibt, ist keine.
    ///
    /// Und die Tuer steht da, wo die Dokumente sie hinstellen: *„opaque, one generator"* mit
    /// **Modulgrenze**. Im erklaerenden Modul ist die Darstellung bekannt und die Umwandlung
    /// erlaubt; ausserhalb ist sie es nicht. *Damit bekommt die Modulgrenze ihre erste
    /// Bedeutung in diesem Pruefer -- und `pub` seine zweite Aufgabe, wenn es je eine
    /// bekommt.*
    fn undurchsichtigkeit_pruefen(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        let wand = |t: &Typ, anderer: &Typ| -> Option<(String, String)> {
            let Typ::Benannt {
                name,
                undurchsichtig: true,
                heimat,
                ..
            } = t
            else {
                return None;
            };
            // Derselbe Typ auf beiden Seiten ist keine Umwandlung.
            if let Typ::Benannt { name: n2, .. } = anderer {
                if n2 == name {
                    return None;
                }
            }
            if matches!(anderer, Typ::Unbekannt) {
                return None;
            }
            Some((name.clone(), heimat.clone()))
        };
        let Some((name, heimat)) = wand(quelle, ziel).or_else(|| wand(ziel, quelle)) else {
            return;
        };
        if self.modul == heimat {
            return;
        }
        self.absagen.schiebe(
            Absage::fehler(
                "D004",
                span,
                format!("{was} silently converts `{name}`"),
            )
            .mit_notiz(
                "D1: an opaque newtype has NO implicit conversion to its carrier",
            )
            .mit_notiz(format!(
                "the conversion belongs in `{heimat}`, which declares the type -- outside \
                    it the representation is unknown",
            )),
        );
    }

    /// **`Some(i)` wird gegen die NUTZLAST geprueft, nicht gegen den Optionstyp.**
    ///
    /// Der Optionstyp enthaelt den Sonderwert -- das ist seine ganze Bauart, und sein
    /// Bereich reicht deshalb bis `N`. Die Nutzlast enthaelt ihn nicht: `Some i` steht fuer
    /// einen **gueltigen** Index, `0 ..< N`.
    ///
    /// > *Wer `Some(N)` schreiben darf, hat `None` geloescht* -- `kodiere_injektiv` in
    /// > `beweise/Option_Sonderwert.thy` haengt genau an dieser Trennung.
    ///
    /// Ueberall sonst faellt der Aufruf auf `passt` zurueck.
    fn passt_wert(&mut self, wert: &Expr, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        match (ist_some(wert), option_nutzlast(ziel)) {
            (true, Some(nutzlast)) => self.passt(quelle, &nutzlast, span, was),
            _ => self.passt(quelle, ziel, span, was),
        }
    }

    /// **`M128` -- a function pointer promises no LESS than the slot it goes into.**
    ///
    /// The rule that turns the contract at the pointer type from a decoration into a fact.
    /// Assignment is **subsumption, not equality**: `&f` fits a `fn(…)` slot when
    ///
    /// * every effect `f` declares is one the slot allows -- *not the other way round*, and
    ///   not "the same set": a `pure` function belongs in a slot that permits `writes X`, and
    ///   forbidding that would make every ops table declare its widest member's effects at
    ///   every member;
    /// * `f` costs at most what the slot promises;
    /// * the shapes agree in arity.
    ///
    /// **The direction is the entire content.** Reversed, a slot promising `pure` would accept
    /// a function that writes the world, and every pass downstream -- the hull, `E008`,
    /// `K001` -- would compute with the promise instead of the fact. *That is the exact shape
    /// of a false green, and it is why this comparison could not be left to `PartialEq`.*
    fn fnptr_passt(&mut self, q: &crate::typen::FnPtrContract, z: &crate::typen::FnPtrContract, span: Span) {
        // **One rule, one refusal site.** The three ways a pointer can fail to fit -- arity,
        // an effect the slot forbids, a cost above the bound -- are three readings of one
        // sentence, so they share one `Absage`. *Three sites would look like three rules to
        // `instrumente/pruefe-vergabe.py`, and a poison probe on `M128` would stop saying
        // which of them it caught.*
        let grund = if q.parameters.len() != z.parameters.len() {
            Some(format!(
                "it takes {} parameters, the slot takes {}",
                q.parameters.len(),
                z.parameters.len()
            ))
        } else if let Some(w) = q
            .effects
            .iter()
            // `pure` promises LESS than anything, so it fits every slot.
            .find(|w| *w != "pure" && !z.effects.iter().any(|x| x == *w))
        {
            Some(format!("it declares `{w}`, which the slot does not allow"))
        } else {
            match (q.costs, z.costs) {
                (Some(a), Some(b)) if a > b => {
                    Some(format!("it costs {a} ops, the slot promises {b}"))
                }
                _ => None,
            }
        };
        let Some(grund) = grund else { return };
        self.absagen.schiebe(
            Absage::fehler(
                "M128",
                span,
                format!("`{}` does not fit `{}`: {grund}", q.shape(), z.shape()),
            )
            .mit_notiz(
                "a function pointer may promise LESS than its slot, never more -- the slot's \
                 promise is what every caller through it computes with, and `E008` and \
                 `K001` compute with it",
            )
            .mit_notiz("either widen the contract at the pointer type, or narrow the function"),
        );
    }

    /// **`M141` -- the SIGNATURE at a `fn(…)` slot, which `M128` never compared.**
    ///
    /// Measured 2026-09-02 against the unchanged checker: `&eng` with `eng(b : u8) -> u8`
    /// went into a `fn(u32) -> u32` slot with **`0 errors` and `100 % coverage`**, the
    /// emitter wrote `.f = &eng`, and `cc` refused it -- *initialization of
    /// `uint32_t (*)(uint32_t)` from incompatible pointer type*. **The `N041` shape: the
    /// checker confirms and the foreign compiler holds the line.**
    ///
    /// ## Why this is a rule of its own and not a fourth reading of `M128`
    ///
    /// `M128`'s sentence is *a function pointer promises no LESS than the slot*, and its own
    /// note says so: **may promise less, never more.** That sentence is FALSE here.
    /// `fn(u32)` at a `fn(u8)` slot is just as wrong as the other way round, because nothing
    /// converts at an indirect call -- the caller pushes the slot's word and the callee reads
    /// its own. *A subsumption and an equality under one identifier would make `gift/241`
    /// green while this half is out, and its poison probe could no longer say which of them
    /// it caught.*
    ///
    /// ## What is compared, per component -- and what is not
    ///
    /// | component | held here | by whom otherwise |
    /// |---|---|---|
    /// | arity | **no** -- and it is the precondition, not an omission | `M128`, which returns first |
    /// | parameter types | **yes**, positionally, as a machine word | -- |
    /// | result present / absent | **yes** | -- |
    /// | result type | **yes**, the same way | -- |
    /// | `effects` | **no** | `M128` |
    /// | `costs` | **no** | `M128` |
    /// | parameter NAMES | **no**, deliberately | nobody: a name at a pointer type binds nothing unless an effect line reads it (`ast::FnZeigerParam`) |
    /// | the declared RANGE | **no**, deliberately -- see below | nobody, and it is named in `TODO.md` |
    ///
    /// **The range is the half `cc` cannot see, and it is left open on purpose.** `u32 in
    /// 0 .. 9` and `u32` are one C type and one ABI, so `darstellung_grund` passes them --
    /// but a function declaring the narrower one accepts LESS than the slot promises, and a
    /// caller through the slot may hand it 1000. *That is a contravariance rule with its own
    /// direction and its own measurement, and writing it into this one would make a rule
    /// about representation quietly also a rule about values.* The refusal says which half
    /// it is.
    fn fnptr_signatur_passt(
        &mut self,
        q: &crate::typen::FnPtrContract,
        z: &crate::typen::FnPtrContract,
        span: Span,
    ) {
        // **Arity is `M128`'s and it reports first.** Position `i` cannot be compared where
        // there is no position `i`, so this is a precondition and not a second opinion.
        if q.parameters.len() != z.parameters.len() {
            return;
        }
        // **One rule, one refusal site** -- the same reason `fnptr_passt` gives one door
        // above. A parameter and the result are two positions of one signature.
        let grund = q
            .parameters
            .iter()
            .zip(z.parameters.iter())
            .enumerate()
            .find_map(|(i, ((_, a), (_, b)))| {
                darstellung_grund(a, b).map(|g| format!("at parameter {}, {g}", i + 1))
            })
            .or_else(|| match (&q.result, &z.result) {
                (Some(a), Some(b)) => darstellung_grund(a, b).map(|g| format!("in the result, {g}")),
                (None, Some(b)) => Some(format!(
                    "it returns nothing, the slot promises `{}`",
                    b.text()
                )),
                (Some(a), None) => Some(format!(
                    "it returns `{}`, the slot takes no result",
                    a.text()
                )),
                (None, None) => None,
            });
        let Some(grund) = grund else { return };
        self.absagen.schiebe(
            Absage::fehler(
                // **`M142` and not `M141` -- the FOURTH code collision in three days.**
                // `domaene.rs` had taken `M141` for the literal index in a predicate and was
                // already on `master` when this rule was written. *Two lanes reading the same
                // free-number list at the same hour is not carelessness; it is what a list
                // without a reservation does* -- and `pruefe-vergabe.py` is the only reason
                // any of the four was noticed before it made every probe on the code
                // ambiguous.
                "M142",
                span,
                format!("`{}` does not fit `{}`: {grund}", q.shape(), z.shape()),
            )
            .mit_notiz(
                "nothing converts at an indirect call: the caller pushes what the SLOT's type \
                 says and the callee reads what its own declaration says, so the two must be \
                 the same machine value",
            )
            .mit_notiz(
                "this compares the SIGNATURE only -- `effects` and `costs` are `M128`'s, and \
                 the declared RANGE of a number is held by nobody at a `fn(...)` slot",
            ),
        );
    }

    /// **The higher-order refinement, harvested (lane 177).**
    ///
    /// Where a named function `&f` flows into a `fn(…)` slot, the LOGIC half of the
    /// refinement is nobody's decision procedure: `requires_slot ⇒ requires_f`
    /// (contravariant -- `f` accepts at least what the slot promises callers may pass)
    /// and `ensures_f ⇒ ensures_slot` (covariant -- `f` delivers at least what the
    /// slot promises). **The direction is the content**: swapping the two hands a
    /// caller a promise the producer never made, and that is exactly what
    /// `beispiele/gift/957`-`958` pin.
    ///
    /// This function HARVESTS (one record per non-trivial half) and HINTS (`N297` at
    /// the site). The record travels to `gabbro obligations` (kind `C`) through
    /// `zeigerverfeinerungen`, harvested in the same run -- *the same run and the same
    /// reader*, the shape `fremdverengungen` above stands for.
    ///
    /// A half is recorded only where it can fail: the `requires` half where `f`
    /// carries any (`true ⇒ R_f` is otherwise trivially true), the `ensures` half
    /// where the SLOT carries any (`E_f ⇒ true` is otherwise trivially true). Where
    /// both sides carry nothing there is no obligation, and where the producer is
    /// unknown (a slot behind a slot) there is no one to owe it.
    fn zeigerverfeinerung_ernten(
        &mut self,
        q: &crate::typen::FnPtrContract,
        z: &crate::typen::FnPtrContract,
        span: Span,
    ) {
        let Some(erzeuger) = q.producer.clone() else { return };
        let mut haelften: Vec<(&str, String)> = Vec::new();
        if !q.requires.is_empty() {
            haelften.push((
                "requires",
                format!(
                    "`&{erzeuger}` accepts what `{}` promises: requires of the slot holds \
                     only what requires of `&{erzeuger}` allows",
                    z.shape()
                ),
            ));
        }
        if !z.ensures.is_empty() {
            haelften.push((
                "ensures",
                format!(
                    "`&{erzeuger}` delivers what `{}` promises: ensures of `&{erzeuger}` \
                     holds only what ensures of the slot allows",
                    z.shape()
                ),
            ));
        }
        if haelften.is_empty() {
            return;
        }
        // **Whose body it is.** The lookup re-spells the producer's path; the text it
        // was written with joins with `::`, so the split round-trips (`Pfad::text`).
        let pfad = gabbro_syntax::ast::Pfad {
            teile: erzeuger
                .split("::")
                .map(|t| gabbro_syntax::ast::Ident {
                    text: t.to_string(),
                    span,
                })
                .collect(),
            span,
        };
        let rumpf_da = self
            .u
            .funktion(&self.modul, &pfad)
            .is_some_and(|s| s.rumpf_da);
        for (haelfte, satz) in haelften {
            self.absagen.schiebe(
                Absage::hinweis(
                    "N297",
                    span,
                    format!("higher-order refinement ({haelfte}): {satz}"),
                )
                .mit_notiz(
                    "the implication is the USER's logic: it stands as kind `C` in \
                     `gabbro obligations` and is decided by no pass -- contravariant \
                     in `requires`, covariant in `ensures`",
                )
                .mit_notiz(
                    "effects, costs, arity and signature are decided, not hinted \
                     (`M128`/`M142` beside this line)",
                ),
            );
            self.zeigerverf.push(ZeigerVerfeinerung {
                rufer: self.rufer.clone(),
                erzeuger: erzeuger.clone(),
                haelfte: haelfte.to_string(),
                slot_gestalt: z.shape(),
                f_requires: q.requires.clone(),
                slot_requires: z.requires.clone(),
                f_ensures: q.ensures.clone(),
                slot_ensures: z.ensures.clone(),
                f_rumpf_da: rumpf_da,
                span,
            });
        }
    }

    /// **`M135` -- `bool` is not a number, and the comparison below cannot say so.**
    ///
    /// `passt` ends in a comparison of RANGES, and `Typ::Wahrheit` has none
    /// (`typen::bereich` answers `Some` for `Ganzzahl`, `Umlaufend` and `Register` and
    /// `None` for the rest). Where one side has no range the comparison returns without a
    /// word -- so `M101` holds `-> u8 { return 300; }` and says nothing at all about
    /// `-> bool { return 7; }`.
    ///
    /// **Measured 2026-08-31** (`messung/proben/probe-rueckgabetyp.gab`): four falsified
    /// returns in one file, and exactly one falls -- the one where both sides carry a
    /// range. The other three cross the `bool`/number boundary and pass.
    ///
    /// ## Why this is worth a refusal when `cc` accepts the C
    ///
    /// It is not a defect the next stage catches. `emit` writes `return 7;` into a `bool`
    /// function and `cc -O0 -Wall -Wextra -Werror` takes it: C converts. **That is what
    /// makes it worse and not better.** The sharpest site is a probe
    /// (`messung/proben/probe-probenurteil-typ.gab`):
    ///
    /// ```gabbro
    /// can_fail { if k >= 3 { return 7; } return true; }
    /// ```
    ///
    /// `7` is not zero, so the probe HOLDS on that path -- always. *A counterprobe that
    /// cannot fall is a measuring instrument stuck at green*, and every stage of this
    /// bench reports it as sound. The `W16` shape, in the tool that holds the duties.
    ///
    /// ## The exception, and the corpus wrote it
    ///
    /// **A range of exactly `0 .. 1` is not a crossing.** `beispiele/gift/416` reads a
    /// one-bit device field into a `bool`:
    ///
    /// ```gabbro
    /// reg LSR : u8 @0x3FD class r fields { THRE @5, }
    /// impl fn lies_lsr(d : ptr<mmio, r> SerialCom1) -> bool { return d.LSR.THRE; }
    /// ```
    ///
    /// `THRE` has type `u8 in 0 .. 1` -- **a type that admits both truth values and
    /// nothing else carries the same question as `bool`**, and the driver idiom that reads
    /// a flag bit is not the defect this rule was built on. *The line is the RANGE and not
    /// the width:* `return 1;` has type `u8 in 1 .. 1`, admits one value, and still falls.
    ///
    /// ## What it deliberately does NOT say
    ///
    /// **Only the `bool`/number boundary**, because that is the one that was falsified.
    /// A float against an integer crosses the same silent `else` in `passt` and is named
    /// in `messung/proben/probe-rueckgabetyp.gab`, not refused here -- *Regel A: the
    /// measurement decides the reach of the rule, not the symmetry of the code.*
    ///
    /// > **The float sentence above is a statement about THIS rule and, since 2026-09-02, no
    /// > longer one about the checker.** `M139` closed the silent `else` itself, and the
    /// > integer/float crossing falls there. What stays here is the split: `M139` hands the
    /// > `bool`/number pair BACK to this rule, because only this one carries the `0 .. 1`
    /// > exception a device flag needs -- *two refusals at one site look like two rules, and
    /// > `beispiele/gift/430` would fall green while this one is out.*
    fn wahrheit_ist_keine_zahl(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        fn ist_zahl(t: &Typ) -> bool {
            matches!(
                t,
                Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Gleitkomma(_) | Typ::Register { .. }
            )
        }
        /// Admits exactly the two truth values and nothing else.
        fn ist_bitbreit(t: &Typ) -> bool {
            t.bereich().is_some_and(|b| b.min == 0 && b.max == 1)
        }
        let (q, z) = (quelle.durchgreifen(), ziel.durchgreifen());
        let (qw, zw) = (matches!(q, Typ::Wahrheit), matches!(z, Typ::Wahrheit));
        if !((qw && ist_zahl(z)) || (ist_zahl(q) && zw)) {
            return;
        }
        if ist_bitbreit(q) || ist_bitbreit(z) {
            return;
        }
        self.absagen.schiebe(
            Absage::fehler(
                "M135",
                span,
                format!(
                    "{was} requires `{}`, the value has `{}`",
                    ziel.text(),
                    quelle.text()
                ),
            )
            .mit_notiz(
                "`bool` is not a number: it says HELD or FALLEN, and a number says how \
                 many -- the two carry different questions and neither answers the other's",
            )
            .mit_notiz(
                "no stage after this one says it either: the emitter writes the value \
                 straight into the C, and C converts silently -- `return 7` in a `bool` \
                 function is `return true` and no warning is printed",
            ),
        );
    }

    /// **`M139` -- the two types are not of the same SHAPE, and `passt` had no word for it.**
    ///
    /// Everything else in `passt` compares a RANGE: `M101` the interval, `M104` the width,
    /// `F001`/`F002` the two float bits, `M128` the contract at a function pointer. The
    /// function ends in
    ///
    /// ```text
    /// let (Some(q), Some(z)) = (quelle.bereich(), ziel.bereich()) else { return; };
    /// ```
    ///
    /// and `typen::bereich` answers `Some` for `Ganzzahl`, `Umlaufend` and `Register` and
    /// `None` for everything else. **A pointer has no range, a record has none, an array has
    /// none** -- so at every one of those the comparison ended in a silent `else`.
    ///
    /// ## What that cost, measured 2026-09-02
    ///
    /// Eighteen parameter kinds against eighteen argument kinds, one file per cell, the
    /// wrong thing passed at a call: **283 of 306 off-diagonal cells went through with
    /// `0 errors`, and the run said `100 % coverage` at each.** The sharpest one is a
    /// pointer to the wrong record:
    ///
    /// ```gabbro
    /// impl fn nimmt(q : ptr<normal, r> Text) -> u32 in 0 .. KAP …
    /// impl fn ruft(a : ptr<normal, r> Andr) -> u32 in 0 .. KAP … { return nimmt(a); }
    /// ```
    ///
    /// `gabbro pruefe` said `6 items, 0 errors`, `gabbro emit` wrote `nimmt(a)` with a
    /// `const Andr *`, and **`cc` answered** -- *"passing argument 1 of 'nimmt' from
    /// incompatible pointer type"*. That is the `N041` shape: the trust base holds, in the
    /// wrong place. Of the 283 silent cells `cc` caught 165 and the emitter refused 96
    /// (`C001`, an array has no lowering as a parameter) -- **22 reached green C**, and TWELVE
    /// of those carried a value no C compiler was ever going to question: four
    /// `bool` <- pointer and eight integer/float. The other ten are correct calls or
    /// `D004`'s, which is silent inside the module that declares the `opaque type`.
    ///
    /// ## What it compares, and what it deliberately leaves
    ///
    /// **The coarse shape**, and where two shapes agree and both sides carry a NAME over an
    /// aggregate, the name. Two records are two declarations even when their fields line up
    /// -- `N030` says the same for `opaque`, `linear`, `ghost` and `tagged`, and this is the
    /// half of that sentence which lives behind a `ptr`.
    ///
    /// It leaves what other rules own: `D004` the opaque conversion, `M135` the
    /// `bool`/number crossing where a range of `0 .. 1` makes it not one, `M101` the
    /// interval, `R008` the address space. **And it leaves a range alias alone** -- `type
    /// Zaehler = u32 in 0 .. 65535` lowers to its carrier and is transparent by
    /// construction, so `gestalt` looks THROUGH `Benannt` and the nominal half only bites
    /// over an aggregate. *Taking a scalar alias nominally would be a language change, not
    /// a hole being closed* (`N030`, 2026-08-20).
    ///
    /// > **`Unbekannt` and `never` stay silent, both of them.** `W10: not refused is not
    /// > confirmed` -- and `Unbekannt` is precisely what the coverage number counts, so a
    /// > refusal built on it would turn the honest exit into a false red.
    fn gestalt_passt(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) -> bool {
        // **One rule, one refusal site** -- same reason as `fnptr_passt`: the three ways a
        // shape can miss (the kind, the pointee's kind, the name over an aggregate) are
        // three readings of one sentence, and three `Absage`s would look like three rules
        // to `instrumente/pruefe-vergabe.py`.
        let Some(grund) = gestalt_grund(quelle, ziel) else { return false };
        // **`M140` and not `M139`, and the split was forced by a measurement.** Two lanes
        // picked the same free number on 2026-09-02 -- one for a literal wider than `i128`,
        // this one for an argument whose SHAPE does not match its parameter. They are two
        // rules, and `pruefe-vergabe.py` said so at the merge: candidates 20 -> 21.
        // *A code carrying two rules makes every probe on it ambiguous, retroactively.*
        self.absagen.schiebe(
            Absage::fehler(
                "M140",
                span,
                format!(
                    "{was} requires `{}`, the value has `{}` -- {grund}",
                    ziel.text(),
                    quelle.text()
                ),
            )
            .mit_notiz(
                "this pass compares RANGES, and neither of these two has one -- until \
                 today the comparison ended here without a word",
            )
            // **The load-bearing reason, and it is not the representation.** Written after
            // `pruefe-gruende.py` filed this rule under `unklar` (2026-09-02): the first
            // note says what the checker DID, which is a statement about the pass and not
            // about the program. *A refusal that cannot say why it exists teaches the
            // reader to route around it.*
            .mit_notiz(
                "what a slot DECLARES is the promise every pass behind it computes with: \
                 the effect hull reads what the caller may touch through this parameter, \
                 `K001` reads the cost it was given, and the range facts held after the \
                 call are the callee's -- a value of another shape arriving here makes \
                 each of them a statement about something that is not there",
            )
            .mit_notiz(
                "the next stage is not the answer: `cc` catches most of these, and a \
                 checker that reports a clean file over C that will not compile has put \
                 its trust base one stage too late",
            ),
        );
        true
    }

    fn passt(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        // **The SHAPE runs before everything else, and it is the one question `passt` never
        // asked** (`M139`, 2026-09-02). Everything below this line compares ranges, widths
        // and contracts; where a shape has none, the comparison used to end in
        // `let (Some(q), Some(z)) = (quelle.bereich(), ziel.bereich()) else { return; }` --
        // *a silent `else`, and a pointer has no range.*
        if self.gestalt_passt(quelle, ziel, span, was) {
            return;
        }
        // **The function pointer comparison runs FIRST and returns** -- the rules below are
        // about ranges and widths, and a function pointer has neither.
        if let (Typ::FnPtr(q), Typ::FnPtr(z)) = (quelle.durchgreifen(), ziel.durchgreifen()) {
            let (q, z) = (q.clone(), z.clone());
            self.fnptr_passt(&q, &z, span);
            // **`M141` runs BESIDE `M128` and not instead of it** -- the contract and the
            // signature are two independent ways to be wrong, and a pointer can be both.
            self.fnptr_signatur_passt(&q, &z, span);
            // **Lane 177: the LOGIC refinement is counted, never decided.** Where a NAMED
            // function `&f` flows into the slot, the implication `requires_slot ⇒
            // requires_f` and `ensures_f ⇒ ensures_slot` is the user's logic: it stands
            // in `gabbro obligations` (kind `C`) and as a hint here. Effects, costs,
            // arity and signature are DECIDED above (`M128`/`M142`) -- this arm decides
            // nothing about logic. Where the producer is unknown (a slot behind a
            // slot) there is no one to owe it, and the question is the slot-subtyping
            // one this lane leaves open.
            self.zeigerverfeinerung_ernten(&q, &z, span);
            return;
        }
        self.undurchsichtigkeit_pruefen(quelle, ziel, span, was);
        self.wahrheit_ist_keine_zahl(quelle, ziel, span, was);
        // **«F»: die zwei Bits, und sie sind der Abnehmer der Faktenmaschine.**
        //
        // Ohne diese Zeilen waere `Fakt::Endlich` gebaut und von nichts gelesen -- genau die
        // Klasse, gegen die `pruefe-klauseln.py` steht. *Ein Typ mit einem GENANNTEN Bereich
        // schliesst NaN aus; ein blankes `f64` nicht.*
        // Neutypen durchgreifen: `type Anteil = f64 in 0.0 .. 1.0` traegt dieselbe Zusage
        // wie die ausgeschriebene Form. *Sonst haenge die Regel daran, ob jemand dem Typ
        // einen Namen gegeben hat.*
        if let (Typ::Gleitkomma(q), Typ::Gleitkomma(z)) =
            (quelle.durchgreifen(), ziel.durchgreifen())
        {
            let mut fehlt = Vec::new();
            if q.kann_nan && !z.kann_nan {
                fehlt.push("NaN");
            }
            if q.kann_unendlich && !z.kann_unendlich {
                fehlt.push("infinity");
            }
            // **`F002` an der VERSCHMAELERUNG.** Ein Literal, das in `f64` exakt liegt,
            // muss es in `f32` nicht -- und `FBereich::mantisse()` stand dafuer da und wurde
            // von niemandem gelesen. *Dieselbe Klasse wie die siebzehn ZUSAGEN, in meinem
            // eigenen Code, einen Tag alt.*
            if q.literal
                && !q.gerundet
                && !crate::typen::FBereich::passt_in_mantisse(q.lo, z.breite)
            {
                self.absagen.schiebe(
                    Absage::fehler(
                        "F002",
                        span,
                        format!(
                            "the literal is not exact in `f{}` (it is in `f64`)",
                            z.breite
                        ),
                    )
                    .mit_notiz(
                        "`f32` carries 24 mantissa bits, `f64` carries 53 -- write \
                            `rounded` if the rounding is meant",
                    ),
                );
            }
            // **Das INTERVALL, und ohne es waere der genannte Bereich eine Behauptung, die
            // nie eingeloest wird.** Schweigen ist unvollstaendig; eine ungepruefte Zusage
            // ist falsch -- und `2.5` ist endlich, liegt aber nicht in `0.0 .. 1.0`.
            if q.lo < z.lo || q.hi > z.hi {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M101",
                        span,
                        format!(
                            "{was} requires `{}`, the value has `{}`",
                            Typ::Gleitkomma(*z).text(),
                            Typ::Gleitkomma(*q).text()
                        ),
                    )
                    .mit_notiz(
                        "`narrow <place> to <lo> .. <hi> else { … }` narrows the range \
                            and names the exit",
                    ),
                );
            }
            if !fehlt.is_empty() {
                self.absagen.schiebe(
                    Absage::fehler(
                        "F001",
                        span,
                        format!(
                            "{was} admits no {}, and the value may be one",
                            fehlt.join(" and no ")
                        ),
                    )
                    .mit_notiz(
                        "`narrow <place> to finite else { … }` establishes both at once",
                    )
                    .mit_notiz(
                        "without the fact even the negation of a comparison yields \
                            nothing -- over floating point `!(x < y)` does not follow `x >= \
                            y`",
                    ),
                );
            }
            return;
        }
        let (Some(q), Some(z)) = (quelle.bereich(), ziel.bereich()) else {
            return;
        };
        if q.passt_in(&z) {
            return;
        }
        let mut a = Absage::fehler(
            "M101",
            span,
            format!(
                "{was} requires `{}`, the value has `{}`",
                z.text(),
                q.text()
            ),
        )
        .mit_notiz(
            "M1: every operation must stay inside the range of its result type -- that is \
                a compile error, not a runtime check",
        );
        if q.min < z.min || q.max > z.max {
            a = a.mit_notiz(format!(
                "what is missing is the proof that the value lies in {} .. {}; a check \
                    before it narrows the range (V1/V2), otherwise `narrow … to … else {{ … }}`",
                z.min, z.max
            ));
        }
        self.absagen.schiebe(a);
    }

    fn ueberlauf(&mut self, span: Span, a: &IntBereich, b: &IntBereich, wort: &str, ort: &Ort) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{}` {wort} leaves the range: `{}` against `{}`",
                    ort.text(),
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "the overflow is a compile error, not a runtime check",
            )
            .mit_notiz(
                "a check before it narrows the range (V1), a relation between two places \
                    carries too (V2)",
            ),
        );
    }

    /// **PLAN-BITS section 4 (lane 88): the overflow operators.**
    ///
    /// Wrapping (`+%`, `-%`, `*%`, `<<%`) lives only on an exact unsigned range
    /// `0 .. 2^N - 1` and answers that range; saturating (`+|`) lives on one
    /// shared integer range and answers it, clamped. Neither ever takes the
    /// `M104` width path -- a wrap is defined modulo 2^N and a clamp fits its
    /// interval by construction. What fails here is exactness (`M153`) or
    /// sharedness (`M154`), never width.
    ///
    /// A literal operand has no range of its own: it takes the other's exact
    /// range when its value lies in it (the `M153`/`M154` sentences say so).
    /// Two literals wrap in their common width and saturate to their exact sum.
    fn wrapping_or_saturating(
        &mut self,
        op: BinOp,
        ba: &IntBereich,
        bb: &IntBereich,
        span: Span,
    ) -> Typ {
        if op == BinOp::PlusSat {
            return self.saturating(ba, bb, span);
        }
        if op == BinOp::SchiebLinksWrap {
            return self.wrapping_shift(ba, bb, span);
        }
        let Some((width, signed)) = typen::gemeinsame_form(ba, bb) else {
            return Typ::Unbekannt;
        };
        if signed {
            self.wrapping_refused(span, ba, bb, op_zeichen(op));
            return Typ::Unbekannt;
        }
        let na = if ba.literal {
            None
        } else {
            typen::exact_wrap_n(ba)
        };
        let nb = if bb.literal {
            None
        } else {
            typen::exact_wrap_n(bb)
        };
        let n = match (na, nb) {
            (Some(x), Some(y)) if x == y => x,
            (Some(x), None)
                if bb.literal && bb.min >= 0 && bb.max <= ((1i128 << x) - 1) =>
            {
                x
            }
            (None, Some(y))
                if ba.literal && ba.min >= 0 && ba.max <= ((1i128 << y) - 1) =>
            {
                y
            }
            // Two literals: no declared range anywhere, so the common width is
            // the modulus -- both values have to lie in it.
            (None, None)
                if ba.literal
                    && bb.literal
                    && ba.min >= 0
                    && bb.min >= 0
                    && ba.max <= ((1i128 << width) - 1)
                    && bb.max <= ((1i128 << width) - 1) =>
            {
                width as u32
            }
            _ => {
                self.wrapping_refused(span, ba, bb, op_zeichen(op));
                return Typ::Unbekannt;
            }
        };
        if n == 0 || n as u8 > width {
            self.wrapping_refused(span, ba, bb, op_zeichen(op));
            return Typ::Unbekannt;
        }
        Typ::Ganzzahl(IntBereich::genau(width, false, 0, (1i128 << n) - 1))
    }

    /// Wrapping dynamic left shift: the value side is exact unsigned, the amount
    /// side only has to lie below the bit count -- like `schiebe_links`, but
    /// against `N` instead of the storage width (PLAN-BITS section 2: the amount
    /// is in the type; `Zahl.shlW` takes it as `Zahl 0 w`).
    fn wrapping_shift(&mut self, ba: &IntBereich, bb: &IntBereich, span: Span) -> Typ {
        let n = if ba.literal {
            let (width, signed) = (ba.breite, ba.vorzeichen);
            if signed || ba.min < 0 || ba.max > ((1i128 << width) - 1) {
                self.wrapping_refused(span, ba, bb, op_zeichen(BinOp::SchiebLinksWrap));
                return Typ::Unbekannt;
            }
            width as u32
        } else {
            match typen::exact_wrap_n(ba) {
                Some(n) if !ba.vorzeichen && n as u8 <= ba.breite => n,
                _ => {
                    self.wrapping_refused(span, ba, bb, op_zeichen(BinOp::SchiebLinksWrap));
                    return Typ::Unbekannt;
                }
            }
        };
        if bb.min < 0 || bb.max >= n as i128 {
            // The amount leaves `0 .. N-1`: the same width refusal a plain shift
            // gets from `schiebe_links`, at the operation and not at the use.
            self.ueberlauf_ausdruck(span, ba, bb, op_zeichen(BinOp::SchiebLinksWrap));
        }
        Typ::Ganzzahl(IntBereich::genau(ba.breite, false, 0, (1i128 << n) - 1))
    }

    /// Saturating addition: one shared integer range in, the same range clamped
    /// out. Signed or unsigned, any interval -- the clamp is what makes it total.
    fn saturating(&mut self, ba: &IntBereich, bb: &IntBereich, span: Span) -> Typ {
        let Some((width, signed)) = typen::gemeinsame_form(ba, bb) else {
            return Typ::Unbekannt;
        };
        let (lo, hi) = match (ba.literal, bb.literal) {
            (true, true) => match ba.min.checked_add(bb.min) {
                Some(s) if ba.min == ba.max && bb.min == bb.max => (s, s),
                _ => return Typ::Unbekannt,
            },
            (true, false) => (bb.min, bb.max),
            (false, true) => (ba.min, ba.max),
            (false, false) => {
                if ba.min != bb.min || ba.max != bb.max {
                    self.saturation_refused(span, ba, bb);
                    return Typ::Unbekannt;
                }
                (ba.min, ba.max)
            }
        };
        let out = IntBereich::genau(width, signed, lo, hi);
        if !out.passt_in_die_breite() {
            // Only the two-literals corner reaches here with a range of its own
            // making: a declared range that already leaves its width falls at
            // its declaration, long before this operation reads it.
            self.ueberlauf_ausdruck(span, ba, bb, op_zeichen(BinOp::PlusSat));
        }
        Typ::Ganzzahl(out)
    }

    /// **`M153` -- wrapping needs a power-of-two range.**
    fn wrapping_refused(&mut self, span: Span, a: &IntBereich, b: &IntBereich, zeichen: &str) {
        let mut absage = Absage::fehler(
            "M153",
            span,
            format!(
                "wrapping `{zeichen}` needs both sides on an exact unsigned range \
                 `0 .. 2^N - 1`, found `{}` and `{}`",
                a.text(),
                b.text()
            ),
        );
        if a.vorzeichen || b.vorzeichen {
            absage = absage.mit_notiz(
                "wrapping is unsigned-only: signed overflow is undefined in C, \
                 and the conversion back from unsigned is implementation-defined \
                 (PLAN-BITS.md section 5b)",
            );
        } else {
            absage = absage.mit_notiz(
                "on a range like `0 .. 5` wrapping is ambiguous (mod 6 costs a \
                 division per operation), so it is not derivable there \
                 (PLAN-BITS.md section 4)",
            );
        }
        absage = absage.mit_notiz(
            "saturating `+|` clamps into the shared range instead and works on \
             every integer range",
        );
        self.absagen.schiebe(absage);
    }

    /// **`M154` -- saturating needs one shared range.**
    fn saturation_refused(&mut self, span: Span, a: &IntBereich, b: &IntBereich) {
        self.absagen.schiebe(
            Absage::fehler(
                "M154",
                span,
                format!(
                    "saturating `+|` needs one shared integer range to clamp into, \
                     found `{}` and `{}`",
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "narrow both sides to one range first (`narrow … to … else { … }`); \
                 a literal takes the other's range",
            ),
        );
    }

    fn ueberlauf_ausdruck(&mut self, span: Span, a: &IntBereich, b: &IntBereich, zeichen: &str) {
        self.absagen.schiebe(
            Absage::fehler(
                "M104",
                span,
                format!(
                    "`{} {zeichen} {}` leaves the width of the result type",
                    a.text(),
                    b.text()
                ),
            )
            .mit_notiz(
                "SYNTAX.md §4: if the result range does not fit, it is a compile error \
                    and not a wrap-around",
            )
            // **«B3» hint 4.** The measured session read this refusal, changed the RETURN
            // type from `u32` to `u64`, and got the same refusal back -- because the width
            // that is left is the width of the OPERANDS, and a wider return type does not
            // widen them. *A message that names the fault without naming where it lives
            // sends the reader to the wrong line, and that cost one whole attempt.*
            .mit_notiz(
                "the width that is left is the OPERANDS' -- a wider RETURN type does not \
                    widen them",
            )
            // The ways out are the ones measured green on 2026-09-01, in the order to try
            // them. **The third one is only a way out while a wider type exists**: at 64
            // bits there is none, and offering it there would be advice that cannot be
            // followed.
            .mit_notiz(wege_aus_der_breite(a, b)),
        );
    }

    /// **Zeigt eine Tatsache diesen Index unter der Hinterlegung?**
    ///
    /// Gesucht wird `Fakt::Beziehung` mit `<index> < <hinterlegung>`. *Ein Schreiben auf die
    /// Hinterlegung loescht diese Tatsache automatisch* (dieselbe Regel wie fuer jeden
    /// anderen Fakt) -- damit ist ein SCHRUMPFEN sicher, ohne dass eine Monotonieregel
    /// noetig waere. **Die Gefahr war nie das Wachsen.**
    fn unter_hinterlegung(&mut self, idx: &Expr, k: &str, lage: &Lage) -> bool {
        let ExprArt::Ort(o) = &idx.art else {
            // Ein Literal ist genau dann sicher, wenn es unter der Hinterlegung liegt -- und
            // die ist ein Wert, also weiss der Pruefer es nicht. *Er weigert sich.*
            return false;
        };
        let Some((schluessel, _)) = schluessel_und_indizes(o) else {
            return false;
        };
        lage.fakten.iter().any(|f| match f {
            Fakt::Beziehung {
                links,
                op,
                rechts,
                ..
            } => *links == schluessel && *op == BinOp::Kleiner && rechts == k,
            _ => false,
        })
    }

    /// **`ensures` wird gelesen -- seit 2026-08-18, und vorher von niemandem.**
    ///
    /// Gemessen: vier unsinnige Nachbedingungen gingen still durch -- ein Name, den es nicht
    /// gibt; `result` an einer Funktion ohne Ergebnis; eine Zusage ueber Zustand, den die
    /// Funktion nicht anfasst; `old` an etwas Nichtexistentem.
    ///
    /// **Was hier NICHT geprueft wird: ob der Rumpf die Zusage einloest.** Das ist
    /// Beweisersache und bleibt es -- der Nutzer beweist seine eigene Logik. *Geprueft wird
    /// die WOHLGEFORMTHEIT, und die ist die Haelfte, die eine Maschine haben kann.*
    ///
    /// Die dritte Regel ist die schaerfste und die einzige, die nicht bloss Buchhaltung ist:
    /// **eine Nachbedingung, die kein `result` nennt und keinen geschriebenen Ort, kann die
    /// Funktion nicht HERSTELLEN.** Sie ist dann ein `requires` oder ein `maintains` am
    /// falschen Platz.
    fn ensures_pruefen(&mut self, f: &FnDecl) {
        if f.ensures.is_empty() {
            return;
        }
        let geschrieben: Vec<String> = f
            .effects
            .as_ref()
            .map(|w| {
                w.liste
                    .iter()
                    .filter_map(|x| match &x.art {
                        WirkungArt::Schreibt(o) | WirkungArt::Veroeffentlicht(o) => {
                            Some(o.basis.text.clone())
                        }
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        for p in &f.ensures {
            let mut namen = Vec::new();
            sammle_namen_pred(p, &mut namen);
            let mut nennt_ergebnis = false;
            let mut nennt_geschriebenes = false;
            for n in &namen {
                if n == "result" {
                    nennt_ergebnis = true;
                    if f.ergebnis.is_none() {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M110",
                                p.span,
                                format!("`{}` names `result` and returns none", f.name.text),
                            )
                            .mit_notiz(
                                "a postcondition about a result that does not exist \
                                    speaks about nothing",
                            ),
                        );
                    }
                    continue;
                }
                // **`Self` nennt den TRAEGER -- und eine Funktion ist keiner.**
                //
                // `Self` steht im Korpus zwanzigmal, und jedes Mal an einem Traeger: in der
                // `invariant` einer `table` (`forall s in slots of Self`) oder an einem
                // `format` (`offset_into Self`, `lenof(Self)`). **An einer `fn` gibt es
                // nichts, worauf es zeigen koennte** -- `ensures` sitzt an einer Funktion,
                // und eine Funktion steht nie in einer `table`.
                //
                // *Deshalb ist das hier eine eigene Absage und nicht `M109`.* Bis zum
                // 2026-08-21 fiel `ensures Self.slots[0].rest <= 4096` an `M109` mit dem Satz
                // „is not declared here" -- und der schickt den Leser los, ein `Self` zu
                // erklaeren, was die Sprache nicht zulaesst. **`M120` nennt stattdessen den
                // Ort, an den die Zeile gehoert.** Die zweite Schreibweise, `lenof(Self)`,
                // fiel dabei gar nicht: sie ist ein TYP und lief durch den blinden
                // `Eingebaut`-Zweig.
                if n == "Self" {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M120",
                            p.span,
                            format!("`Self` in `ensures` of `{}` names no carrier", f.name.text),
                        )
                        .mit_notiz(
                            "`Self` is the carrier of a `table` or `format`; a function is \
                                not one -- a statement about the carrier belongs in its \
                                `invariant`, not in a postcondition",
                        ),
                    );
                    continue;
                }
                // **`&f` -- the producer of a function pointer, and its name is a FUNCTION
                // name.** It resolves in a different table from every other name here, and
                // it is neither `result` nor a written place: whatever else the
                // postcondition says, this half of it establishes nothing.
                if let Some(fnname) = n.strip_prefix('&') {
                    let bekannt = self
                        .u
                        .kandidaten_aufloesbar(&self.modul, fnname)
                        .iter()
                        .any(|k| self.u.funktionen.contains_key(k));
                    if !bekannt {
                        self.absagen.schiebe(
                            Absage::fehler(
                                "M109",
                                p.span,
                                format!("`{fnname}` in `ensures` is not declared here"),
                            )
                            .mit_notiz(
                                "`&f` makes a function into a value, so the name has to be \
                                    a function -- and this one is none",
                            )
                            .mit_notiz(
                                "a postcondition whose names do not resolve stands in the \
                                    certificate and in the library ABI -- and says nothing",
                            ),
                        );
                    }
                    continue;
                }
                if geschrieben.iter().any(|g| g == n) {
                    nennt_geschriebenes = true;
                }
                let bekannt = f.parameter.iter().any(|x| x.name.text == *n)
                    || self.u.suche_global(&self.modul, n).is_some()
                    || self.u.kandidaten_aufloesbar(&self.modul, n).iter().any(|k| {
                        self.u.typen.contains_key(k) || self.u.konstanten.contains_key(k)
                    });
                if !bekannt {
                    self.absagen.schiebe(
                        Absage::fehler(
                            "M109",
                            p.span,
                            format!("`{n}` in `ensures` is not declared here"),
                        )
                        .mit_notiz(
                            "a postcondition whose names do not resolve stands in the \
                                certificate and in the library ABI -- and says nothing",
                        ),
                    );
                }
            }
            if !nennt_ergebnis && !nennt_geschriebenes && !namen.is_empty() {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M111",
                        p.span,
                        format!(
                            "`{}` cannot establish this postcondition",
                            f.name.text
                        ),
                    )
                    .mit_notiz(
                        "it names neither `result` nor a place the function writes \
                            according to `effects` -- then it is a `requires` or a \
                            `maintains` in the wrong place",
                    ),
                );
            }
        }
    }

    /// **`maintains` bekommt seinen Leser -- P6, erster Schritt (2026-08-19).**
    ///
    /// `maintains I` an einem `impl fn` ist die kleinste wahre Form der Verfeinerungspflicht,
    /// die der Plan unter P6 fuehrt: *die Invariante `I` gilt vorher und nachher.* Sie steht
    /// seit jeher in der Grammatik, an sieben Korpusstellen -- **und kein Pass las sie.**
    ///
    /// Drei Regeln, und jede ist Wohlgeformtheit, nicht Beweis:
    ///
    /// * **`M112`** -- der genannte Name ist eine erklaerte `spec fn`. *Ein `maintains`, das
    ///   ins Leere nennt, steht im Zeugnis und in der Bibliotheks-ABI und sagt nichts.*
    /// * **`M113`** -- eine `spec fn` erhaelt nichts; sie IST die Aussage. `maintains` an
    ///   einer `spec fn` ist eine Pflicht ohne Rumpf, der sie schuldet.
    /// * **`M114`** -- die Invariante muss ueber etwas sprechen, das die Funktion ANFASST.
    ///   Erhaelt sie etwas, das die Funktion nicht schreibt, ist die Pflicht leer -- der
    ///   Rahmen gibt sie schon. *Dieselbe Linie wie `M111` bei `ensures`.*
    ///
    /// **Was hier NICHT geprueft wird: dass der Rumpf sie erhaelt.** Das ist die erzeugte
    /// Beweispflicht, und sie wird gezaehlt statt eingeloest -- `gabbro pflichten` druckt
    /// sie. *Zaehlen ist der Schritt, der die Kennzahl ueberhaupt sichtbar macht.*
    /// **`refines` gets its reader -- the HEAD FORM of P6 (2026-08-24).**
    ///
    /// `messung/VERFEINERUNG.md` measures the starting state: the form did NOT exist. `spec`
    /// and `impl` were qualifiers, no word joined them, and that is why the head form of P6
    /// had zero sites. *That was not a corpus gap but a missing production* -- and while it
    /// was missing, `refinement.rs` could produce no `W` obligation, only `K`.
    ///
    /// Three rules, and each is well-formedness, not proof:
    ///
    /// * **`M130`** -- `refines` stands only at an `impl fn`. A `spec fn` refines nothing, it
    ///   IS the specification; a `raw`/`extern`/`prim` body has none Gabbro could lower.
    /// * **`M131`** -- the named path is a declared `spec fn`. *A `refines` that names into
    ///   the void creates a proof obligation over a statement that does not exist* -- and
    ///   that is worse than no obligation, because the prover assumes it.
    /// * **`M132`** -- both sides carry the same arity. A refinement between functions of
    ///   different arity is none; the generated obligation would carry unbound variables.
    ///
    /// **What is NOT checked here: that the body REDEEMS the specification.** That is the
    /// generated refinement obligation, and it is counted rather than discharged --
    /// `gabbro pflichten` prints it, `gabbro pflichten --isabelle` writes it.
    /// *Whether the goal then CLOSES is decided by `refinement.rs`, and exactly there it
    /// shows whether a body semantics is missing.*
    fn verfeinert_pruefen(&mut self, f: &FnDecl) {
        let Some(pfad) = &f.verfeinert else {
            return;
        };
        if f.klasse != Some(FnKlasse::Impl) {
            self.absagen.schiebe(
                Absage::fehler(
                    "M130",
                    pfad.span,
                    format!("`{}` carries `refines` but is not an `impl fn`", f.name.text),
                )
                .mit_notiz(
                    "a specification refines nothing -- it IS the statement; and a body                         Gabbro never lowers has no refinement to state",
                ),
            );
            return;
        }
        let genannt = pfad.teile.last().map(|i| i.text.clone()).unwrap_or_default();
        let Some(&stellen) = self.spec_fns.get(&genannt) else {
            self.absagen.schiebe(
                Absage::fehler(
                    "M131",
                    pfad.span,
                    format!("`{genannt}` in `refines` is not a declared `spec fn`"),
                )
                .mit_notiz(
                    "a refinement obligation over a statement that does not exist is worse than none \
                     -- the prover assumes it",
                ),
            );
            return;
        };
        if stellen != f.parameter.len() {
            self.absagen.schiebe(
                Absage::fehler(
                    "M132",
                    pfad.span,
                    format!(
                        "`{}` takes {} parameter(s), the specification `{genannt}` takes {stellen}",
                        f.name.text,
                        f.parameter.len()
                    ),
                )
                .mit_notiz(
                    "a refinement between functions of different arity is none -- the generated \
                     obligation would carry unbound variables",
                ),
            );
        }
    }

    fn maintains_pruefen(&mut self, f: &FnDecl) {
        if f.maintains.is_empty() {
            return;
        }
        if f.klasse == Some(FnKlasse::Spec) {
            self.absagen.schiebe(
                Absage::fehler(
                    "M113",
                    f.maintains[0].span,
                    format!("`{}` is a `spec fn` and maintains nothing", f.name.text),
                )
                .mit_notiz(
                    "a specification IS the statement -- `maintains` on it is an \
                        obligation no body owes",
                ),
            );
            return;
        }
        let geschrieben: Vec<String> = f
            .effects
            .as_ref()
            .map(|w| {
                w.liste
                    .iter()
                    .filter_map(|x| match &x.art {
                        WirkungArt::Schreibt(o) | WirkungArt::Veroeffentlicht(o) => {
                            Some(o.basis.text.clone())
                        }
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        for i in &f.maintains {
            if !self.spezifikationen.contains_key(&i.text) {
                self.absagen.schiebe(
                    Absage::fehler(
                        "M112",
                        i.span,
                        format!("`{}` in `maintains` is neither a `spec fn` nor a declared invariant", i.text),
                    )
                    .mit_notiz(
                        "a maintained invariant whose name does not resolve stands in the \
                            certificate and in the library ABI -- and says nothing",
                    ),
                );
                continue;
            }
            // **`M114`:** schreibt die Funktion ueberhaupt etwas? Wenn nicht, ist die
            // Erhaltung vom Rahmen geschenkt und die Pflicht leer.
            if geschrieben.is_empty() {
                self.absagen.schiebe(
                    Absage::hinweis(
                        "M114",
                        i.span,
                        format!(
                            "`{}` maintains `{}` and writes nothing",
                            f.name.text, i.text
                        ),
                    )
                    .mit_notiz(
                        "what writes nothing maintains every invariant -- the frame gives \
                            it already, and the line promises more than it says",
                    ),
                );
            }
        }
    }

    /// **Die relationale Nachbedingung eines Rufs (Punkt 4, zweite Haelfte).**
    ///
    /// `ensures result <= s.len` an der Deklaration nennt den **Parameter** `s`; der Rufer
    /// schreibt `unberuehrt(x)`. Uebersetzt wird der Ort: `s.len` -> `x.len`.
    ///
    /// **Gedeckt ist die einfache Form** -- `result <op> <ort>`, wobei `<ort>` an einem
    /// Parameter haengt und das zugehoerige Argument selbst ein schlichter Ort ist. *Ein
    /// Argument, das gerechnet wird (`f(a + 1)`), hat keinen Ort, und dann schweigt die
    /// Regel* -- W10.
    ///
    /// **Und dies ist die ZWEITE Stelle, an der ein fremder Vertrag zu einer Tatsache wird**
    /// (2026-08-21). Sie steht deshalb ebenso im Zeugnis wie die Bereichsverengung; *eine
    /// Flaeche, von der nur eine Haelfte gebucht ist, sieht kleiner aus als sie ist.*
    /// **Wirksam heisst hier: eine Tatsache ist ENTSTANDEN.** Ob sie irgendwo gebraucht wird,
    /// entscheidet dieser Pass nicht -- die Zahl ist in dieser Richtung eine OBERE Schranke,
    /// und sie steht als solche in `messung/FREMDVERENGUNG.md`.
    fn beziehung_aus_ensures(&mut self, binder: &str, r: &Ruf, lage: &mut Lage) {
        let Some(sig) = r.path().and_then(|p| self.u.funktion(&self.modul, p)).cloned() else { return };
        for p in &sig.ensures {
            let PredArt::Vergleich(e) = &p.art else { continue };
            let ExprArt::Binaer(op, a, c) = &e.art else { continue };
            let (op, ort) = match (&a.art, &c.art) {
                (ExprArt::Ergebnis, ExprArt::Ort(o)) => (*op, o),
                (ExprArt::Ort(o), ExprArt::Ergebnis) => (gespiegelt(*op), o),
                _ => continue,
            };
            // Welcher Parameter ist die Wurzel des genannten Orts?
            let Some(i) = sig.parameter.iter().position(|(n, _)| *n == ort.basis.text) else {
                continue;
            };
            let Some(arg) = r.argumente.get(i) else { continue };
            let ExprArt::Ort(argort) = &arg.art else { continue };
            if !argort.suffixe.is_empty() {
                continue;
            }
            // `s.len` am Vertrag wird `x.len` beim Rufer.
            let mut ziel = argort.clone();
            ziel.suffixe = ort.suffixe.clone();
            let (Some((links, _)), Some((rechts, indizes))) = (
                schluessel_und_indizes(&Ort {
                    basis: gabbro_syntax::ast::Ident { text: binder.to_string(), span: r.span },
                    suffixe: Vec::new(),
                    span: r.span,
                }),
                schluessel_und_indizes(&ziel),
            ) else {
                continue;
            };
            if !sig.rumpf_da {
                self.fremd.push(Stelle {
                    rufer: self.rufer.clone(),
                    gerufener: r.target_text(),
                    span: r.span,
                    klausel: format!("result {} {}", zeichen(op), ort.text()),
                    wirkung: Wirkung::Beziehung,
                });
            }
            lage.fakten.push(Fakt::Beziehung { links, op, rechts, indizes });
        }
    }

    /// **The traversal counter gets the type it provably has** (2026-09-07).
    ///
    /// Until today this line read `insert(t.variable.text.clone(), Typ::Unbekannt)`, and it
    /// was the largest single source of untyped expressions in the clean corpus: **24 of
    /// 84** (`messung/KLEMPNEREI-2026-09-07.md` §5). *A user who writes `index into T` on a
    /// parameter gets the bound; the binder that has the same bound by construction got
    /// nothing.*
    ///
    /// **And `Unbekannt` was not silence, it was an acquittal.** Measured on
    /// `table Q count 8`:
    ///
    /// ```gabbro
    /// traverse i over slots of w by unvisited touches writes w.slots {
    ///     w.slots[i + 1000000].aktiv = true;      -- 0 errors, and the C is WRITTEN
    /// }
    /// ```
    ///
    /// `gabbro pruefe` said `0 errors, 0 hints`; `gabbro emit` returned 0 and wrote
    /// `w->slots[i + 1000000].aktiv = true;` over a `Q_slot slots[8]`. **Both nets passed an
    /// out-of-bounds write**, because `M103` asks the index for its type first and says
    /// nothing when there is none -- the shape `m1::name_aufloesen` already had written down
    /// for an undeclared name: *"every range rule silently steps aside where the type is
    /// missing -- including the index bound."*
    ///
    /// ## The procedure, and why it is not a guess
    ///
    /// `binder_tabelle` names the table for the three domains whose counter is a slot index;
    /// `Umgebung::indextyp` builds **the same type `index into T` a human would have
    /// written**, from the same `count N`, through the same code. Two readers of one
    /// declaration is what this folder pays for; there is one.
    ///
    /// **Where it cannot prove, it says nothing and the old `Unbekannt` stands** -- and a
    /// table without a `count`. *W10: a bound that is not proved is not narrowed, and the
    /// loss is a refusal that does not fall, never an acceptance that does not hold.*
    ///
    /// ## `elems of` -- the fourth traversal domain, closed 2026-09-08
    ///
    /// `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §2.4 booked the binder without a type
    /// at four domains; 2026-09-07 closed three of them through `binder_tabelle`, and
    /// **`elems of` stayed open because `binder_tabelle` returns `None` for it** -- it
    /// resolves a TABLE, and an array field is not one.
    ///
    /// > **And the folder's own prose said the binder was an element.** `binder_tabelle`'s
    /// > doc reads *"`queue` and `elems of` bind an ELEMENT, not an index -- a different
    /// > type entirely"*. **Three channels say otherwise, and they are the ones that run:**
    /// > `domaene::Binderart` books it as `Feldindex` (*"an index into the array field it
    /// > runs over"*), `emit.rs` writes `for (uint64_t i = 0; i < sizeof(f)/sizeof(f[0]);
    /// > i++)`, and `lean.rs::domain_of` calls it *"the index domain of the array's
    /// > pseudo-table … the binder is the index, as every use in the corpus reads it"*.
    /// > *A comment that contradicts the emitter is the `W16` shape in prose: it reads like
    /// > a decision and it is a stale one.* The bound built here follows the emitter.
    ///
    /// The length is not computed a second time either: `Sicht::domaenenschranke` has read
    /// `Typ::Feld { laenge }` for this domain since 2026-08-19 -- **for the COST pass**, and
    /// nobody ever turned it into a type. *One declaration, one reader, as at `indextyp`.*
    ///
    /// The type is a plain `u64 in 0 ..= n-1` and not an `index into T`: there is no table
    /// to name, and a name that resolves to nothing would be worse than none.
    fn binder_typ(&mut self, t: &Traverse, lage: &Lage) -> Typ {
        let sicht = crate::domaene::Sicht {
            u: self.u,
            modul: &self.modul,
            lokal: &lage.lokal,
        };
        if let Some(tabelle) = sicht.binder_tabelle(&t.domaene) {
            return self.u.indextyp(&self.modul, &tabelle, false);
        }
        if matches!(t.domaene, Domaene::ElementeVon(_)) {
            if let Some(n) = sicht.domaenenschranke(&t.domaene) {
                if n > 0 {
                    return Typ::Ganzzahl(IntBereich::genau(64, false, 0, n - 1));
                }
            }
        }
        Typ::Unbekannt
    }

    /// **«H2.1» -- ein Traversierungszaehler erbt die Schranke seiner Domaene (2026-08-19).**
    ///
    /// Zwei Fundstellen im ganzen Korpus, dieselbe Form:
    ///
    /// ```gabbro
    /// let mut n : u32 in 0 .. NSLOTS = 0;
    /// traverse i over slots of w by unvisited {
    ///     narrow n to 0 ..< NSLOTS else { return n; }   -- der else-Zweig kann NICHT
    ///     n += 1;                                       -- genommen werden
    /// }
    /// ```
    ///
    /// *Die Schranke faellt aus der Domaene -- aber M1 sah sie nicht, weil der Zaehler eine
    /// gewoehnliche lokale Variable ist.* Die `narrow`-Zeile ist damit die letzte
    /// handbewiesene Bereichspflicht des Korpus, und ihr `else` ist ein Ritual.
    ///
    /// ## Die Rechnung
    ///
    /// ```text
    /// c = obere Schranke von `n` beim Betreten (aus der Bindung, V1)
    /// B = Domaenenschranke                     (`domaene::Sicht`, DIESELBE wie kosten.rs)
    /// k = der konstante Zuwachs
    /// -----------------------------------------------------------------------------
    /// an der Zuwachsstelle:  n <= c + (B - 1) * k
    /// ```
    ///
    /// **Die `B - 1` ist die schaerfere und die richtige:** vor dem k-ten Zuwachs sind
    /// hoechstens k-1 geschehen. Genau sie macht die `narrow`-Zeile ueberfluessig.
    ///
    /// ## Und es ist die einzige Ausnahme von `SPRACHE.md`:657
    ///
    /// > *„Loops carry no facts inward."*
    ///
    /// **Der Unterschied zwischen Ausnahme und Loch liegt in der Richtung.** Nichts, was VOR
    /// der Schleife galt, gilt darin weiter -- die Regel ist unangetastet. Neu ist eine
    /// Tatsache, die die Schleife aus ihrer EIGENEN Form erzeugt: Domaenenschranke plus
    /// Zuwachsform. *Es ist die Induktionsvariable, und sie ist die eine Stelle, an der die
    /// Schleife etwas weiss, das eine Faktenmenge nicht hineintragen kann.*
    ///
    /// ## Fuenf Bedingungen, und jede ist ein Schweigen, wenn sie fehlt
    ///
    /// Der Zaehler ist lokal und skalar · im Rumpf **genau eine** Zuwachsstelle der Form
    /// `n += k` mit konstantem `k > 0` · die Domaene hat eine Schranke · die Traversierung
    /// liegt in keiner weiteren Schleife · niemand nimmt seine Adresse (in Gabbro geschenkt).
    ///
    /// **Faellt eine, sagt der Pass nichts** -- W10, und die `narrow`-Zeile bleibt noetig.
    fn zaehler_erbt_die_schranke(&mut self, t: &Traverse, aussen: &Lage, innen: &mut Lage) {
        let Some(b) = (crate::domaene::Sicht {
            u: self.u,
            modul: &self.modul,
            lokal: &aussen.lokal,
        })
        .domaenenschranke(&t.domaene) else {
            return;
        };
        if b <= 0 {
            return;
        }
        // **Bedingung 4: keine verschachtelte Schleife.** Sonst multipliziert sich `B`, und
        // eine Schranke, die zu klein ist, waere schlimmer als keine.
        if enthaelt_schleife(&t.rumpf) {
            return;
        }
        for (name, k) in zuwaechse(&t.rumpf) {
            // Bedingung 1: lokal und skalar.
            let Some(typ) = innen.lokal.get(&name).cloned() else { continue };
            let Some(dekl) = typ.bereich() else { continue };
            let ort = Ort {
                basis: gabbro_syntax::ast::Ident { text: name.clone(), span: t.span },
                suffixe: Vec::new(),
                span: t.span,
            };
            // `c` -- was der Zaehler beim Betreten hoechstens ist. Ohne die Tatsache aus der
            // Bindung waere das der deklarierte Hoechstwert, und die Rechnung nutzlos.
            let Some(c) = self.mit_fakt(&ort, typ.clone(), aussen).bereich().map(|x| x.max) else {
                continue;
            };
            if c >= dekl.max {
                continue;
            }
            let obergrenze = c.saturating_add((b - 1).saturating_mul(k));
            if obergrenze >= dekl.max {
                continue;
            }
            innen.fakten.push(Fakt::Bereich {
                schluessel: name,
                indizes: Vec::new(),
                min: dekl.min,
                max: obergrenze,
            });
        }
    }

    /// M4 an der Stelle, an der M1 die Zahl hat: ein Index gegen die Laenge seines Feldes.
    /// **`M119` — ein Name, den niemand deklariert** (Rezension 2026-08-20).
    ///
    /// `namen.rs` prüft DEKLARATIONEN. Eine BENUTZUNG löste niemand auf, und M1 überspringt
    /// still, was es nicht typisieren kann — mit Rückgabewert 0.
    ///
    /// ```gabbro
    /// impl fn liest(t : ptr<normal, r> T, i : u32 in 0 .. 127) -> u32 {
    ///     return t.slots[j].x;        -- `j` gibt es nicht
    /// }                               -- 0 Fehler
    /// ```
    ///
    /// **Der Schaden ist genau messbar:** dieselbe Zeile mit `i` gibt `M103` — der Index
    /// verlässt die Tabelle. *Ein Tippfehler schaltet die Indexprüfung ab, die
    /// Vorzeigeklasse dieses Ordners.* Und der Erzeuger schreibt den Namen ins C.
    ///
    /// > Eine Deckungsquote, die einen unbekannten Namen gar nicht erst zählt, misst nicht
    /// > die Deckung, sondern das Gesehene.
    fn name_aufloesen(&mut self, o: &Ort, lage: &Lage) {
        let n = &o.basis.text;
        // **Ein QUALIFIZIERTER Name hat keine Basis, die man nachschlagen koennte.**
        // `u64::max` ist ein Ort, dessen Basis das TYPWORT `u64` ist -- gefunden sofort an
        // `beispiele/11-grammatikbefunde.gab`. *Ein Namensauflöser, der Typwörter für
        // Variablen hält, ist schlimmer als keiner.*
        //
        // **`|| breite_wort(n)` stood beside it and fell on 2026-09-05.** It covered the
        // UNqualified case as well -- a bare `u32` as a place -- and that was harmless for as
        // long as the reader let no vocabulary word through at any name position: the case
        // could not arise. Since `u8 … i64`, `f32` and `f64` are ordinary names it can, and
        // then the exemption was a silent pass: `return u32;` with `u32` undeclared gave
        // **0 errors** and the generator wrote `return u32;` into the C. *An exemption whose
        // premise is taken away somewhere else does not announce itself.*
        //
        // PLAN-BITS §1: a sugared width reads as one identifier, so the sugar
        // spelling reaches this resolver as an UNqualified bare name -- and the
        // qualified `u13::max` is exempted one line up like `u64::max`. A bare
        // `u13` as a PLACE is the same defect the `breite_wort` exemption was:
        // the type rule desugars the spelling, but a place never passes through
        // it. `return u13;` with `u13` undeclared must fall here, not confirm.
        if o.text().contains("::") {
            return;
        }
        // Zweimal derselbe Ort waere zweimal dieselbe Meldung: `index_pruefen` wertet einen
        // Index fuer die Schranke aus, und die Zaehlung tut es fuer die Quote.
        if !self.schon_gemeldet.insert((o.basis.span.von, o.basis.span.bis)) {
            return;
        }
        let bekannt = lage.lokal.contains_key(n)
            || self.u.suche_global(&self.modul, n).is_some()
            || self.u.funktionen.contains_key(n)
            || self.u.tabellen.keys().any(|k| k == n || k.rsplit("::").next() == Some(n.as_str()))
            // **«E4»:** an arena is no value in `globale` (a declaration name
            // is no value), but it IS a declared name -- a read `A[i]` must
            // not fall here beside the arena rules.
            || self.u.arenen.keys().any(|k| k == n || k.rsplit("::").next() == Some(n.as_str()));
        // **`|| n == "result"` stood here and fell on 2026-09-05, for the same reason as
        // `breite_wort` above.** The return value used to be a NODE of its own
        // (`ExprArt::Ergebnis`) that no place could ever be, so a place literally named
        // `result` was unreachable and the exemption cost nothing. It is reachable now --
        // `result` is a word only inside a contract -- and the exemption made
        // `return result;` in a body **0 errors** with `return result;` emitted into C.
        // `beispiele/gift/684` holds the line.
        if !bekannt {
            self.absagen.schiebe(
                Absage::fehler("M119", o.basis.span, format!("`{n}` is declared nowhere"))
                    .mit_notiz(
                        "an unknown name has no type, and every range rule silently steps \
                         aside where the type is missing -- including the index bound",
                    ),
            );
        }
    }

    /// **«E4» -- `N214`: an index is typed by its arena.**
    ///
    /// Three faces, one rule. A place whose basis is an unshadowed arena is
    /// exactly `A[i]`: (1) any other shape -- a bare `A`, a field, a second
    /// index -- names no readable slot; (2) `i` has type `index into A`,
    /// the name this pass bound at the `alloc`. The generation question
    /// belongs to `arena.rs` (`N211`); the unknown bare name to `M119`.
    /// Returns whether the basis is an unshadowed arena at all.
    fn arena_ort(&mut self, o: &Ort, lage: &Lage) -> bool {
        if lage.lokal.contains_key(&o.basis.text) {
            return false;
        }
        let Some(q) = self.u.nennt_arena(&self.modul, &o.basis.text) else {
            return false;
        };
        let kurz = crate::umgebung::kurzname(&q);
        if o.suffixe.len() != 1 || !matches!(o.suffixe.first(), Some(OrtSuffix::Index(_))) {
            self.absagen.schiebe(
                Absage::fehler(
                    "N214",
                    o.span,
                    format!(
                        "`{}` names no slot: a place over the arena `{}` is \
                         exactly `{}[i]`",
                        o.text(),
                        o.basis.text,
                        o.basis.text
                    ),
                )
                .mit_notiz(
                    "an arena is no value -- only a slot of it can be read, \
                     and only through its index",
                ),
            );
            return true;
        }
        if let Some(OrtSuffix::Index(idx)) = o.suffixe.first() {
            let it = self.ausdruck_roh(idx, lage);
            let erwartet = format!("index into {kurz}");
            let traegt = matches!(&it, Typ::Benannt { name, .. } if name == &erwartet);
            if !traegt {
                self.absagen.schiebe(
                    Absage::fehler(
                        "N214",
                        idx.span,
                        format!(
                            "this index is no index into `{}`: an index is \
                             typed by its arena, and only `alloc` out of `{}` \
                             binds one",
                            o.basis.text, o.basis.text
                        ),
                    )
                    .mit_notiz(
                        "a number in range is not enough -- after a `reset` \
                         the same number names another lifetime of the slot, \
                         and the generation travels with the bound name",
                    ),
                );
            }
        }
        true
    }

    /// **«E4» -- `N214`, third face: an arena slot is written by `alloc`.**
    ///
    /// `A[i] = v`, `publishes` and `exchange` over an arena place bypass
    /// the used counter: the slot may be unallocated, and the count the
    /// reservation is held against drifts. Returns whether the target is
    /// an unshadowed arena place.
    fn arena_schreibziel(&mut self, o: &Ort, lage: &Lage) -> bool {
        if lage.lokal.contains_key(&o.basis.text) {
            return false;
        }
        if self.u.nennt_arena(&self.modul, &o.basis.text).is_none() {
            return false;
        }
        self.absagen.schiebe(
            Absage::fehler(
                "N214",
                o.span,
                format!(
                    "`{}` is written outside `alloc`: an arena slot is \
                     stored once, at allocation -- the used counter and the \
                     reservation count what `alloc` does",
                    o.text()
                ),
            )
            .mit_notiz("read the slot with `A[i]`, store it with `alloc`"),
        );
        true
    }

    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {
        // **«E4»:** an arena place is owned by `arena_ort` below -- shape,
        // index belonging, and nothing else. A local shadowing the arena
        // resolves to the local, so the rule stays silent about it.
        if self.arena_ort(o, lage) {
            return;
        }
        // **`suche` und nicht `get`, und das war ein Loch in der ERSTEN getragenen Klasse.**
        //
        // Bis zum 2026-08-17 stand hier ein direktes `get(&o.basis.text)`. Die Schluessel in
        // `globale` sind QUALIFIZIERT (`beispiel::x::Kappenraum`), also traf der Blick auf
        // `"Kappenraum"` in jedem `module`-Block ins Leere -- der Traeger wurde `Unbekannt`,
        // und `M103` sagte nichts.
        //
        // ```gabbro
        // table W count 8 { slot { a : u32, } }
        // impl fn f(i : u32 in 0 .. 300) -> u32 { return W.slots[i].a; }   -- 0 Fehler
        // ```
        //
        // > **Die Regel war gebaut, gebucht und getragen -- und traf genau die Form nicht,
        // > fuer die sie da ist:** eine Tabelle, die ueber ihren globalen Namen adressiert
        // > wird. *Das ist die Bauart von `beispiele/09-ohne-zeiger.gab`, dessen ganzer Punkt
        // > es ist, dass Kernzustand keinen Zeiger braucht.*
        //
        // Gefunden beim Bauen von `const fn`, weil eine Giftprobe nicht fiel, die fallen
        // musste (R11). *`typ_von_ort` daneben hat immer `suche` benutzt -- die zwei Blicke
        // auf dieselbe Karte gingen auseinander, und nur einer davon hatte einen Test.*
        let mut traeger = lage
            .lokal
            .get(&o.basis.text)
            .cloned()
            .or_else(|| {
                self.u
                    .suche_global(&self.modul, &o.basis.text)
                    .cloned()
            })
            .unwrap_or(Typ::Unbekannt);
        // **Welche Tabelle ist das?** Fuer `backed` gebraucht: die Hinterlegung haengt an der
        // TABELLE, nicht am Feld.
        let tabelle = match traeger.durchgreifen() {
            Typ::Tabelle(q) => Some(q.clone()),
            _ => None,
        };
        for suffix in &o.suffixe {
            match suffix {
                OrtSuffix::Index(idx) => {
                    if let Typ::Feld {
                        element,
                        laenge: Some(n),
                    } = traeger.durchgreifen()
                    {
                        let n = *n as i128;
                        let it = self.ausdruck_roh(idx, lage);
                        if let Some(b) = it.bereich() {
                            if b.max >= n || b.min < 0 {
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "M103",
                                        idx.span,
                                        format!(
                                            "the index has `{}`, the array has {n} elements",
                                            b.text()
                                        ),
                                    )
                                    .mit_notiz(
                                        "M4: no unchecked indexing -- the bound comes \
                                            from the declaration of the carrier",
                                    ),
                                );
                            }
                        }
                        // **`M108`: im Adressraum, aber nicht im Speicher.**
                        //
                        // `count N` sagt, wie viele Plaetze der Typ kennt; `backed k` nennt
                        // den Wert, bis zu dem sie hinterlegt sind. *Ein Zugriff auf einen
                        // nicht hinterlegten Platz ist typkorrekt und trotzdem ein
                        // Fehlzugriff* -- und in einem Kernel ist das besonders scharf, weil
                        // er selbst die Instanz ist, die Seiten hinterlegt.
                        //
                        // **Das Tor ist keine neue Pruefung, sondern dieselbe gegen die
                        // richtige Zahl.** Die Tatsache `i < k` ist ein Vergleich zweier
                        // Stellen, und den fuehrt M1 als `Fakt::Beziehung` seit jeher --
                        // `narrow i to 0 ..< k` und `if i < k` liefern ihn gleichermassen.
                        if let Some(k) = tabelle
                            .as_ref()
                            .and_then(|t| self.u.hinterlegungen.get(t))
                        {
                            if !self.unter_hinterlegung(idx, k, lage) {
                                self.absagen.schiebe(
                                    Absage::fehler(
                                        "M108",
                                        idx.span,
                                        format!(
                                            "the index lies inside the address space, but \
                                                nothing shows it is BACKED"
                                        ),
                                    )
                                    .mit_notiz(
                                        "`count` is the address space, `backed` the \
                                            memory -- an index into an unbacked place is \
                                            type-correct and still a fault",
                                    )
                                    .mit_notiz(
                                        "`narrow <index> to 0 ..< <backing> else { … }` \
                                            carries it too, like every other bound",
                                    ),
                                );
                            }
                        }
                        traeger = (**element).clone();
                    } else {
                        traeger = match traeger.durchgreifen() {
                            Typ::Feld { element, .. } => (**element).clone(),
                            _ => Typ::Unbekannt,
                        };
                    }
                }
                OrtSuffix::Feld(f) | OrtSuffix::Ueber(f) => {
                    // **`M134` -- a field access on a carrier that cannot carry it.**
                    //
                    // Measured 2026-08-31 through the UNCHANGED checker
                    // (`messung/ZWEI-BLINDSTELLEN.md`): `m.op` on a `u64` and
                    // `m.gibt_es_nicht` on a declared record BOTH passed with
                    // `0 errors, 0 hints`, and the emitter wrote `m->op` and
                    // `m.gibt_es_nicht` into the C. `cc` refused each.
                    //
                    // *The checker had the answer in its hands the whole time:* the run
                    // printed `M1 saw 3 expressions, 1 of them without a type` -- it COUNTED
                    // the hole and did not name it. **A coverage figure is not a refusal.**
                    match self.u.feldurteil(&traeger, &f.text) {
                        crate::umgebung::Feldurteil::KeinFeld(hat) => {
                            let mut a = Absage::fehler(
                                "M134",
                                f.span,
                                format!("`{}` is not a field of this carrier", f.text),
                            )
                            .mit_notiz(format!(
                                "the carrier is `{}`, and the lowering writes the name \
                                 straight into C",
                                traeger.text()
                            ));
                            a = if hat.is_empty() {
                                a.mit_notiz("it declares no fields at all")
                            } else {
                                a.mit_notiz(format!("it has: {}", hat.join(", ")))
                            };
                            self.absagen.schiebe(a);
                        }
                        crate::umgebung::Feldurteil::KeineFelder => {
                            self.absagen.schiebe(
                                Absage::fehler(
                                    "M134",
                                    f.span,
                                    format!(
                                        "`.{}` reads a field on something that has none",
                                        f.text
                                    ),
                                )
                                .mit_notiz(format!(
                                    "the carrier is `{}` -- a number, a truth value or a \
                                     reason carries no fields",
                                    traeger.text()
                                ))
                                .mit_notiz(
                                    "the lowering writes `->` into C, and `cc` answers \
                                     `invalid type argument of '->'`",
                                ),
                            );
                        }
                        // The carrying case is the ordinary one; `Unklar` is the honest
                        // exit -- where
                        // the carrier's type never resolved, this rule claims nothing (W10).
                        _ => {}
                    }
                    traeger = self.u.feld_von(&self.modul, &traeger, &f.text);
                }
            }
        }
    }
}

/// Der Schluessel eines Ortes -- `None`, wenn ein Index kein einfacher Ort und keine Zahl
/// ist. **Ohne Schluessel kein Fakt:** zwei verschiedene Indizes duerfen nicht denselben
/// Namen bekommen, sonst verengt eine Pruefung ueber `a[i]` auch `a[j]`.
fn schluessel_von(o: &Ort) -> Option<String> {
    schluessel_und_indizes(o).map(|(s, _)| s)
}

/// **U3.** Zum Schluessel gehoeren die Namen seiner Indizes. `buf[i]` bleibt sonst
/// derselbe Ort, waehrend `i` sich darunter wegbewegt -- ein Fakt ueber `buf[i]` ueberlebte
/// `i = 0` und verengte danach einen ganz anderen Platz.
fn schluessel_und_indizes(o: &Ort) -> Option<(String, Vec<String>)> {
    let mut s = o.basis.text.clone();
    let mut indizes = Vec::new();
    for suffix in &o.suffixe {
        match suffix {
            OrtSuffix::Feld(f) => {
                s.push('.');
                s.push_str(&f.text);
            }
            OrtSuffix::Ueber(f) => {
                s.push_str("->");
                s.push_str(&f.text);
            }
            OrtSuffix::Index(e) => match &e.art {
                ExprArt::Zahl(v) => s.push_str(&format!("[{v}]")),
                ExprArt::Ort(inner) if inner.suffixe.is_empty() => {
                    s.push_str(&format!("[{}]", inner.basis.text));
                    indizes.push(inner.basis.text.clone());
                }
                // **Ein Index mit Suffixen -- die Zeichenkettenform, 2026-08-19.**
                //
                // `s.bytes[s.len] = x` fiel bis dahin auf `None`, und `None` heisst hier
                // `lage.fakten.clear()`: **jede Tatsache des Blocks stirbt.** Damit war
                //
                // ```gabbro
                // narrow s.len to 0 ..< KAP else { return false; }
                // s.bytes[s.len] = b;
                // s.len += 1;              -- M101: der Bereich der Verengung ist fort
                // ```
                //
                // nicht schreibbar -- und das ist die gewoehnlichste Form, die es gibt:
                // *ein Puffer mit einer Laenge daneben.* Der Ordner fuehrte
                // „allgemeine Zeichenketten" darum als nicht schreibbar, und der Grund war
                // nicht die Sprache, sondern diese Zeile.
                //
                // > **Die Vergroeberung war sicher und unnoetig teuer.** Ein Schreiben auf
                // > `s.bytes[…]` trifft `s.bytes` und alles, was ueber `s.len` indiziert --
                // > nicht `s.len` selbst.
                ExprArt::Ort(inner) => {
                    let (innen, mut tiefer) = schluessel_und_indizes(inner)?;
                    s.push_str(&format!("[{innen}]"));
                    indizes.append(&mut tiefer);
                    indizes.push(innen);
                }
                _ => return None,
            },
        }
    }
    Some((s, indizes))
}

/// Beruehren sich zwei Ortsschluessel? Ein Schreiben auf `c.slots` trifft auch
/// `c.slots[i].benutzt`, und umgekehrt.
fn beruehrt(a: &str, b: &str) -> bool {
    a == b
        || a.starts_with(b) && trennt(a.as_bytes().get(b.len()).copied())
        || b.starts_with(a) && trennt(b.as_bytes().get(a.len()).copied())
}

/// A `ptr` as stored, chasing aliases but never the pointee (unlike
/// `durchgreifen`, which answers the pointee for field access).
fn ist_zeiger(t: &Typ) -> bool {
    match t {
        Typ::Zeiger(_) => true,
        Typ::Benannt { unter, .. } => ist_zeiger(unter),
        _ => false,
    }
}

/// **V4 -- a write naming this carrier expires every local tainted with it**
/// (spec §1, carrier granularity §2a -- no path overlap, syntax only; own writes
/// kill, §2b). The written name itself is rebound when bare (fresh again) and
/// stale when only a part of it was written.
fn frische_toeten_schreiben(traeger: &str, nackt: bool, lage: &mut Lage) {
    if let Some(s) = lage.frisch.remove(traeger) {
        if !nackt {
            lage.veraltet.insert(traeger.to_string(), s);
        }
    }
    if nackt {
        lage.veraltet.remove(traeger);
    }
    frische_toeten_traeger(lage, traeger);
}

/// **V4 -- expire every tainted local of this carrier, keep the rest.** Each
/// expired name keeps the taint set it died with: that set is what later tells
/// a disjoint index (excused) from a decision on the stale value (refused).
fn frische_toeten_traeger(lage: &mut Lage, traeger: &str) {
    let frisch = std::mem::take(&mut lage.frisch);
    let mut rest = HashMap::with_capacity(frisch.len());
    for (name, s) in frisch {
        if s.contains(traeger) {
            lage.veraltet.insert(name, s);
        } else {
            rest.insert(name, s);
        }
    }
    lage.frisch = rest;
}

/// **V4 -- expire every taint** (spec §2c loops, and the coarse call rule): the
/// names stay known-expired instead of going silent, each with the carriers it
/// was read from.
fn frische_alle_toeten(lage: &mut Lage) {
    for (name, s) in std::mem::take(&mut lage.frisch) {
        lage.veraltet.insert(name, s);
    }
}

fn trennt(c: Option<u8>) -> bool {
    matches!(c, Some(b'.') | Some(b'[') | Some(b'-'))
}

/// Steht irgendwo in diesem Ausdruck ein Aufruf?
/// The name of a call -- empty when it is indirect. **An empty return leads to the coarse
/// rule**, because a `fn(…)` pointer names no effect list one could read.
fn rufnamen_im_ruf(r: &Ruf) -> Vec<&Pfad> {
    r.path().map(|p| vec![p]).unwrap_or_default()
}

fn enthaelt_ruf(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Ruf(_) => true,
        ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => enthaelt_ruf(i),
        ExprArt::Binaer(_, a, b) => enthaelt_ruf(a) || enthaelt_ruf(b),
        ExprArt::Ort(o) => o.suffixe.iter().any(|sx| match sx {
            OrtSuffix::Index(i) => enthaelt_ruf(i),
            _ => false,
        }),
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Aligned(a, c) => enthaelt_ruf(a) || enthaelt_ruf(c),
            _ => false,
        },
        // **«SG-24»** -- a call inside the counted predicate runs once per entry:
        // facts die at it like at any other call (`rufe_im_ausdruck` funnels
        // through `alle_ausdruecke` and sees it for the same reason).
        ExprArt::Zaehle { rumpf, .. } => crate::ausdruecke_im_praedikat(rumpf)
            .into_iter()
            .any(enthaelt_ruf),
        // **Lane E1:** a call inside the arguments of a library call kills
        // facts like any other call.
        ExprArt::LibraryCall(r) => r.args.iter().any(enthaelt_ruf),
        _ => false,
    }
}

/// Ist dieser Ausdruck der Konstruktor `Some(…)`? **`Some` ist ein reserviertes Wort**
/// (`kw.rs`), also kann diese Frage keine benutzerdeklarierte Funktion treffen.
fn ist_some(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Ruf(r) => r.heisst("Some"),
        _ => false,
    }
}

/// **Die Nutzlast eines `option index into T`: `index into T`.**
///
/// Der Optionsbereich ist `0 ..= N`, die Nutzlast `0 ..< N` -- der Unterschied ist genau
/// der Sonderwert. *Er wird hier abgezogen und nicht neu ausgerechnet: eine zweite
/// Kapazitaetsrechnung neben `umgebung.rs` waere das zweite Register ueber derselben Sache
/// (W7).*
fn option_nutzlast(t: &Typ) -> Option<Typ> {
    let Typ::Benannt { name, heimat, undurchsichtig, unter } = t else {
        return None;
    };
    let ohne = name.strip_prefix("option ")?;
    let Typ::Ganzzahl(b) = unter.as_ref() else {
        return None;
    };
    let mut eng = *b;
    eng.max -= 1;
    Some(Typ::Benannt {
        name: ohne.to_string(),
        heimat: heimat.clone(),
        undurchsichtig: *undurchsichtig,
        unter: Box::new(Typ::Ganzzahl(eng)),
    })
}

/// **The coarse shape of a type -- the question `passt` could not ask** (`M139`).
///
/// `None` is the honest exit and it is deliberate: `Unbekannt` is what the coverage number
/// counts, and `never` inhabits nothing. *Building a refusal on either would turn the exit
/// into a false red.*
///
/// **A `Benannt` is looked THROUGH.** A range alias lowers to its carrier and is transparent
/// by construction (`N030`, 2026-08-20) -- the name is asked for again in `gestalt_grund`,
/// and only where the shape is an aggregate.
fn gestalt(t: &Typ) -> Option<&'static str> {
    match t {
        // A device register is a number whose bits have names -- at a slot it is a number.
        Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Register { .. } => Some("a number"),
        Typ::Gleitkomma(_) => Some("a floating-point number"),
        Typ::Wahrheit => Some("a truth value"),
        Typ::Zeiger(_) => Some("a pointer"),
        Typ::Verbund(_) | Typ::Verbundname(_) => Some("a record"),
        Typ::Feld { .. } => Some("an array"),
        Typ::FnPtr(_) => Some("a function pointer"),
        Typ::Summe { .. } => Some("a sum type"),
        Typ::Tabelle(_) => Some("a table"),
        Typ::Grund(_) => Some("a reason"),
        Typ::Benannt { unter, .. } => gestalt(unter),
        Typ::Nie | Typ::Unbekannt => None,
    }
}

/// The name a type CARRIES -- `None` where there is none to compare.
fn nominal(t: &Typ) -> Option<&str> {
    match t {
        Typ::Benannt { name, .. } | Typ::Summe { name, .. } => Some(name),
        Typ::Verbundname(n) | Typ::Tabelle(n) | Typ::Grund(n) => Some(n),
        _ => None,
    }
}

/// Strips the NAME and nothing else -- `durchgreifen` also strips the pointer, and here the
/// pointer is the thing being asked about.
fn ohne_namen(t: &Typ) -> &Typ {
    match t {
        Typ::Benannt { unter, .. } => ohne_namen(unter),
        anderer => anderer,
    }
}

/// **The LITERAL ZERO** -- a number whose whole range is `0 .. 0`.
///
/// It is the null pointer (`beispiele/38`: `static tz : ptr<normal, rw> Platz = 0;`) and the
/// zero-initialiser of an aggregate (`beispiele/08`, `beispiele/64`:
/// `static mut PUFFER : [u8; KAP] = 0;`). **Both forms stand in the CLEAN corpus** -- the
/// first cut of this rule refused them, and that was a language change and not a hole.
fn ist_null(t: &Typ) -> bool {
    t.bereich().is_some_and(|b| b.min == 0 && b.max == 0)
}

/// **An array decaying to a pointer to its element** -- C's array-to-pointer decay, and
/// `beispiele/64` rests on it: `write(1, PUFFER, LAENGE)` at
/// `extern fn write(…, p : ptr<normal, r> u8, …)`.
fn zerfaellt_zu(quelle: &Typ, ziel: &Typ) -> bool {
    let (Typ::Feld { element, .. }, Typ::Zeiger(z)) = (ohne_namen(quelle), ohne_namen(ziel))
    else {
        return false;
    };
    gestalt_grund(element, z).is_none()
}

/// **Why the two cannot stand at the same place -- `None` where nothing here says so.**
///
/// Three readings of one question, and the ORDER is the rule: first the shape, then -- behind
/// a pointer -- the shape of the pointee, then the NAME over an aggregate.
///
/// **And two crossings belong to OTHER rules**, measured against the corpus and not designed:
/// `bool` against a number is `M135` together with its `0 .. 1` exception
/// (`beispiele/gift/416` reads a device bit into a `bool` and MUST stay clean), and a
/// `reason` at a value position is `M124` -- structural, four doors, and
/// `beispiele/gift/293` falls there. *Two refusals at one site look like two rules, and the
/// older one's poison probe would fall green while that rule is out.*
fn gestalt_grund(quelle: &Typ, ziel: &Typ) -> Option<String> {
    let (q, z) = (gestalt(quelle)?, gestalt(ziel)?);
    if q == z {
        // **A pointer is compared at what it points AT.** `Typ::Zeiger` carries no space and
        // no rights -- those are `M3`'s (`R008`), measured and separate -- so what is left
        // here is the pointee, and that is exactly the half `cc` was answering for.
        if let (Typ::Zeiger(a), Typ::Zeiger(b)) = (ohne_namen(quelle), ohne_namen(ziel)) {
            return gestalt_grund(a, b);
        }
        // **An aggregate is NOMINAL, a scalar alias is not.** Two records are two
        // declarations even where their fields line up; `type Zaehler = u32 in 0 .. 65535`
        // is its carrier.
        let (Some(qn), Some(zn)) = (nominal(quelle), nominal(ziel)) else {
            return None;
        };
        if qn != zn && matches!(q, "a record" | "an array" | "a sum type" | "a table") {
            return Some(format!("`{qn}` and `{zn}` are two declarations, not one"));
        }
        return None;
    }
    let zahl = |g: &str| g == "a number" || g == "a floating-point number";
    // `M135` owns this crossing, WITH the `0 .. 1` exception a device flag needs.
    if (q == "a truth value" && zahl(z)) || (zahl(q) && z == "a truth value") {
        return None;
    }
    // `M124` owns the position of a reason value, structurally and at four doors.
    if q == "a reason" || z == "a reason" {
        return None;
    }
    if ist_null(quelle) && matches!(z, "a pointer" | "a record" | "an array") {
        return None;
    }
    if zerfaellt_zu(quelle, ziel) {
        return None;
    }
    Some(format!("{q} does not answer for {z}"))
}

/// **Why these two cannot be the SAME machine value -- `M141`'s per-component question.**
///
/// `gestalt_grund` above asks whether two types can stand at the same place, and at an
/// ordinary slot that is the right question: C converts, `M101`/`M104` hold the range, and
/// `u8` at a `u32` parameter is a widening nobody needs to be told about.
///
/// **Through a function pointer nothing converts.** The caller pushes what the SLOT's type
/// says and the callee reads what its OWN declaration says; there is no site in between for
/// a conversion to live. So here -- and only here -- the question is sharper: *do the two
/// lower to the same C type?* `cc` asks exactly this and answers
/// *incompatible pointer type*.
///
/// Three readings, in order: the shape (`gestalt_grund`, one home and not a second), then
/// the pointee behind a pointer and the element behind an array, then the machine word --
/// width and signedness for an integer, width for a float.
///
/// **`None` stays the honest exit.** `Unbekannt` and `never` have no shape, and neither has
/// a range -- so both loops below simply do not run. *W10: not refused is not confirmed.*
fn darstellung_grund(quelle: &Typ, ziel: &Typ) -> Option<String> {
    if let Some(g) = gestalt_grund(quelle, ziel) {
        return Some(g);
    }
    match (ohne_namen(quelle), ohne_namen(ziel)) {
        // A pointer's own lowering is the same word everywhere; what differs is the pointee.
        (Typ::Zeiger(a), Typ::Zeiger(b)) => return darstellung_grund(a, b),
        // **An array cannot be a parameter at all** (`C001`, the emitter), so this arm is
        // reached only through a pointer to one. The length is part of the C type.
        (Typ::Feld { element: a, laenge: la }, Typ::Feld { element: b, laenge: lb }) => {
            if la != lb {
                return Some(format!(
                    "`{}` and `{}` are arrays of different length",
                    quelle.text(),
                    ziel.text()
                ));
            }
            return darstellung_grund(a, b);
        }
        _ => {}
    }
    // **The machine word.** `type Zaehler = u32 in 0 .. 9` and `u32` are ONE C type and one
    // ABI -- `bereich()` looks through the name by construction (`N030`), and the declared
    // range is deliberately not compared here; see the note at `fnptr_signatur_passt`.
    if let (Some(a), Some(b)) = (quelle.bereich(), ziel.bereich()) {
        if a.breite != b.breite || a.vorzeichen != b.vorzeichen {
            return Some(format!(
                "`{}` and `{}` are different machine words",
                quelle.text(),
                ziel.text()
            ));
        }
    }
    if let (Typ::Gleitkomma(a), Typ::Gleitkomma(b)) = (ohne_namen(quelle), ohne_namen(ziel)) {
        if a.breite != b.breite {
            return Some(format!(
                "`{}` and `{}` are different machine words",
                quelle.text(),
                ziel.text()
            ));
        }
    }
    None
}

/// Nennt der Fakt diesen Namen -- als Grundname oder in einem Index?
fn nennt_namen(f: &Fakt, name: &str) -> bool {
    let trifft = |s: &str| {
        s == name
            || s.starts_with(name) && trennt(s.as_bytes().get(name.len()).copied())
            || s.split(['[', ']', '.']).any(|t| t == name)
    };
    match f {
        Fakt::Endlich { schluessel, .. }
        | Fakt::FIntervall { schluessel, .. }
        | Fakt::Bereich { schluessel, .. } => trifft(schluessel),
        Fakt::Beziehung { links, rechts, .. } => trifft(links) || trifft(rechts),
    }
}

/// Sammelt jedes Ziel, auf das ein Block schreibt -- auch in seinen Unterbloecken.
fn sammle_schreibziele(b: &Block, out: &mut Vec<Ort>) {
    for s in &b.anweisungen {
        crate::schreibziele(s, out);
    }
}

fn negiere(op: BinOp) -> BinOp {
    match op {
        BinOp::Gleich => BinOp::Ungleich,
        BinOp::Ungleich => BinOp::Gleich,
        BinOp::Kleiner => BinOp::GroesserGleich,
        BinOp::KleinerGleich => BinOp::Groesser,
        BinOp::Groesser => BinOp::KleinerGleich,
        BinOp::GroesserGleich => BinOp::Kleiner,
        anderer => anderer,
    }
}

/// `3 <= x` sagt dasselbe wie `x >= 3`.
fn spiegle(op: BinOp) -> BinOp {
    match op {
        BinOp::Kleiner => BinOp::Groesser,
        BinOp::KleinerGleich => BinOp::GroesserGleich,
        BinOp::Groesser => BinOp::Kleiner,
        BinOp::GroesserGleich => BinOp::KleinerGleich,
        anderer => anderer,
    }
}

fn op_wort(op: ZuwOp) -> &'static str {
    match op {
        ZuwOp::Plus => "+=",
        ZuwOp::Minus => "-=",
        ZuwOp::Und => "&=",
        ZuwOp::Oder => "|=",
        ZuwOp::Setzt => "=",
    }
}

fn op_zeichen(op: BinOp) -> &'static str {
    match op {
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
        // PLAN-BITS section 4 (lane 88): the overflow spellings, quoted the way
        // the source wrote them -- held to the same answer as the other two
        // tables by `op_zeichen_sagt_dasselbe_wie_fremdverengung` below.
        BinOp::PlusWrap => "+%",
        BinOp::MinusWrap => "-%",
        BinOp::MalWrap => "*%",
        BinOp::SchiebLinksWrap => "<<%",
        BinOp::PlusSat => "+|",
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        // **The comparisons stood on the `_ => "?"` arm until 2026-08-31**, and nothing read
        // them: the only caller was the overflow message, which fires in the arithmetic
        // branch alone. `M136` names an operator pair and printed `x | y ? z` for
        // `x | y == z` -- a refusal that cannot quote the line it is about.
        BinOp::Gleich => "==",
        BinOp::Ungleich => "!=",
        BinOp::Kleiner => "<",
        BinOp::KleinerGleich => "<=",
        BinOp::Groesser => ">",
        BinOp::GroesserGleich => ">=",
        // **And the last two came out of the `_` on the same day.** `||` and `&&` were the
        // only ones left in it; the arm answered `?` for them and for nothing else, so it
        // was `M136` waiting for a caller. *A branch that is silent over 499 files is not a
        // branch that is right.*
        BinOp::Oder => "||",
        BinOp::Und => "&&",
    }
}

/// Die BASISNAMEN, die ein Praedikat nennt -- ohne Feldnamen, denn die haengen am Traeger.
/// **Der INDEX war das Loch, und er ist die Haelfte der Korpusstellen.**
///
/// Bis zum 2026-08-19 sammelte diese Funktion aus einem `Ort` nur `o.basis.text` -- die
/// Suffixe blieben ungelesen, und ein Index ist ein AUSDRUCK.
///
/// ```gabbro
/// ensures forall s in slots of W : W.slots[tippfehler].a == 0
/// --> 3 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// **`M109` prueft damit genau die Namen, die niemand falsch schreibt.** Fuenf der sechzehn
/// `ensures`-Stellen des Korpus indizieren (`c.slots[s]`, `Kappenraum.slots[s]`), und in
/// keiner war der Index gelesen. *Dieselbe Bauart wie die vier blinden Walker: der Rumpf
/// wurde betreten, ein Zweig davon nicht.*
///
/// Die zweite Haelfte ist die Bindung: `forall s in …` ERKLAERT `s`, also darf `s` im Rumpf
/// nicht als unbekannt gelten. **Ohne sie waere der Absteig ein Fehlalarm** -- und ein
/// Fehlalarm an einer Regel, die den eigenen Korpus zerlegt, ist schlimmer als die Luecke.
fn sammle_namen_pred(p: &Pred, out: &mut Vec<String>) {
    sammle_namen_pred_geb(p, &mut Vec::new(), out);
}

fn sammle_namen_pred_geb(p: &Pred, gebunden: &mut Vec<String>, out: &mut Vec<String>) {
    fn aus_ort(o: &Ort, gebunden: &[String], out: &mut Vec<String>) {
        if !gebunden.iter().any(|g| *g == o.basis.text) {
            out.push(o.basis.text.clone());
        }
        // **Und hier steigt es ab.** `.feld` und `->feld` sind Namen im TYP, nicht in der
        // Umgebung; ein `[expr]` dagegen ist ein gewoehnlicher Ausdruck ueber gewoehnlichen
        // Orten -- und genau dort stand der Tippfehler, den niemand fand.
        for s in &o.suffixe {
            if let OrtSuffix::Index(e) = s {
                aus_expr(e, gebunden, out);
            }
        }
    }
    fn aus_expr(e: &Expr, gebunden: &[String], out: &mut Vec<String>) {
        match &e.art {
            ExprArt::Ort(o) => aus_ort(o, gebunden, out),
            ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => aus_expr(i, gebunden, out),
            ExprArt::Binaer(_, a, b) => {
                aus_expr(a, gebunden, out);
                aus_expr(b, gebunden, out);
            }
            ExprArt::Ruf(r) => {
                // `old(x)` ist ein Geisterausdruck; sein Argument ist ein gewoehnlicher Ort.
                for a in &r.argumente {
                    aus_expr(a, gebunden, out);
                }
            }
            ExprArt::Ergebnis => out.push("result".into()),
            // `old(x)` ist ein Geisterausdruck ueber den VORzustand -- sein Ort muss es
            // trotzdem geben. *Eine Nachbedingung ueber den alten Wert von nichts ist keine.*
            ExprArt::Alt(o) => aus_ort(o, gebunden, out),
            // **`sizeof`/`lenof`/`aligned` tragen Namen, und bis heute sah sie niemand.**
            //
            // Gemessen 2026-08-21: `ensures result <= sizeof(tippfehler)` ging mit **0
            // Fehlern** durch, ebenso `ensures aligned(tippfehler, 8)`. `ExprArt::Eingebaut`
            // fiel in den Sammelzweig darunter -- *und was der Sammler nicht betritt, prueft
            // `M109` nicht.* Dieselbe Bauart wie die vier blinden Walker: der Rumpf wurde
            // betreten, ein Zweig davon nicht.
            //
            // `aligned(a, b)` ist der teuerste der drei: **zwei ganze Ausdruecke**, beliebig
            // tief, und keiner davon war sichtbar.
            ExprArt::Eingebaut(b) => match b.as_ref() {
                Eingebaut::Sizeof(t) | Eingebaut::Lenof(t) => match t {
                    TypOderOrt::Ort(o) => aus_ort(o, gebunden, out),
                    // **`lenof(Self)` ist ein TYP, kein Ort** -- `typ_oder_ort` entscheidet
                    // das am naechsten Zeichen: `Self` allein ist ein Typ, `Self.feld` ein
                    // Ort. Beide Wege muessen bei `M120` ankommen, sonst faellt die eine
                    // Schreibweise und die andere nicht.
                    TypOderOrt::Typ(TypExpr::Pfad(p)) => {
                        if p.teile.len() == 1 && p.teile[0].text == "Self" {
                            out.push("Self".into());
                        }
                    }
                    TypOderOrt::Typ(_) => {}
                },
                Eingebaut::Aligned(a, b) => {
                    aus_expr(a, gebunden, out);
                    aus_expr(b, gebunden, out);
                }
            },
            // **`&f` names a function, and one character took the name check away**
            // (measured 2026-09-02).
            //
            // ```text
            // ensures result == tippfehler     ->  M109  `tippfehler` … is not declared here
            // ensures result == &tippfehler    ->  0 errors
            // ```
            //
            // `ExprArt::FnWert` carries a `Pfad` and no sub-expression, so it looked like a
            // leaf and fell into the catch-all with the leaves. *It is a leaf that NAMES
            // something* -- and `M109` exists for exactly the names nobody writes wrong.
            //
            // **The `&` is carried into the name on purpose.** A bare `hart_bereit` in value
            // position is a PLACE (`ast.rs`, on `FnWert`: *"a bare name in value position is
            // a `place`"*), and the two must not be looked up in the same table: the bare
            // form has to keep falling, the `&` form has to resolve among FUNCTIONS. One
            // list of strings, two questions -- the marker says which.
            ExprArt::FnWert(p) => out.push(format!("&{}", p.text())),
            _ => {}
        }
    }
    match &p.art {
        PredArt::Vergleich(e) => aus_expr(e, gebunden, out),
        PredArt::Element(e, _) => aus_expr(e, gebunden, out),
        PredArt::Erreicht { von, nach, .. } => {
            aus_ort(von, gebunden, out);
            aus_ort(nach, gebunden, out);
        }
        // `Held(L)` nennt eine Sperre, keine Zusage ueber einen Wert.
        PredArt::Held { .. } => {}
        PredArt::Quantor(q) => {
            // Der TRAEGER der Domaene ist ein gewoehnlicher Ort und muss aufloesen; die
            // VARIABLE wird von ihr erklaert und darf es nicht muessen.
            match &q.domaene {
                Domaene::SlotsVon(o)
                | Domaene::NachfahrenVon(o)
                | Domaene::VorfahrenVon(o)
                | Domaene::Schlange(o)
                | Domaene::ElementeVon(o)
                | Domaene::AbbildungenVon(o)
                | Domaene::KetteIn { ort: o, .. } => aus_ort(o, gebunden, out),
                Domaene::FelderVon(_) | Domaene::Threads => {}
            }
            gebunden.push(q.variable.text.clone());
            sammle_namen_pred_geb(&q.rumpf, gebunden, out);
            gebunden.pop();
        }
        // **Die fuenf Verknuepfungen -- bis zum 2026-08-21 alle fuenf blind.**
        //
        // Gemessen: `ensures result > 0 && tippfehler > 0` gab **0 Fehler**, ebenso
        // `ensures !(tippfehler > 0)`. Sie fielen in den Sammelzweig, und damit war jede
        // ZUSAMMENGESETZTE Nachbedingung ungeprueft -- `M109` sah nur die atomare.
        //
        // > **Und `M111` schwieg mit.** Seine Bedingung traegt `&& !namen.is_empty()`; ein
        // > blinder Zweig sammelt keine Namen, also sah die Regel „nichts zu sagen" statt
        // > „nichts gesehen". *Eine Blindheit, die sich als Unbedenklichkeit liest, ist die
        // > teuerste Sorte* -- genau die Bewegung, gegen die W16 steht.
        //
        // Der Korpus trug die Luecke nicht: keine `ensures`-Zeile ist zusammengesetzt.
        // *Also war es hier kein Fehlalarm und morgen einer* -- dieselbe Begruendung, mit der
        // der Posten fuer `Self` im TODO steht.
        PredArt::Klammer(i) | PredArt::Nicht(i) => sammle_namen_pred_geb(i, gebunden, out),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            sammle_namen_pred_geb(a, gebunden, out);
            sammle_namen_pred_geb(b, gebunden, out);
        }
    }
}

/// **Bedingung 4:** liegt in diesem Rumpf eine weitere Schleife? Dann multipliziert sich die
/// Domaenenschranke, und «H2.1» schweigt.
fn enthaelt_schleife(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| match &s.art {
        StmtArt::Schleife(_) => true,
        _ => crate::unterbloecke(s).into_iter().any(enthaelt_schleife),
    })
}

/// **Die Zuwaechse eines Rumpfes: Name auf konstanten Zuwachs.**
///
/// Bedingung 2 in Reinform -- ein Name, der irgendwo ANDERS geschrieben wird als durch
/// `n += <Zahl>`, faellt heraus. *Zwei Zuwachsstellen fuer denselben Namen ebenfalls: nach
/// dem ersten Schreiben ist die Tatsache tot, und eine Regel, die das nicht mitrechnet,
/// waere eine, die den zweiten Zuwachs uebersieht.*
fn zuwaechse(b: &Block) -> Vec<(String, i128)> {
    let mut kandidaten: HashMap<String, Option<i128>> = HashMap::new();
    sammle_zuwaechse(b, &mut kandidaten);
    kandidaten
        .into_iter()
        .filter_map(|(n, k)| k.map(|k| (n, k)))
        .collect()
}

fn sammle_zuwaechse(b: &Block, aus: &mut HashMap<String, Option<i128>>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                let name = z.ziel.basis.text.clone();
                let gut = z.ziel.suffixe.is_empty()
                    && z.op == ZuwOp::Plus
                    && matches!(&z.wert.art, ExprArt::Zahl(n) if *n > 0);
                let k = match (&z.wert.art, gut) {
                    (ExprArt::Zahl(n), true) => Some(*n as i128),
                    _ => None,
                };
                // Zweite Schreibstelle desselben Namens -> heraus.
                aus.entry(name).and_modify(|e| *e = None).or_insert(k);
            }
            StmtArt::Let(l) => {
                aus.insert(l.name.text.clone(), None);
            }
            // **Ein Zuwachs in einer GESCHACHTELTEN Schleife ist keine Zahl** -- und bis
            // 2026-08-19 war er nicht einmal sichtbar. «H2.1» leitet aus
            // `n += k` die Schranke `n <= c + (B-1)*k` ab; laeuft derselbe Zuwachs in einer
            // inneren Schleife, gilt sie **nicht**, und der Pass sagte trotzdem ja.
            //
            // > *Die Vergroeberung ging in die gefaehrliche Richtung:* nicht „ich weiss es
            // > nicht", sondern „ich habe es nicht gesehen". Dasselbe gilt fuer die Auswege
            // > (`narrow … else`, `let … else`) und den `exchange`-Rumpf, der bei einem
            // > Fehlschlag mehrfach laeuft.
            StmtArt::Schleife(_)
            | StmtArt::Narrow(_)
            | StmtArt::LetSonst(_)
            | StmtArt::Exchange(_) => {
                let mut innen = HashMap::new();
                for k in crate::unterbloecke(s) {
                    sammle_zuwaechse(k, &mut innen);
                }
                for n in innen.into_keys() {
                    aus.insert(n, None);
                }
            }
            _ => {
                // Gerader Code in Klammern: `locks`, `breaking`, `observes`, die Zweige.
                for k in crate::unterbloecke(s) {
                    sammle_zuwaechse(k, aus);
                }
            }
        }
    }
}

/// Basis und erstes Feld eines Ortsschluessels: `s.bytes[i].x` -> `("s", Some("bytes"))`.
fn erstes_feld(k: &str) -> (&str, Option<&str>) {
    let ende = k.find(['.', '[']).unwrap_or(k.len());
    let basis = &k[..ende];
    let rest = &k[ende..];
    if let Some(r) = rest.strip_prefix('.') {
        let e = r.find(['.', '[']).unwrap_or(r.len());
        (basis, Some(&r[..e]))
    } else {
        (basis, None)
    }
}

/// Ist dieses Wort ein Typwort der Sprache? `u64::max` traegt es als Basis eines Ortes.
/// The `reason` an expression NAMES -- written as `R::F`, or as a binding that points at a
/// reason. **Both shapes, because `let … else` binds the second one.**
fn grundname_von(e: &Expr, lage: &Lage) -> Option<String> {
    match &e.art {
        ExprArt::Grund { grund, .. } => Some(grund.text.clone()),
        ExprArt::Klammer(x) => grundname_von(x, lage),
        ExprArt::Ort(o) if o.suffixe.is_empty() => match lage.lokal.get(&o.basis.text) {
            Some(Typ::Grund(n)) => Some(n.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// **The ways out of `M104`, and the third one is offered only where it exists.**
///
/// *«B3», hint 4 of five.* The measured `add two numbers` session read *"`u32 + u32` leaves
/// the width of the result type"*, changed the RETURN type to `u64` and got the identical
/// refusal back. The message named the fault and not the LINE it lives on -- the operands.
///
/// Three shapes were measured green on 2026-09-01, and they are named in the order a reader
/// should try them: a range on the declaration, a `narrow` before the line, a wider binding.
/// **The last one stops being a way out at 64 bits**, where there is no wider type, and an
/// message that offered it there would be advice nobody can follow.
fn wege_aus_der_breite(a: &IntBereich, b: &IntBereich) -> String {
    let breite = a.breite.max(b.breite);
    let art = if a.vorzeichen || b.vorzeichen { 'i' } else { 'u' };
    let kopf = format!(
        "two ways out: put a range on the operands where they are DECLARED \
         (`x : {art}{breite} in 0 .. N`), or `narrow x to 0 .. N else {{ … }}` before this line"
    );
    if breite >= 64 {
        format!("{kopf} -- at 64 bits there is no wider type to bind into")
    } else {
        format!(
            "{kopf}; or bind each operand into a wider type first \
             (`let w : {art}64 = x;`), and then the sum has room"
        )
    }
}

/// **`M146` -- the ENDS of a declared range are integers.**
///
/// `type T = u32 in 0.5 .. 1.5;` checked with `0 errors, 0 hints` until 2026-09-08, and
/// the bound the person wrote reached nothing: `umgebung::Umgebung::intbereich`
/// evaluates each end with `auswerten`, a float literal gives `None`, and the arm for
/// "an end that does not stand fast" is `IntBereich::voll` -- *the range does not get
/// NARROWER*. So the declaration lowers to the full width of the word.
///
/// **Measured against the UNCHANGED checker**, one file per row, `type T = <ty>` and a
/// body `return 9;`:
///
/// ```text
/// declaration            | pruefe
/// -----------------------|--------------------------
/// u32                    | 0 errors      (9 fits u32)
/// u32 in 0 .. 1          | 1 errors      (9 leaves the range)
/// u32 in 0.5 .. 1.5      | 0 errors      <- the written bound bought NOTHING
/// ```
///
/// The third row is the finding: the person wrote a bound, the checker kept none, and the
/// proof channel is handed `Shape.intIn 0 4294967295` -- a shape whose meaning nobody
/// stated (`PLAN.md` §3.1, `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §1.2).
///
/// ## Where it looks, and it is NINETEEN positions and not one
///
/// A range stands at three places in the grammar (`SYNTAX.md`: `intty`, `floatty`,
/// `narrowstmt`), and an `intty` stands wherever a `typeexpr` may. The sweep of 2026-09-08
/// wrote one probe per position and got **0 errors, 0 hints in all nineteen** -- so the
/// rule walks all of them rather than the one the census happened to write down. *A
/// measurement that stops at the first position that already objects answers "does one
/// position object", and the question was "which".*
///
/// ## Why a FLOAT LITERAL and not "an end that does not evaluate"
///
/// The wider rule would refuse `u32 in 0 .. N` wherever `N` is a name this file cannot
/// resolve -- an excerpt, a constant from another unit -- and that is *W10 in the expensive
/// direction*: a refusal with the sign that rejects a correct program. A float literal in
/// an integer range is decidable from the source alone and needs no environment. **What is
/// NOT refused here stays silent on purpose**: an unresolvable end is a second finding with
/// a second measurement, and it is not this one.
///
/// **And `floatty` is not touched.** `f64 in 0.5 .. 1.5` is the form the range was written
/// for; `umgebung::gleitwert` reads it, and it means what it says.
fn bereichsgrenzen(baum: &Programm, u: &Umgebung, absagen: &mut Absagen) {
    fn bruchstelle(e: &Expr) -> Option<Span> {
        crate::alle_ausdruecke(e)
            .into_iter()
            .find(|x| matches!(x.art, ExprArt::Gleitkomma { .. }))
            .map(|x| x.span)
    }
    fn range(b: &Bereich, wo: &str, absagen: &mut Absagen) {
        for (e, seite) in [(&b.von, "lower"), (&b.bis, "upper")] {
            let Some(span) = bruchstelle(e) else { continue };
            absagen.schiebe(
                Absage::fehler(
                    "M146",
                    span,
                    format!("the {seite} end of this range is not an integer"),
                )
                .mit_notiz(format!(
                    "in {wo}: an integer range is bounded by integers -- \
                     `Shape.intIn lo hi` in the model carries exactly this declaration"
                ))
                .mit_notiz(
                    "the end is DROPPED, it does not round: an end that does not stand \
                     fast widens the range to the whole word, so the written bound buys \
                     nothing and the model is handed the full range",
                ),
            );
        }
    }
    fn im_typ(t: &TypExpr, wo: &str, absagen: &mut Absagen) {
        // **Only `intty`.** `floatty` carries the same shape of clause and means it --
        // `umgebung::gleitwert` reads a fraction there and keeps it.
        if let TypExpr::Int(i) = t {
            if let Some(b) = &i.bereich {
                range(b, wo, absagen);
            }
        }
    }
    // **The statement half, and it is its own walk on purpose.**
    //
    // `crate::jeder_typausdruck_im_item` visits DECLARED types of an item and says so; a
    // `let`'s type and a `narrow`'s range stand in a BODY, and no item-level walk reaches
    // them. *Three of the nineteen positions of the sweep are here.*
    //
    // **`narrow` is the one position that needs the ENVIRONMENT**, and the corpus said so
    // before any reasoning did: `narrowstmt = "narrow" place "to" (range | "finite")` hangs
    // a range on a PLACE and not on a type, so `narrow x to 0.0 .. 1.0` is the correct
    // spelling at an `f64` and the fault at a `u32`. The first build of this rule read the
    // range alone and refused `beispiele/26-gleitkomma.gab`:42 -- *`impl fn klemmen(x :
    // f64)`, the file that exists to show `narrow … else` as the NaN path.* **A refusal with
    // the sign that rejects a correct program, W10, caught by the corpus sweep and not by
    // the design.** So the place is resolved, and where it does not resolve to an integer --
    // for any reason, a float, a name this walk cannot see -- nothing is said.
    fn im_block(
        b: &Block,
        wo: &str,
        modul: &str,
        u: &Umgebung,
        lokal: &mut HashMap<String, Typ>,
        absagen: &mut Absagen,
    ) {
        for s in &b.anweisungen {
            match &s.art {
                StmtArt::Let(l) => {
                    if let Some(t) = &l.typ {
                        im_typ(t, wo, absagen);
                        lokal.insert(l.name.text.clone(), u.typ_von_ausdruck_decl(modul, t));
                    }
                }
                // **«E4»:** the `alloc` annotation is a type in a body like
                // the `let` one -- same walk, same map.
                StmtArt::Alloc(a) => {
                    if let Some(t) = &a.typ {
                        im_typ(t, wo, absagen);
                        lokal.insert(a.name.text.clone(), u.typ_von_ausdruck_decl(modul, t));
                    }
                }
                // **`let … else` carries no type annotation** (`ast::LetSonst` has
                // `quelle` and no `typ`), so it is not a position a range can stand in --
                // named here rather than left to the `_` below, because the reader's
                // question is "which of the nineteen" and the answer for this one is
                // "the grammar has no slot".
                StmtArt::Narrow(n) => {
                    if let NarrowZiel::Bereich(r) = &n.ziel {
                        if matches!(
                            u.typ_von_ort(modul, &n.ort, lokal).durchgreifen(),
                            Typ::Ganzzahl(_) | Typ::Umlaufend(_)
                        ) {
                            range(r, wo, absagen);
                        }
                    }
                }
                _ => {}
            }
            for k in crate::unterbloecke(s) {
                im_block(k, wo, modul, u, &mut lokal.clone(), absagen);
            }
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let wo = item.art.benennung();
        crate::jeder_typausdruck_im_item(item, &mut |t| im_typ(t, wo, absagen));
        // **The item kinds `jeder_typausdruck_im_item` does not reach**, written out
        // here rather than added there: that walk feeds `bindung.rs` and `namen.rs`, and
        // widening it is a change to THEIR population and belongs to a measurement of its
        // own. *Named, not swept under a `_`.*
        match &item.art {
            ItemArt::Axiom(a) => {
                for p in &a.parameter {
                    im_typ(&p.typ, wo, absagen);
                }
                if let Some(t) = &a.rueckgabe {
                    im_typ(t, wo, absagen);
                }
            }
            ItemArt::Accumulates(a) => im_typ(&a.typ, wo, absagen),
            ItemArt::Funktion(f) => {
                if let FnRumpf::Block(b) = &f.rumpf {
                    // The parameters are the scope a body starts in; without them a
                    // `narrow` on a parameter resolves to nothing and stays silent, which
                    // is the quiet direction and the wrong one for a rule that is supposed
                    // to reach all nineteen positions.
                    let mut lokal: HashMap<String, Typ> = f
                        .parameter
                        .iter()
                        .map(|p| {
                            (p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ))
                        })
                        .collect();
                    im_block(b, wo, modul, u, &mut lokal, absagen);
                }
            }
            ItemArt::Check(c) => {
                im_block(&c.can_fail, wo, modul, u, &mut HashMap::new(), absagen)
            }
            _ => {}
        }
    });
}

/// **The third operator table against the second** -- see `opsruf::operatortafeln` for why
/// there are three and what the `_ => "?"` in this one did.
#[cfg(test)]
mod operatortafel {
    use super::*;

    #[test]
    fn op_zeichen_sagt_dasselbe_wie_fremdverengung() {
        let alle = [
            BinOp::Oder,
            BinOp::Und,
            BinOp::Gleich,
            BinOp::Ungleich,
            BinOp::Kleiner,
            BinOp::KleinerGleich,
            BinOp::Groesser,
            BinOp::GroesserGleich,
            BinOp::BitUnd,
            BinOp::BitOder,
            BinOp::BitXor,
            BinOp::SchiebLinks,
            BinOp::SchiebRechts,
            BinOp::Plus,
            BinOp::Minus,
            BinOp::Mal,
            BinOp::Geteilt,
            BinOp::Rest,
            BinOp::PlusWrap,
            BinOp::MinusWrap,
            BinOp::MalWrap,
            BinOp::SchiebLinksWrap,
            BinOp::PlusSat,
        ];
        for op in alle {
            assert_eq!(op_zeichen(op), crate::fremdverengung::zeichen(op), "{op:?}");
            assert_ne!(op_zeichen(op), "?", "{op:?}");
        }
    }
}

/// **M150 probes -- unary minus leaves the width.**
///
/// The gift files `749`/`750`/`751` pin the shapes file by file; these tests pin
/// the exactness the file-level run cannot: the must-fall fires EXACTLY once,
/// and the must-pass twins fire NOTHING AT ALL (no `M150` beside another code,
/// no second site).
#[cfg(test)]
mod m150_proben {
    use gabbro_syntax::diag::Stufe;

    fn fehler(quelle: &str) -> Vec<&'static str> {
        let (baum, mut absagen) = gabbro_syntax::lies("m150.gab", quelle);
        let _ = crate::pruefe(&baum, &mut absagen);
        absagen
            .absagen
            .iter()
            .filter(|a| a.stufe == Stufe::Fehler)
            .map(|a| a.code)
            .collect()
    }

    /// Must-fall: a full-range `i32` negated into a wider result. `M101` stays
    /// silent here -- it compares intervals, never widths -- so without `M150`
    /// this program passed with 0 errors (measured over the unchanged checker).
    #[test]
    fn offene_negation_faellt_genau_einmal() {
        let f = fehler(
            "module probe::m150_fall {\n\
             impl fn negiere(x : i32) -> i64 effects { pure } {\n\
                 return -x;\n\
             }\n\
             }\n",
        );
        assert_eq!(f, vec!["M150"], "open negation must fall exactly once");
    }

    /// Must-pass: a V1-narrowed operand, the declared boundary without the
    /// smallest value, and a `wrapping` operand whose overflow is declared.
    #[test]
    fn enge_negation_schweigt() {
        let still = [
            // V1 fact: `-x` over `0 .. 100` is `-100 .. 0` and fits.
            "module probe::m150_eng1 {\n\
             impl fn negiere(x : i32) -> i64 effects { pure } {\n\
                 narrow x to 0 .. 100 else { return 0; }\n\
                 return -x;\n\
             }\n\
             }\n",
            // Declared boundary: without `INT_MIN` the negation fits exactly.
            "module probe::m150_eng2 {\n\
             impl fn negiere(x : i32 in -2147483647 .. 2147483647) -> i64 effects { pure } {\n\
                 return -x;\n\
             }\n\
             }\n",
            // Declared overflow: `wrapping` is exempt, as at `M104`.
            "module probe::m150_eng3 {\n\
             table Z count 4 { slot { marke : u32 wrapping, } }\n\
             impl fn negiere(z : ptr<normal, r> Z) -> i64 effects { reads z.slots } {\n\
                 return -z.slots[0].marke;\n\
             }\n\
             }\n",
        ];
        for (n, quelle) in still.iter().enumerate() {
            assert!(
                fehler(quelle).is_empty(),
                "still shape {n} must stay silent, fell with {:?}",
                fehler(quelle)
            );
        }
    }

    /// Boundary: one value decides. The pair differs by the smallest value of
    /// the width only -- the first stays silent, the second falls exactly once.
    #[test]
    fn grenze_entscheidet_um_einen_wert() {
        let f = fehler(
            "module probe::m150_grenze {\n\
             impl fn rand(x : i32 in -2147483647 .. 2147483647) -> i64 effects { pure } {\n\
                 return -x;\n\
             }\n\
             impl fn voll(y : i32) -> i64 effects { pure } {\n\
                 return -y;\n\
             }\n\
             }\n",
        );
        assert_eq!(f, vec!["M150"], "boundary pair must fall exactly once");
    }
}

/// **M152 probes -- the remainder at `INT_MIN % -1` traps.**
///
/// The gift files `780`/`781`/`782` pin the shapes file by file; these tests pin
/// the exactness the file-level run cannot: the must-fall fires EXACTLY once,
/// and the must-pass twins fire NOTHING AT ALL (no `M152` beside another code,
/// no second site).
#[cfg(test)]
mod m152_proben {
    use gabbro_syntax::diag::Stufe;

    fn fehler(quelle: &str) -> Vec<&'static str> {
        let (baum, mut absagen) = gabbro_syntax::lies("m152.gab", quelle);
        let _ = crate::pruefe(&baum, &mut absagen);
        absagen
            .absagen
            .iter()
            .filter(|a| a.stufe == Stufe::Fehler)
            .map(|a| a.code)
            .collect()
    }

    /// Must-fall: an open `i32` dividend against a `-1` denominator. The
    /// computed range fits (`0 .. 0`), so without `M152` this program passed
    /// with 0 errors (measured over the unchanged checker) -- and the emitter
    /// wrote `return x % y;` into C that traps at `x == INT_MIN`.
    #[test]
    fn offener_rest_gegen_minus_eins_faellt_genau_einmal() {
        let f = fehler(
            "module probe::m152_fall {\n\
             impl fn rest(x : i32, y : i32 in -1 .. -1) -> i32 effects { pure } {\n\
                 return x % y;\n\
             }\n\
             }\n",
        );
        assert_eq!(f, vec!["M152"], "open remainder over -1 must fall exactly once");
    }

    /// Must-pass: a denominator narrowed away from `-1`, an unsigned pair
    /// (defined in C for every nonzero denominator), and a dividend narrowed
    /// away from the smallest value.
    #[test]
    fn enger_rest_schweigt() {
        let still = [
            // No `-1` in the denominator range: nothing can trap.
            "module probe::m152_eng1 {\n\
             impl fn rest(x : i32, y : i32 in 1 .. 100) -> i32 effects { pure } {\n\
                 return x % y;\n\
             }\n\
             }\n",
            // Unsigned: `%` is defined for every nonzero denominator.
            "module probe::m152_eng2 {\n\
             impl fn rest(x : u32, y : u32) -> u32 effects { pure } {\n\
                 if y >= 1 {\n\
                     return x % y;\n\
                 }\n\
                 return 0;\n\
             }\n\
             }\n",
            // Dividend without its smallest value: `-1` divides everything left.
            "module probe::m152_eng3 {\n\
             impl fn rest(x : i32 in -100 .. 100, y : i32 in -1 .. -1) -> i32 effects { pure } {\n\
                 return x % y;\n\
             }\n\
             }\n",
        ];
        for (n, quelle) in still.iter().enumerate() {
            assert!(
                fehler(quelle).is_empty(),
                "still shape {n} must stay silent, fell with {:?}",
                fehler(quelle)
            );
        }
    }

    /// Boundary: one value decides. The pair differs by `-1` in the denominator
    /// range only -- the first stays silent, the second falls exactly once.
    #[test]
    fn nennergrenze_entscheidet_um_einen_wert() {
        let f = fehler(
            "module probe::m152_grenze {\n\
             impl fn eng(x : i32, y : i32 in -2 .. -2) -> i32 effects { pure } {\n\
                 return x % y;\n\
             }\n\
             impl fn offen(x : i32, y : i32 in -2 .. -1) -> i32 effects { pure } {\n\
                 return x % y;\n\
             }\n\
             }\n",
        );
        assert_eq!(f, vec!["M152"], "denominator boundary must fall exactly once");
    }
}

/// **V2-subtraction probes -- `M104` at the operation, not `M101` at the assignment.**
///
/// The gift file `783` pins the shape file by file; these tests pin the
/// exactness the file-level run cannot: the open subtraction under `a >= b`
/// falls with EXACTLY `["M104"]` at the operation (measured over the unchanged
/// checker it passed with 0 errors into an `i64` result), and the narrowed
/// twin fires nothing.
#[cfg(test)]
mod vsub_proben {
    use gabbro_syntax::diag::Stufe;

    fn fehler(quelle: &str) -> Vec<&'static str> {
        let (baum, mut absagen) = gabbro_syntax::lies("vsub.gab", quelle);
        let _ = crate::pruefe(&baum, &mut absagen);
        absagen
            .absagen
            .iter()
            .filter(|a| a.stufe == Stufe::Fehler)
            .map(|a| a.code)
            .collect()
    }

    /// Must-fall: two open `i32` under `a >= b` build `0 .. 4294967295` -- out
    /// of the width the C computes in -- and refuse at the `-` node itself.
    #[test]
    fn offene_v2_differenz_faellt_an_der_operation() {
        let f = fehler(
            "module probe::vsub_fall {\n\
             impl fn diff(a : i32, b : i32) -> i64 effects { pure } {\n\
                 if a >= b {\n\
                     return a - b;\n\
                 }\n\
                 return 0;\n\
             }\n\
             }\n",
        );
        assert_eq!(
            f,
            vec!["M104"],
            "open V2 difference must fall at the operation"
        );
    }

    /// Must-pass: narrowed operands keep the V2 range inside the width.
    #[test]
    fn enge_v2_differenz_schweigt() {
        let f = fehler(
            "module probe::vsub_still {\n\
             impl fn diff(a : i32 in 0 .. 100, b : i32 in 0 .. 50) -> i64 effects { pure } {\n\
                 if a >= b {\n\
                     return a - b;\n\
                 }\n\
                 return 0;\n\
             }\n\
             }\n",
        );
        assert!(
            f.is_empty(),
            "narrowed V2 difference must stay silent, fell with {f:?}"
        );
    }
}
