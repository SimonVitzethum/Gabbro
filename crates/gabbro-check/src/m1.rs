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

fn lauf(baum: &Programm, absagen: &mut Absagen) -> (Zaehlung, Vec<Stelle>) {
    let umgebung = Umgebung::sammle(baum);
    let mut spezifikationen = std::collections::HashMap::new();
    sammle_spezifikationen(&baum.items, &mut spezifikationen);
    let mut p = Pruefer {
        u: &umgebung,
        absagen,
        zaehlung: Zaehlung::default(),
        modul: String::new(),
        rufer: String::new(),
        fremd: Vec::new(),
        spezifikationen,
        unveraenderlich: std::collections::HashSet::new(),
        unveraenderliche_statiken: std::collections::HashMap::new(),
        schon_gemeldet: std::collections::HashSet::new(),
    };
    p.programm(baum);
    (p.zaehlung, p.fremd)
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
}

/// Die Bindungen und Fakten eines Blocks. Ein Block erbt beide und gibt keins zurueck.
#[derive(Clone, Default)]
struct Lage {
    lokal: HashMap<String, Typ>,
    fakten: Vec<Fakt>,
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
                self.passt(&quelle, &ziel, k.wert.span, "die Konstante");
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
                self.passt(&quelle, &ziel, st.wert.span, "der statische Wert");
            }
            if let ItemArt::Funktion(f) = &item.art {
                self.modul = modul.to_string();
                self.ensures_pruefen(f);
                self.maintains_pruefen(f);
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
                    self.block(b, &mut lage, ergebnis.as_ref());
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

    fn anweisung(&mut self, s: &Stmt, lage: &mut Lage, ergebnis: Option<&Typ>) {
        match &s.art {
            StmtArt::Let(l) => {
                let wert = self.ausdruck(&l.wert, lage);
                self.rufe_im_ausdruck(&l.wert, lage);
                let ziel = l.typ.as_ref().map(|t| self.u.typ_von_ausdruck_decl(&self.modul, t));
                if let Some(z) = &ziel {
                    self.passt(&wert, z, l.wert.span, "die Bindung");
                }
                // U2: die neue Bindung verdeckt die alte -- jeder Fakt ueber den Namen
                // stirbt, sonst erbt die Verdeckung die Verengung ihres Vorgaengers.
                lage.fakten
                    .retain(|f| !nennt_namen(f, &l.name.text));
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
                let t = match l.als_ruf() {
                    Some(r) => self.ruf(r, lage),
                    None => crate::typen::Typ::Unbekannt,
                };
                lage.fakten.retain(|f| !nennt_namen(f, &l.name.text));
                lage.lokal.insert(l.name.text.clone(), t);
                self.aufruf_toetet_fakten(lage);
                self.unterblock(&l.sonst, lage, ergebnis);
            }
            StmtArt::Zuweisung(z) => {
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
                let ziel = self.u.typ_von_ort(&self.modul, &z.ziel, &lage.lokal);
                self.buche(&ziel);
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
                        "die Zuweisung",
                    );
                }
                self.schreiben_toetet_fakten(&z.ziel, lage);
            }
            StmtArt::Publish(p) => {
                self.index_pruefen(&p.ziel, lage);
                let ziel = self.u.typ_von_ort(&self.modul, &p.ziel, &lage.lokal);
                self.buche(&ziel);
                let quelle = self.ausdruck(&p.wert, lage);
                self.rufe_im_ausdruck(&p.wert, lage);
                self.passt(&quelle, &ziel, p.wert.span, "die Veroeffentlichung");
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
                // Schleifen tragen keine Fakten hinein -- die Invariante der Traversierung
                // tut das, und die gehoert dem Beweiser.
                let mut innen = Lage {
                    lokal: lage.lokal.clone(),
                    fakten: Vec::new(),
                };
                let rumpf = match sch.as_ref() {
                    Schleife::Traverse(t) => {
                        innen
                            .lokal
                            .insert(t.variable.text.clone(), Typ::Unbekannt);
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
                if let Some(z) = ergebnis {
                    let z = z.clone();
                    self.passt_wert(e, &t, &z, e.span, "die Rueckgabe");
                }
            }
            StmtArt::Ruf(r) => {
                let _ = self.ruf(r, lage);
                self.aufruf_toetet_fakten(lage);
            }
            StmtArt::AwaitLoad(a) => {
                let t = self.u.typ_von_ort(&self.modul, &a.quelle, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(a.name.text.clone(), t);
            }
            StmtArt::Exchange(e) => {
                let t = self.u.typ_von_ort(&self.modul, &e.ort, &lage.lokal);
                self.buche(&t);
                lage.lokal.insert(e.name.text.clone(), t.clone());
                if let XForm::Update { binder, rumpf, .. } = &e.form {
                    let mut innen = lage.clone();
                    innen.lokal.insert(binder.text.clone(), t);
                    self.block(rumpf, &mut innen, ergebnis);
                }
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
                let name = r
                    .pfad
                    .teile
                    .last()
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
            ExprArt::Zahl(v) => match i128::try_from(*v) {
                Ok(w) => Typ::Ganzzahl(IntBereich::konstante(w)),
                Err(_) => Typ::Unbekannt,
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
            ExprArt::Klammer(i) => self.ausdruck_roh(i, lage),
            ExprArt::Ort(o) => {
                self.name_aufloesen(o, lage);
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
            ExprArt::Eingebaut(_) => Typ::Unbekannt,
            ExprArt::Unaer(UnOp::Nicht, i) => {
                let _ = self.ausdruck(i, lage);
                Typ::Wahrheit
            }
            ExprArt::Unaer(UnOp::Negativ, i) => {
                let t = self.ausdruck(i, lage);
                match t.bereich() {
                    Some(b) => Typ::Ganzzahl(IntBereich::genau(
                        b.breite,
                        true,
                        -b.max,
                        -b.min,
                    )),
                    None => Typ::Unbekannt,
                }
            }
            ExprArt::Binaer(op, a, b) => self.binaer(*op, a, b, e.span, lage),
        }
    }

    fn binaer(&mut self, op: BinOp, a: &Expr, b: &Expr, span: Span, lage: &Lage) -> Typ {
        let ta = self.ausdruck(a, lage);
        let tb = self.ausdruck(b, lage);
        if op == BinOp::Und || op == BinOp::Oder {
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
        if op == BinOp::Minus {
            if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {
                if let Some(untergrenze) = self.beziehung(oa, ob, lage) {
                    return Typ::Ganzzahl(IntBereich::genau(
                        ba.breite,
                        ba.vorzeichen,
                        untergrenze,
                        (ba.max - bb.min).max(untergrenze),
                    ));
                }
            }
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
                    typen::rest(&ba, &bb)
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
        // **Aufgeloest wird im Modul des Aufrufs**, nicht ueber den blanken Namen.
        let signatur = self.u.funktion(&self.modul, &r.pfad).cloned();
        let mut argtypen = Vec::new();
        for a in &r.argumente {
            argtypen.push((self.ausdruck(a, lage), a.span));
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
        if r.pfad.teile.last().is_some_and(|n| n.text == "Some") {
            return argtypen.first().map(|(t, _)| t.clone()).unwrap_or(Typ::Unbekannt);
        }
        let Some(sig) = signatur else {
            return Typ::Unbekannt;
        };
        // Die Stelligkeit gehoert dem Namenspass; hier faellt nur der Bereich.
        for ((t, span), (pname, pt)) in argtypen.iter().zip(sig.parameter.iter()) {
            self.passt(t, pt, *span, &format!("das Argument `{pname}`"));
        }
        self.requires_pruefen(r, &sig, &argtypen);
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
                    gerufener: r.pfad.text(),
                    span: r.span,
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
    fn requires_pruefen(&mut self, r: &Ruf, sig: &crate::umgebung::Signatur, argtypen: &[(Typ, Span)]) {
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
                        "M115",
                        *span,
                        format!(
                            "`{}` requires `{name} {} {zahl}`, and the argument lies in \
                                {} .. {}",
                            r.pfad.text(),
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
        let gefunden = self.u.verbundfelder(&self.modul, &r.pfad).cloned();
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
                                r.pfad.text(),
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
                            r.pfad.text()
                        ),
                    )
                    .mit_notiz(format!(
                        "`{}({})`",
                        r.pfad.text(),
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
                        format!("`{}` is not a struct; labels exist only at a constructor", r.pfad.text()),
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
    fn nan_moeglich(&mut self, e: &Expr, lage: &Lage) -> bool {
        match self.ausdruck(e, lage) {
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
            let lage_kopie = &Lage { lokal: lage.lokal.clone(), fakten: Vec::new() };
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
    }

    /// Ein Aufruf toetet die Fakten ueber alles **Nichtlokale**. Lokale Groessen kann er
    /// nicht aendern: Gabbro hat keinen Adressoperator.
    /// **U5.** Ein Aufruf steht selten allein: `let t = nuller(z);` ist derselbe Aufruf wie
    /// `nuller(z);`. Vorher toetete nur die zweite Form Fakten -- ein Zeichen Unterschied
    /// entschied ueber die Zusage.
    fn rufe_im_ausdruck(&self, e: &Expr, lage: &mut Lage) {
        if enthaelt_ruf(e) {
            self.aufruf_toetet_fakten(lage);
        }
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

    // -- Absagen ------------------------------------------------------------------------

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
                format!("{was} wandelt `{name}` stillschweigend um"),
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

    fn passt(&mut self, quelle: &Typ, ziel: &Typ, span: Span, was: &str) {
        self.undurchsichtigkeit_pruefen(quelle, ziel, span, was);
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
                fehlt.push("unendlich");
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
                            fehlt.join(" und kein ")
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
            ),
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
        let Some(sig) = self.u.funktion(&self.modul, &r.pfad).cloned() else { return };
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
                    gerufener: r.pfad.text(),
                    span: r.span,
                    klausel: format!("result {} {}", zeichen(op), ort.text()),
                    wirkung: Wirkung::Beziehung,
                });
            }
            lage.fakten.push(Fakt::Beziehung { links, op, rechts, indizes });
        }
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
        if o.text().contains("::") || breite_wort(n) {
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
            || n == "result";
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

    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {
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

fn trennt(c: Option<u8>) -> bool {
    matches!(c, Some(b'.') | Some(b'[') | Some(b'-'))
}

/// Steht irgendwo in diesem Ausdruck ein Aufruf?
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
        _ => false,
    }
}

/// Ist dieser Ausdruck der Konstruktor `Some(…)`? **`Some` ist ein reserviertes Wort**
/// (`kw.rs`), also kann diese Frage keine benutzerdeklarierte Funktion treffen.
fn ist_some(e: &Expr) -> bool {
    match &e.art {
        ExprArt::Ruf(r) => r.pfad.teile.last().is_some_and(|n| n.text == "Some"),
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
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        _ => "?",
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
        _ => {}
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
fn breite_wort(n: &str) -> bool {
    matches!(
        n,
        "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" | "bool" | "f32" | "f64"
    )
}
