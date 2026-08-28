//! **Die dritte Zaehlspalte: die Erzeuger-Schablonen.**
//!
//! Der Wortschatz hat seine Ratsche (`pruefe-wortschatz.py`, 189 gegen 189). Die Axiomschicht
//! hat ihre (`gabbro annahmen`, „bewiesen unter A1…An"). **Die Schablonen hatten keine** — und
//! sie sind der Empfaenger jeder Rettung ueber den *dritten Ausgang*: `by consuming`,
//! `table ops`, `transset`, `exchange`, `accumulates`, und die Kandidaten, die diese Woche
//! dazukamen (erzeugte Suche, erzeugtes `reset`, Konstruktoren, Gruppen-`ops`).
//!
//! > **Jede dieser Rettungen faellt „einmal in der Schablone".** Die Schablone ist die
//! > **vertrauenskritischste, unbewiesene Flaeche**, geprueft vom unverifizierten Kern
//! > ([`BEWEIS.md`](BEWEIS.md)). Ohne Zaehlung waechst sie **monoton und unbeziffert** — genau
//! > wie die Axiomschicht vor ihrer Auszaehlung.
//!
//! Damit hoert der eine Isabelle-Posten auf, **ein Posten** zu sein, und wird **eine Liste mit
//! Laenge**. Die Pruefzeile des dritten Ausgangs bekommt ihren zweiten Halbsatz:
//!
//! > *Waere die Aussage noetig, wenn die Operation erzeugt waere —* **und was kostet die
//! > erzeugte Form die Schablonenflaeche?**
//!
//! ## Die Regel, die ueber allen Eintraegen steht (W6)
//!
//! Schablonen erzeugen zweierlei: **Beweispflichten** und **Code**. Zwischen beiden verlaeuft
//! die Linie, an der dieser Ordner schon einmal bezahlt hat:
//!
//! > **Das Weglassen einer Laufzeitpruefung ist ausschliesslich M1-begruendet, nie
//! > invariantenbegruendet. Das zitierte Faktum muss aus M1 allein ableitbar sein — sonst
//! > bleibt die Pruefung im C.**
//!
//! **M1 haengt am Typ und wird je Programm nachgerechnet. Eine Invariante haengt an der
//! Schablone, die sie erhaelt — also an genau dieser Flaeche hier**, der unbewiesenen. Wer
//! eine Bereichspruefung streicht, *weil der Beweis sagt, es koenne nicht negativ werden*,
//! entlaesst eine Behauptung ueber das Modell in die Maschine — woertlich die gebuchte
//! Fehlerklasse aus `5904cae`, eine Ebene tiefer.
//!
//! Die Regel sitzt **an der Emissionsentscheidung**, nicht am Gegenstand: eine Zeile im
//! Emissionspass statt einer je Konstrukt. **Sie ist weiterhin eine Vorabfestlegung** — der
//! Emissionspass existiert seit dem 2026-08-17 (`emit.rs`, zwei Mutationen), senkt aber genau
//! die Formen EINER Beispieldatei ab und weigert sich (`C001`) fuer jede andere. Keine
//! Schablone dieser Liste ist damit beruehrt.

/// Wie weit eine Schablone ist.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stand {
    /// In der Spezifikation benannt, kein Erzeugercode.
    Entworfen,
    /// Der Uebersetzer stuetzt sich heute darauf.
    Getragen,
    /// Einmal nach Isabelle gebracht. **Der einzige Stand, der die Vertrauensbasis
    /// verkleinert** — und seit dem 2026-08-16 erreichen ihn vier.
    Bewiesen,
}

impl Stand {
    pub const fn text(self) -> &'static str {
        match self {
            Stand::Entworfen => "entworfen",
            Stand::Getragen => "GETRAGEN",
            Stand::Bewiesen => "bewiesen",
        }
    }
}

/// **Eine Praemisse des Satzes -- und WER sie herstellt.**
///
/// Der dritte Zahn, seit 2026-08-18, und er kam aus einem Fund: `device.konstruktor` ist
/// BEWIESEN, und sein Hauptsatz setzt `getrennt r s` voraus -- *dass zwei Register getrennte
/// Lagen haben.* Kein Pass rechnet das nach (`pruefe-klauseln.py`: `versatz` wird nur
/// abgesenkt).
///
/// > **Das ist gefaehrlicher als eine ungelesene Klausel.** Bei der weiss niemand etwas; hier
/// > steht ein Isabelle-Beweis, und wer das Zeugnis liest, schliesst auf Ueberlappungsfreiheit.
/// > *Ein Beweis deckt die Luecke zu, statt sie zu zeigen.*
///
/// `durch` nennt, was die Praemisse herstellt, und die beiden Sorten sind nicht gleich stark:
///
/// ```text
/// ein PASS            deckt jedes Programm, das der Uebersetzer je sieht
/// eine MUTATIONSPROBE deckt den ERZEUGER, einmal -- die Bruecke aus PLAN.md PL.3
/// None                NIEMAND. Der Satz haengt in der Luft.
/// ```
#[derive(Clone)]
pub struct Voraussetzung {
    pub was: &'static str,
    pub durch: Option<&'static str>,
    /// **Was sie herstellen WUERDE -- der dritte Zahn, geschaerft am 2026-08-19.**
    ///
    /// `durch: None` sagte bisher nur *„niemand"*. Eine Liste von Loechern ohne die Angabe,
    /// womit man sie fuellt, ist eine Klage und kein Arbeitsauftrag -- *derselbe Satz, den
    /// das Tor von P6 ueber die Kennzahl schreibt: „eine Zahl ohne diese Aufschluesselung
    /// ist wertlos, weil sie keinen Arbeitsauftrag enthaelt."*
    ///
    /// **Und es ist ausdruecklich kein Ersatz fuer `durch`.** Eine Praemisse mit `braeuchte`
    /// und ohne `durch` steht weiter in `in_der_luft()`; sie zaehlt als offen. *Der
    /// Unterschied ist, dass jetzt dabeisteht, was fehlt.*
    pub braeuchte: Option<&'static str>,
}

#[derive(Clone)]
pub struct Schablone {
    pub name: &'static str,
    /// **Andere Schablonen, auf denen diese ruht.** Neu am 2026-08-16, und der Grund ist ein
    /// Fund: die Formalisierung von `table.induktion` spuelte aus, dass ihre Endlichkeit
    /// nicht aus ihrer eigenen Deklaration faellt, sondern aus `table.indexschranke`.
    ///
    /// > **Eine Schablonenliste ohne Abhaengigkeiten sieht aus wie 17 unabhaengige Posten --
    /// > und ist es nicht.** Wer eine faellt, faellt sie moeglicherweise unter einer, die
    /// > noch steht.
    pub haengt_an: &'static [&'static str],
    /// Welches Konstrukt sie traegt.
    pub konstrukt: &'static str,
    /// **Was genau einmal gezeigt werden muss.** Ohne diesen Satz ist ein Eintrag ein Name.
    pub pflicht: &'static str,
    pub stand: Stand,
    /// **Die Rueckrichtung: welche Praemisse stellt welcher Pass her?**
    ///
    /// Pflicht fuer jeden `Bewiesen`-Eintrag (Zahn 3). Leer bei `Entworfen`/`Getragen` --
    /// dort ist der Satz noch nicht gefuehrt, also gibt es auch keine Praemisse zu binden.
    pub voraussetzungen: &'static [Voraussetzung],
    pub fundstelle: &'static str,
}

/// **Die Fallrichtung der Ratsche** — ausgesprochen wie bei der Axiomschicht, sonst ist die
/// Liste eine Sammlung und keine Buchung:
///
/// > **Ein Eintrag verlaesst die Liste nur auf zwei Wegen: BEWIESEN, oder MITSAMT SEINEM
/// > KONSTRUKT.** Nicht durch Umformulierung, nicht durch Zusammenfassen zweier Eintraege zu
/// > einem, nicht dadurch, dass die Pflicht „eigentlich schon in einer anderen steckt".
///
/// Dieselbe Bewegung, gegen die die Kennzahl fuenf benannte Wege fuehrt: **eine Flaeche, die
/// man durch Umschreiben verkleinert, ist nicht kleiner geworden.** `RATSCHE` unten haelt das
/// mechanisch — wer einen Namen entfernt, bricht einen Test.
pub const RATSCHE: &[&str] = &[
    "consuming.ordnung",
    "consuming.umhaengen",
    "consuming.leermenge",
    "table.ops.erhaltung",
    "table.induktion",
    "transition.transset",
    "exchange.rmw",
    "accumulates.monoid",
    "walk.mappings",
    "format.roundtrip",
    "entry.abdruck",
    "device.konstruktor",
    "table.indexschranke",
    "table.absenkung",
    "ops.suche",
    "state.reset",
    "verbund.konstruktor",
    "gruppe.ops",
    "gruppe.sperrabdruck",
    "option.sonderwert",
    "restrict.alleinzugriff",
];

/// **Die Liste.** Jeder Eintrag ist eine Beweispflicht, die der Erzeuger schuldet — einmal,
/// nicht je Aufrufstelle. Ein neues Konstrukt mit erzeugter Form **gehoert hierher, bevor es
/// in die Grammatik kommt**.
pub const SCHABLONEN: &[Schablone] = &[
    Schablone {
        name: "restrict.alleinzugriff",
        haengt_an: &[],
        konstrukt: "ptr<…> T als Parameter (Absenkung mit `restrict`)",
        // **Eingetragen 2026-08-19, als der Erzeuger `restrict` schrieb.** Der Anlass war eine
        // MESSUNG: 2,85 dort, wo der C-Uebersetzer die Herkunft der Zeiger nicht sieht.
        //
        // Und die zweite Messung am selben Tag hat den Eintrag sofort wieder eingeschraenkt:
        // der Fall, den die heutige Regel freischaltet -- EIN Zeiger gegen eine globale
        // Tabelle desselben Typs -- bringt **1,00**. GCC weiss laengst, dass ein `static`,
        // dessen Adresse nie genommen wird, von keinem Zeiger erreicht werden kann.
        // *Die Angabe, die C wirklich fehlt, ist die andere: ZWEI Zeiger desselben Typs, und
        // die verlangt die `own`-Entscheidung.*
        pflicht: "UNTER DEN HYPOTHESEN H1 (der Rahmen ist vollstaendig -- `E008` ueber den                   ORT, `E010` fuer das Lesen) und H2 (keine andere Wurzel trifft denselben                   Ort): jeder Zugriff des Rumpfes auf das Objekt hinter `p` laeuft ueber `p`,                   also gilt die C11-6.7.3.1-Bedingung -- **maschinell geprueft**                   (`restrict_gerechtfertigt`). H2a weist der Pruefer syntaktisch nach                   (hoechstens EIN Zeigerparameter je Traegertyp); H2b haelt die SPRACHE: ohne                   `cast` (G9) und ohne Adressoperator laesst sich ein Zeiger auf eine globale                   Tabelle nicht bilden. **NICHT bewiesen ist, dass `own` Exklusivitaet                   bedeutet** -- das ist eine Sprachentscheidung, und sie ist genau die, die                   H2a fuer zwei Zeiger desselben Typs liefern wuerde.",
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "H1 -- der Rahmen ist VOLLSTAENDIG: jeder Zugriff des Rumpfes hat eine Wurzel aus der deklarierten Menge", durch: Some("`E008` (kompositional ueber die Huelle, seit 2026-08-19 ueber den ORT und nicht die ART) und `E010` fuer das Lesen"), braeuchte: None },
            Voraussetzung { was: "H2a -- kein zweiter Zeigerparameter desselben Traegertyps", durch: Some("`emit::darf_restrict`, syntaktisch ueber die Signatur; Mutation `restrict-auch-bei-zwei-zeigern`"), braeuchte: None },
            Voraussetzung { was: "H2b -- kein globaler Traeger desselben Typs ist erreichbar", durch: Some("die SPRACHE: kein `cast` (G9), kein Adressoperator -- ein Zeiger auf eine globale Tabelle laesst sich nicht bilden; `darf_restrict` prueft die Wirkungsliste zusaetzlich"), braeuchte: None },
            Voraussetzung { was: "ZWEI `own`-Zeiger desselben Typs zeigen auf Verschiedenes -- das waere der Fall mit 2,85", durch: None, braeuchte: Some("ein PROGRAMM mit zwei besitzenden Zeigern desselben Traegers. *Die ENTSCHEIDUNG ist am 2026-08-20 gefallen -- `own` ist die Freigabeoperation (SPRACHE.md §5); damit koennten zwei `own`-Zeiger desselben Typs beide `restrict` tragen.* Gebaut ist sie NICHT, und der Grund ist gemessen: der ganze Korpus hat EINE Funktion mit zwei Zeigern desselben Traegers (`beispiele/07::wechseln`), und die traegt kein `own`. **Regel A** -- kein Konstrukt ohne ein Programm, das es gebraucht hat") },
        ],
        fundstelle: "beweise/Restrict_Alleinzugriff.thy; MESSUNGEN.md «OPT1» (2,85 gegen                      1,00); PLAN.md «OPT»",
    },
    Schablone {
        name: "option.sonderwert",
        haengt_an: &["table.indexschranke"],
        konstrukt: "option index into T (Absenkung)",
        // **Eingetragen 2026-08-17, als der Erzeuger F8 absenkte.** Die Darstellung war bis
        // dahin offen, und der Erzeuger weigerte sich (`C001`) statt zu vergroebern -- eine
        // Absenkung zu blankem `uint32_t` haette das `None` still geloescht.
        // **Nachgezogen 2026-08-17 nach der Formalisierung** (`beweise/Option_Sonderwert.thy`).
        // Die Praemisse `N < 2^w` stand in keiner der drei Fassungen des Satzes -- weder hier
        // noch in `SPRACHE.md` noch im Erzeuger. Sie kam aus dem Beweis und steht jetzt als
        // Pruefung im Erzeuger.
        // **Der Widerruf, 2026-08-19 («C1»).** Die zweite Haelfte stand hier als OFFEN, mit
        // der Begruendung *„heute weigert sich der Erzeuger fuer `None` als Ausdruck, und
        // solange er das tut, kann keine Rechnung ihn erzeugen"*. **Seit «C1» weigert er
        // sich nicht mehr** -- `T_NONE` steht wirklich im erzeugten C. *Damit war die
        // Begruendung verbraucht und die Luecke lebendig*, und sie wurde am selben Tag
        // gemessen: `h.slots[frei].kopf` ging mit null Fehlern durch.
        pflicht: "UNTER DER PRAEMISSE `N < 2^w` (w = Breite des Indexworts, heute 32): der \
                  Sonderwert `N` liegt ausserhalb der Indexdomaene `0 ..< N`, und die \
                  Kodierung `None -> N`, `Some i -> i` ist injektiv -- **maschinell geprueft** \
                  (`kodiere_wort_injektiv`). Bei `N = 2^w` faellt sie zusammen, und `None` ist \
                  von `Some 0` nicht mehr zu unterscheiden \
                  (`sonderwert_kollidiert_bei_vollem_wort`). **Die zweite Haelfte traegt seit \
                  «C1» ein PASS statt einer Weigerung:** `option index into T` reicht bis `N`, \
                  `index into T` bis `N-1` (umgebung.rs), also faellt jeder Gebrauch eines \
                  Optionswertes als Index an `M103` und jedes `Some(N)` an `M101`. **OFFEN \
                  bleibt die Arithmetik AUF einem Index** -- `i + 1` auf `index into T` \
                  rechnet M1 im Indexbereich nach, aber dass keine erzeugte Rechnung den \
                  Sonderwert TRIFFT, ist eine Aussage ueber `emit.rs` und keine ueber eine \
                  Menge.",
        stand: Stand::Getragen,
        voraussetzungen: &[],
        fundstelle: "FRAGMENTE.md F1 (vier CDT-Felder), F8 (`aufloesen`); MESSUNGEN.md B3, \
                     `while i != NIL`; beweise/Option_Sonderwert.thy",
    },
    Schablone {
        name: "consuming.ordnung",
        haengt_an: &["table.induktion"],
        konstrukt: "traverse … by consuming (ENTFERNEN)",
        // **Berichtigt und maschinell geprueft am 2026-08-16** (`beweise/Consuming.thy`).
        // Die alte Fassung trug zwei Saetze, die beide zu gross waren:
        //
        //   K-1  `unter der erzeugten Mutation` -- Singular, ohne zu nennen WELCHE. Bewiesen
        //        ist genau eine: das ENTFERNEN (`ordnung_bleibt_unter_entfernen`, ueber
        //        `wf_subset`). Das UMHAENGEN ist nicht gedeckt -> `consuming.umhaengen`.
        //   K-3  `daraus faellt die Blattheit` -- sie FAELLT NICHT. `wf` sagt, dass minimale
        //        Elemente EXISTIEREN, nicht dass die Traversierung eines NIMMT. Die fehlende
        //        Bedingung heisst `waehlt_minimal` und ist eine zusaetzliche Pflicht an die
        //        Erzeugung der Zeugenreihenfolge, keine Folge.
        pflicht: "Die Domaene liefert ihre Zeugen in der erzeugten wohlfundierten Ordnung. \
                  Unter dem ENTFERNEN des besuchten Zeugen bleibt die Ordnung erhalten -- die \
                  Kantenmenge wird kleiner, und eine Teilmenge einer wohlfundierten Relation \
                  ist wohlfundiert. **Die Blattheit zum Verbrauchszeitpunkt folgt daraus \
                  NICHT**; sie verlangt zusaetzlich, dass die Auswahl MINIMAL ist.",
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "die erzeugte Mutation ist ein ENTFERNEN und kein Umhaengen", durch: None, braeuchte: Some("ein Erzeuger fuer `by consuming` -- heute gibt es keinen; `umhaengen_faellt` (Table_Ops_Erhaltung) zeigt das Gegenbeispiel") },
            Voraussetzung { was: "die Auswahl des Zeugen ist MINIMAL (`waehlt_minimal`)", durch: None, braeuchte: Some("einen ERZEUGER der Zeugenreihenfolge -- an ihm haengt die Minimalitaet, und es gibt keinen. *Berichtigt 2026-08-20: hier stand `abstieg ist eine ZUSAGE ohne Leser`, und das war seit dem 2026-08-19 falsch -- `S005` liest ihn. S005 prueft aber, dass das MASS sich bewegen kann, nicht dass die AUSWAHL minimal ist; zwei verschiedene Aussagen*") },
        ],
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "consuming.umhaengen",
        haengt_an: &["consuming.ordnung"],
        konstrukt: "traverse … by consuming (UMHAENGEN)",
        // **Abgespalten am 2026-08-16, und die naive Fassung ist WIDERLEGT.**
        // `umhaengen_kann_zyklus_erzeugen` in `beweise/Consuming.thy` konstruiert einen
        // wohlfundierten Zustand, aus dem EIN Umhaengen eine Schlinge macht.
        //
        // **Und es ist kein Randfall.** Der Bestand tut beides in EINEM Zug: `delete_leaf`
        // ruft `unlink`, und `unlink` schreibt die Geschwisterzeiger der NACHBARN um --
        // B3 hat das als Marke Nb2 gezaehlt (`space.rs:1044`).
        //
        // **2026-08-28: ONE such mutation has been shown individually since, and this entry
        // stays `Entworfen` all the same.** `umhaengen_erhaelt` (Table_Ops_Erhaltung, U-3)
        // gives the condition for re-hanging along the PARENT edge, outside any traversal.
        // What this entry is about is the re-hanging of sibling and child pointers DURING a
        // `by consuming` -- a different edge and a different state. *A theorem about the one
        // edge is not a theorem about the other.*
        pflicht: "Eine erzeugte Mutation, die Kanten HINZUFUEGT (Umhaengen von \
                  Geschwister-/Kindzeigern), erhaelt die Wohlfundiertheit -- und das ist \
                  NICHT durch `wf_subset` gedeckt, sondern je Mutation einzeln zu zeigen. \
                  **Die pauschale Fassung ist widerlegt**, nicht offen.",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "MESSUNGEN.md, ERGEBNIS III (2026-08-16), Befund K-2; B3, Marke Nb2",
    },
    Schablone {
        name: "consuming.leermenge",
        haengt_an: &[],
        konstrukt: "traverse … by consuming",
        // **Maschinell geprueft am 2026-08-16** -- `leermenge` in `beweise/Consuming.thy`,
        // eine Aequivalenz in einer Zeile. Vorhergesagt waren 0--1 ausgespuelte Bedingungen;
        // es wurde eine, und es ist dieselbe wie N-2 bei `table.induktion`:
        //
        //   der ZUSTAND. `Ist sie leer, ist die Domaene leer` nennt keinen -- und in einer
        //   VERBRAUCHENDEN Traversierung ist genau das die Frage: leer WANN? Vor dem Zug
        //   oder nach dem letzten Verbrauch? `leermenge_ist_zustandsabhaengig` zeigt, dass
        //   die zwei Zeitpunkte verschiedene Antworten geben.
        pflicht: "Die erzeugte Zeugenmenge ist VOLLSTAENDIG **an einem genannten Zustand**: \
                  ist sie dort leer, ist die Domaene dort leer. Ohne diese Richtung koennte \
                  eine Traversierung Elemente auslassen und trotzdem terminieren -- sie waere \
                  dann total, aber nicht erschoepfend. **Ohne den genannten Zustand ist der \
                  Satz in einer verbrauchenden Traversierung mehrdeutig.**",
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "der Zustand, an dem die Leerheit behauptet wird, ist GENANNT -- leer WANN?", durch: None, braeuchte: Some("eine Grammatikzeile: `by consuming` nennt keinen Zeitpunkt. Erst die Form, dann der Pass") },
        ],
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "table.ops.erhaltung",
        haengt_an: &[],
        konstrukt: "table … ops",
        // **F-1, Redaktion 2026-08-17.** Alt: *„Je erzeugter Mutation bleibt JEDE
        // `online`-Invariante erhalten."* Zu stark und vom eigenen Ordner widerlegt: eine
        // VERBINDUNGS-Invariante ueber zwei Traegern wird von keiner Operation eines
        // einzelnen Traegers erhalten -- genau deshalb gibt es `gruppe.ops` («B13»). Der
        // Eintrag versprach, was S16 als offen fuehrt.
        pflicht: "Je erzeugter Mutation bleibt jede `online`-Invariante DIESES TRAEGERS \
                  erhalten -- einmal ueber der Deklaration, nicht je Aufrufstelle. \
                  **Invarianten UEBER Traegern sind ausdruecklich nicht gedeckt**; sie sind \
                  `gruppe.ops`.",
        // **Maschinell geprueft am 2026-08-19 -- und der Gegenstand fehlte.**
        //
        // Beim Ansetzen gemessen: `ops` steht an NULL Korpusstellen, und
        // `opdecl = "ops" identlist ";"` nimmt beliebige Bezeichner. **Nirgends stand, WAS
        // eine erzeugte Mutation tut** -- der Satz hatte kein Subjekt. Er ist aus dem Korpus
        // geholt statt erfunden: `beispiele/01-tabelle.gab` schreibt `blatt_loeschen` mit
        // `maintains baum_wohlgeformt`, und `aushaengen` daneben.
        //
        // **Theorem -> line. Redrawn 2026-08-28, evening: Teil II has THREE mutations now,
        // and the counterexample changed its job** (the five-line German map that stood here
        // is a subset of this one):
        //   amortisation ("once per operation")   -> `folge_erhaelt`, `erreichbares_erhaelt`
        //   insert preserves                      -> `einfuegen_erhaelt` (two premises)
        //   remove preserves                      -> `blatt_loeschen_erhaelt`
        //   the parent chain, reflexive           -> `ueber` (inductive: `hier`, `hoeher`)
        //   a chain clear of `s` survives         -> `umhaengen_ausserhalb` (U-1)
        //   a chain THROUGH `s` follows on        -> `umhaengen_durch_s` (U-2)
        //   relabel preserves                     -> `umhaengen_erhaelt` (U-3, two premises)
        //     the same on an occupied slot        -> `umhaengen_erhaelt_am_belegten_platz`
        //   relabel falls WITHOUT the condition   -> `umhaengen_faellt` (COUNTEREXAMPLE)
        //     and it meets the other two premises -> `gegenbeispiel_erfuellt_die_alten` (G-1)
        //     and violates EXACTLY the new one    -> `gegenbeispiel_verletzt_die_neue` (G-2)
        //   connecting invariant not covered      -> `verbindung_nicht_gedeckt`
        //
        // **ENTWORFEN -> GETRAGEN am 2026-08-28, and the first of the three reasons has
        // fallen.** They stood as:
        //
        // 1. ~~`Getragen` would mean *"the compiler rests on it today"* -- it does not: `ops`
        //    has no generator.~~ **It has one since 2026-08-28** (`emit.rs::ops`, cut (c)).
        // 2. `Bewiesen` would mean the duty is discharged. Part I carries the amortisation
        //    only under the hypothesis *"every generated operation preserves I"*, and no pass
        //    establishes it. Part II discharges it for TWO operations BY HAND.
        // 3. **An entry leaves this list only proved or together with its construct.**
        //
        // > **And the generator was cut to the proof, not the other way round:** it emits
        // > exactly `insert` (`einfuegen_erhaelt`) and `remove` (`blatt_loeschen_erhaelt`).
        //
        // **UPDATED 2026-08-28, evening: `relabel` is the THIRD generated operation, and
        // the state stays `Getragen`.** What stood here was *"and it REFUSES `relabel` by
        // naming `umhaengen_faellt`"* -- and the refusal was not wrong, it was incomplete.
        // It said THAT the re-hanging falls, never what it falls ON.
        //
        // > What stood there was the third word of a CLOSED vocabulary that emitted nothing
        // > and nobody could call -- *a clause with no redeemer* (`N037`, `H007`/`H008`), at
        // > 127 measured corpus sites.
        //
        // **The proof came first, as K100's second gate demands** (booked precedent
        // `verbund.konstruktor`: *"the proof came first"*). `umhaengen_erhaelt` (U-3) names
        // the condition -- the re-hung slot is off the new parent's chain, that parent
        // included; `umhaengen_faellt` stays, and `G-1`/`G-2` show it fails at EXACTLY that
        // premise and no other. *The emitted set and the proved set are the same set again
        // -- with three elements now.*
        // `messung/OPS-RELABEL.md` weighs the three forms the condition could have taken in
        // Gabbro.
        //
        // **Why NOT `Bewiesen`:** reason 2 below stands unchanged. Teil II now discharges
        // the hypothesis for THREE operations by hand instead of two -- by hand and on the
        // model it remains.
        //
        // **`L` rises from 1 to 2, and that is the second gate working, not a regression.**
        // A construct that closes plumbing costs trust surface, and K100's whole point is
        // that the shift gets COUNTED. What is still not proved is the step from the Isabelle
        // model to the emitted C -- the same gap `Table_Absenkung.thy` names in its own words
        // ("die Sprachdefinition von C und keine Annahme dieses Beweises").
        stand: Stand::Getragen,
        voraussetzungen: &[
            Voraussetzung { was: "jede ERZEUGTE Operation erhaelt die Invariante -- Teil I ist parametrisch", durch: Some("`emit.rs::ops` (2026-08-28): the generator emits exactly the THREE operations Teil II proves -- `insert` = `einfuegen`, `remove` = `blatt_loeschen`, `relabel` = `umhaengen` -- and refuses an invented word. The emitted set and the proved set are the same set. *`relabel` joined on the evening of that day, and the theorem came first (`umhaengen_erhaelt`, U-3); until then the word emitted nothing and nobody could call it*"), braeuchte: None },
            Voraussetzung { was: "beim Einfuegen ist der Platz FRISCH und der Elter erreichbar", durch: Some("`D012` (2026-08-28, `messung/OPS-RUFFORM.md`): both premises stand at the emitted head and are held against every call site -- `!t.slots[n].<occupied>` and `t.slots[p] reaches <root> via <parent>`. What is NOT established is their TRUTH: a standing `requires` pushes the duty one frame outwards, where `gabbro pflichten` counts it"), braeuchte: None },
            Voraussetzung { was: "beim Loeschen ist der Platz ein BLATT", durch: Some("`D012` demands the theorem's own `blatt sigma s` -- `forall x in slots of t : t.slots[x].<parent> != Some(s)` -- and deliberately NOT the weaker `ist_blatt(c, s)` of beispiele/01, which holds of a slot whose child list has drifted from its parent pointers"), braeuchte: None },
            Voraussetzung { was: "beim Umhaengen ist der NEUE Elter erreichbar und der umgehaengte Platz liegt NICHT auf dessen Elternkette", durch: Some("`D012` (2026-08-28, abends): both premises of `umhaengen_erhaelt` stand at the emitted head and are held against every call site -- `t.slots[p] reaches <root> via <parent>` and `!(t.slots[p] reaches t.slots[s] via <parent>)`. **The second is read in the theorem's REFLEXIVE-transitive shape and in no other**: `ancestors of` is strict, says nothing about `p == s`, and would let the self-loop through (beispiele/gift/332). **And the TARGET of that `reaches` is read strictly**, unlike the root of the first premise: gift/334 writes it about a different slot and falls. A table without a `parent` edge has no `relabel` at all -- `C001`, and gift/333 measures it"), braeuchte: None },
        ],
        fundstelle: "SPRACHE.md §10.2",
    },
    Schablone {
        name: "table.induktion",
        haengt_an: &["table.indexschranke", "consuming.ordnung"],
        // **Maschinell geprueft am 2026-08-16** -- Isabelle2025-2, `beweise/`.
        // Zuordnung Satz -> Zeile (die vorregistrierte Ungueltigkeitsprobe):
        //   N-1  Endlichkeit           -> `im_bereich`, `kante_bleibt_im_bereich`,
        //                                 `traeger_endlich`
        //   N-2  ein Zustand           -> `kante :: tabelle => (idx * idx) set` (Parameter)
        //   N-3  Basisfall absorbiert  -> `blatt_ohne_eigene_klausel`
        //   N-4  zwei Praemissen       -> `kante` als Vereinigung, `table_induktion_zwei_kanten`
        //   Wohlfundiertheit Hypothese -> `assumes wf` in `table_induktion`
        // Umgekehrt: keine Zeile der Formalisierung ohne Satz im Eintrag.
        //
        // **Was NICHT bewiesen ist, und es steht hier statt in einer Fussnote:** dass der
        // ERZEUGER dieses Schema emittiert. Es gibt keinen Erzeuger; die Emissionsflaechen
        // weist `mutiere-pruefer.py` mit 0 Mutationen aus. Bewiesen ist die MATHEMATIK der
        // Schablone, nicht ihre Auslieferung.
        //
        // **Und die zweite Grenze ist unbequemer:** die vier Nebenbedingungen hat die
        // HANDARBEIT ausgespuelt, nicht die Maschine. Der erste Anlauf haette am Pruefer
        // scheitern muessen (ein Vorwaertsverweis auf eine nie definierte Funktion) -- ich
        // habe ihn vorher berichtigt. **Die Maschine hat bestaetigt, nicht entdeckt.**
        // Eine Formalisierung, die nur aufschreibt, was ihr Verfasser ohnehin glaubte, kann
        // nicht mehr ausspuelen als er sah; das faende erst eine UNABHAENGIGE.
        konstrukt: "by induction over <domain>",
        pflicht: "Das aus der `table`-Deklaration erzeugte Induktionsschema ist wohlfundiert \
                  und vollstaendig. **In vier Teilen, die die alte Fassung stillschweigend \
                  trug:** (N-1) die Traegermenge ist ENDLICH, und das faellt NICHT aus dieser \
                  Deklaration, sondern aus `table.indexschranke`; (N-2) das Prinzip gilt fuer \
                  EINEN Zustand -- ueber eine mutierende Traversierung sagt es NICHTS, das ist \
                  `consuming.ordnung`; (N-3) eine eigene Leere-Menge-Klausel braucht es NICHT, \
                  der Basisfall ist absorbiert; (N-4) fuer `chain(a,b) in` hat die Domaene \
                  ZWEI Kantenarten und das Schema braucht ZWEI Praemissen. \
                  **Wohlfundiertheit ist HYPOTHESE, nicht Ergebnis** -- die Deklaration muss \
                  die tragende Invariante nennen (`invariant acyclic`).",
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "die Traegermenge ist endlich: die Verkettungsfelder bleiben in der Tabelle", durch: Some("M103, ueber `table.indexschranke`"), braeuchte: None },
            Voraussetzung { was: "je Verkettungsfeld eine Kantenpraemisse -- der Erzeuger schreibt ZWEI, nicht eine", durch: None, braeuchte: Some("ein Erzeuger fuer das Induktionsschema; ersatzweise eine Regel, die `chain(a,b)` gegen die Zahl der Kantenpraemissen haelt") },
        ],
        fundstelle: "SYNTAX.md §5, SPRACHE.md Teil V",
    },
    Schablone {
        name: "transition.transset",
        haengt_an: &[],
        konstrukt: "transition { a: … , b: … }",
        // **F-1, Redaktion 2026-08-17.** Alt: *„KEIN Zwischenzustand ist beobachtbar."*
        // Beobachtbar **von wem**? Auf einem Mehrkerner sieht ein fremder Kern ihn, sofern
        // nicht eine Sperre oder Atomaritaet ihn deckt. Der Satz war absolut und liess
        // seinen Beobachter weg -- dieselbe Luecke wie N-2 bei `table.induktion`.
        //
        // **The form is not what is missing here** (measured 2026-08-28, W24). `transset`
        // has carried several places since the first day (`SYNTAX.md`:1256), the parser has
        // the comma loop, and `beispiele/02-geraet.gab`:42 uses it. `PFLICHTEN.md` read the
        // opposite twice («B17», *"`transition` writes exactly ONE `place`"*) and was wrong
        // on that for eleven days.
        //
        // > **And this template is the reason the row could not simply be built shut.** The
        // > promise above needs an OBSERVER, and at two slot fields of a table there is
        // > none: the lowering would be two `store`. So the site went to the form that
        // > promises the opposite and can keep it -- `breaking I { … }` names the region
        // > instead of denying it, and the held lock names who does not see it.
        // > *This template therefore stays `Entworfen`, deliberately* (K100's second gate),
        // > and it carries no `Voraussetzung`: a premise entry counts in tooth 3, which
        // > measures proofs nothing establishes -- this one establishes nothing and proves
        // > nothing either. The weighing: `messung/ZWEI-ORTE.md`.
        pflicht: "Mehrere Orte in EINEM Zug: kein Zwischenzustand ist beobachtbar **fuer \
                  einen benannten Beobachter** -- auf einem Kern der Kontrollfluss, auf \
                  mehreren jeder Kern, der die Sperre des Zuges nicht haelt. **Ohne \
                  benannten Beobachter ist die Zusage auf einem Mehrkerner leer.**",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "SYNTAX.md §10",
    },
    Schablone {
        name: "exchange.rmw",
        haengt_an: &[],
        konstrukt: "exchange update(v) { … } / … when … returns",
        // **F-4, Redaktion 2026-08-17.** Zwei Haelften in einem Satz, und sie gehoeren
        // verschiedenen Flaechen: die REINHEIT ist mechanisch pruefbar (Pass 8), die
        // ATOMARITAET ist eine Aussage ueber das Speichermodell und faellt in die
        // Axiomschicht -- `paarung.rs` sagt dasselbe ueber `release`/`acquire`.
        pflicht: "Der Rumpf von `update(v)` ist rein (mechanisch, Pass 8). **Die \
                  Atomaritaet der Lese-Aendere-Schreibe-Folge ist KEINE Schablonenpflicht, \
                  sondern eine Annahme der Axiomschicht** -- sie steht dort und nicht hier.",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "SPRACHE.md Teil III §1",
    },
    Schablone {
        name: "accumulates.monoid",
        haengt_an: &[],
        konstrukt: "accumulates … merge",
        // **F-1 UND F-4, Redaktion 2026-08-17.** Zwei Haelften (Monoid: pruefbar;
        // Absenkung: redet ueber die Emission, die es nicht gibt) -- und die zweite ist
        // falsch, wie sie dasteht: ein NEBENLAEUFIGES Lesen einer je-Kern-Zelle liefert
        // nicht denselben Wert wie ein atomares RMW, nur an einem Ruhepunkt.
        pflicht: "Die Merge-Menge ist ein kommutatives Monoid (mechanisch pruefbar). \
                  **Die Absenkung ergibt denselben Wert wie ein atomares RMW nur an einem \
                  RUHEPUNKT** -- nebenlaeufig gelesen tut sie es nicht, und das ist keine \
                  Ungenauigkeit, sondern der Preis der Absenkung. *Die Emissionshaelfte \
                  wartet auf einen Erzeuger.* **Maschinell geprueft:** die Faltung ist \
                  reihenfolgeunabhaengig (`faltung_ist_reihenfolgeunabhaengig`) und stimmt \
                  am Ruhepunkt mit der atomaren RMW-Kette ueberein \
                  (`am_ruhepunkt_gleich_dem_atomaren_rmw`); je Verknuepfung steht die \
                  Instanz da -- **und `min` hat als Neutrales das MAXIMUM des Typs, nicht \
                  die Null** (`min_ist_monoid_mit_top`).",
        // **Maschinell geprueft am 2026-08-17** (`beweise/Accumulates_Monoid.thy`, K11.3.2)
        // -- und zwar VOR dem Konstrukt, wie das zweite Tor es verlangt.
        //
        // *Ausgespuelt: `min` mit `0` als Startwert zieht jedes Ergebnis auf null.* Eine
        // Falle, die der Eintrag nicht nannte und die beim Nachweis der Instanzen abfiel --
        // ueber `nat` gibt es kein Neutrales fuer `min`, ueber einem Maschinenwort schon.
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            // **Praezisiert 2026-08-18.** Die Praemisse lautete "die Verknuepfung stammt aus
            // max/min/add/or/and", hergestellt vom geschlossenen Wortschatz. Das ist die
            // halbe Wahrheit: der Wortschatz reicht nur, WEIL alle Zahlentypen ganzzahlig
            // sind. Ueber `f64` waere `add` nicht assoziativ und `max` mit NaN kein Verband
            // -- `faltung_ist_reihenfolgeunabhaengig` verlangt beides.
            //
            // *Der Satz bliebe wahr und seine Praemisse wuerde falsch* -- genau die Bewegung,
            // gegen die Zahn 3 steht.
            Voraussetzung { was: "die Verknuepfung stammt aus max/min/add/or/and", durch: Some("der geschlossene Wortschatz: `MergeOp` laesst nichts anderes zu"), braeuchte: None },
            Voraussetzung { was: "und alle Zahlentypen sind GANZZAHLIG -- sonst ist `add` nicht assoziativ", durch: Some("es gibt keinen Gleitkommatyp (MEMO-GLEITKOMMA.md); mit einem muesste `merge` mechanisch einschraenken"), braeuchte: None },
            Voraussetzung { was: "je Kern eine Zelle, mit dem richtigen Neutralen angelegt", durch: Some("Mutationsprobe `min-akkumulator-ohne-umkehr`, Einheit `beispiel23`"), braeuchte: None },
            Voraussetzung { was: "der RUHEPUNKT -- kein Kern schreibt mehr, waehrend gefaltet wird", durch: None, braeuchte: Some("die AUSFUEHRUNGSKONTEXTE (K11.2.2) -- ohne sie sagt Gabbro nicht, wer nebenlaeufig laeuft, und keine Regel kann den Ruhepunkt feststellen") },
        ],
        fundstelle: "SPRACHE.md §11.4; beweise/Accumulates_Monoid.thy",
    },
    Schablone {
        name: "walk.mappings",
        haengt_an: &[],
        konstrukt: "walk … levels / mappings of",
        // **F-1, Redaktion 2026-08-17.** *„trifft GENAU die erreichbaren Blatteintraege"*
        // -- dieselbe Form wie das widerlegte *„deckt genau die belegten Slots"* bei S12,
        // und aus demselben Grund verdaechtig: eine grosse Seite ist ein Mapping an einem
        // Eintrag, der KEIN Blatt der vollen Tiefe ist.
        pflicht: "Die erzeugte Domaene `mappings of` trifft jeden erreichbaren Eintrag, \
                  der eine Abbildung TRAEGT -- samt va und level. **Das ist nicht dasselbe \
                  wie `Blatteintrag`:** eine grosse Seite bildet oberhalb der vollen Tiefe \
                  ab. *Ob die Domaene sie heute trifft, ist ungeprueft.*",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "SPRACHE.md §5.4, §6",
    },
    Schablone {
        name: "format.roundtrip",
        haengt_an: &[],
        konstrukt: "format",
        // **F-1 UND F-4, Redaktion 2026-08-17.** *„genau einmal am Eintritt"* ist fuer
        // VARIABLE Laengen falsch -- und genau die sind ein offener Posten der Sprache. Dazu
        // zwei Pflichten in einem Satz.
        pflicht: "(1) `lesen(schreiben(x)) == x` fuer jedes darstellbare x. (2) Der Leser \
                  prueft die Pufferlaenge einmal am Eintritt -- **das gilt nur fuer FESTE \
                  Laengen.** Bei variablen faellt die Schranke erst aus dem Inhalt, und dann \
                  ist je Feld zu pruefen. *Solange variable Laengen offen sind, deckt diese \
                  Schablone nur den festen Fall.*",
        // **Getragen seit 2026-08-17** fuer den byteweisen Fall: `emit.rs` erzeugt Zugriffe in
        // der erklaerten Bytereihenfolge plus eine Gueltigkeitsfunktion aus den
        // `where`-Klauseln. Bitlagen bleiben abgelehnt («B24»).
        //
        // **Maschinell geprueft am 2026-08-17** (`beweise/Format_Roundtrip.thy`, K11.3.2).
        // *Ausgespuelt hat der Beweis eine dritte Haelfte, die der Eintrag nicht nannte:* die
        // Rundreise je Feld ist wertlos, solange nicht dasteht, dass ein Schreiben in das eine
        // das andere nicht zerstoert (`schreiben_stoert_getrennte_felder_nicht`) -- **und
        // genau das ist die Stelle, an der ein Erzeuger zwei Versaetze ueberlappen laesst.**
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "der geschriebene Wert passt in die deklarierte Breite", durch: Some("M101 (m1.rs)"), braeuchte: None },
            Voraussetzung { was: "die Felder liegen GETRENNT (`trennt f g`)", durch: Some("die Lage selbst, `bitlage::lies` -- je Feld ohne Bitlage ein eigenes Wort, je Bitgruppe eines, und der Versatz waechst monoton. Zwei Felder koennen nur INNERHALB einer Gruppe kollidieren, und dort haelt `N008`"), braeuchte: None },
        ],
        fundstelle: "SPRACHE.md §10.1; beweise/Format_Roundtrip.thy",
    },
    Schablone {
        name: "entry.abdruck",
        haengt_an: &[],
        konstrukt: "entry … dispatch",
        // **F-4, Redaktion 2026-08-17.** Drei Pflichten in einem Satz, und die dritte ist
        // ein undefinierter Begriff: *„der Stapelwechsel ist KORREKT"* -- korrekt WOGEGEN?
        // Eine Beweispflicht mit unbestimmtem Praedikat ist keine.
        pflicht: "(1) Der erzeugte Eintrittspfad erhaelt jedes Register aus `preserves`. \
                  (2) Er schreibt kein Register ausserhalb von `clobbers`. (3) **Der \
                  Stapelwechsel ist NOCH KEINE Pflicht, sondern ein unbestimmtes Wort** -- \
                  `korrekt` ist nirgends definiert; die Pflicht ist erst formulierbar, wenn \
                  eine Stapelinvariante dasteht. **Kein nachgelagerter Beweiser** -- das \
                  Vertrauen schrumpft auf eine Stelle, es verschwindet nicht.",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "SPRACHE.md Teil II §2",
    },
    Schablone {
        name: "device.konstruktor",
        haengt_an: &[],
        konstrukt: "device D(params) at space",
        // **F-4, Redaktion 2026-08-17.** Zwei Haelften, und die zweite ist in KEINEM
        // Beweiser zeigbar: *„die Registerlagen treffen die Hardware-Lagen"* ist eine
        // Aussage ueber ein physisches Geraet. Eine Schablone, die eine Hardwareannahme
        // fuehrt, macht sie beweisbar aussehen.
        pflicht: "Aus der Adresse entsteht ein typisierter Griff, und die erzeugten \
                  Zugriffe treffen die im `device`-Block DEKLARIERTEN Lagen. **Dass die \
                  deklarierten Lagen die des Geraets sind, ist eine ANNAHME der \
                  Axiomschicht** und wird hier nicht gezeigt. **Was bleibt, ist die \
                  RECHNUNG**, und sie ist maschinell geprueft: getrennte Register treffen \
                  getrennte Zellen, und zwar FUER JEDE BASIS \
                  (`trennung_haengt_nicht_an_der_basis` -- deshalb darf der Griff der \
                  Konstruktor sein); Bankeintraege ueberlappen nicht \
                  (`bankeintraege_ueberlappen_nicht`).",
        // **Maschinell geprueft am 2026-08-17** (`beweise/Device_Konstruktor.thy`, K11.3.2).
        // Der Beweis darf kurz sein, und der Eintrag sagt warum: *„stimmt 0x18 fuer GCMD?"*
        // ist keine Frage an ein Beweissystem, sondern an ein Datenblatt -- sie steht als
        // Annahme mit Sonde im Manifest.
        //
        // **Und er spuelte einen Posten aus:** eine `bank` mit `stride 0` erzeugt LEERE
        // Zellen, der Satz gilt trivial, und der Erzeuger sollte sie ablehnen statt sie
        // leerlaufen zu lassen. *Richtig und nutzlos ist keine bestandene Pruefung.*
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "zwei `reg` haben getrennte Lagen (`getrennt r s`)", durch: Some("N009, seit 2026-08-19 -- die Byte-Bereiche zweier Register ueberlappen nicht"), braeuchte: None },
            Voraussetzung { was: "`stride` ist nicht null -- sonst ist jede Bankzelle leer", durch: Some("N010, seit 2026-08-19 -- `stride 0` faellt am Pass statt im Kommentar"), braeuchte: None },
            Voraussetzung { was: "die deklarierten Lagen sind die des Geraets", durch: Some("Axiomschicht: `assume` mit Falsifikator, `gabbro annahmen`"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, Der Ursprung, 2026-08-14; beweise/Device_Konstruktor.thy",
    },
    Schablone {
        name: "table.indexschranke",
        haengt_an: &[],
        konstrukt: "table … count N / index into T",
        // **Berichtigt und maschinell geprueft am 2026-08-16** (`beweise/Table_Indexschranke.thy`).
        // Die alte Fassung lautete: *„Der erzeugte Indextyp `0 ..< N` deckt genau die
        // belegten Slots, und die Absenkung legt N Slots an."* Davon war der erste Halbsatz
        // **falsch** und der zweite gehoert nicht hierher:
        //
        //   M-1  `deckt genau die belegten Slots` ist WIDERLEGT -- eine Tabelle mit
        //        `count 80256` und drei belegten Slots hat einen Indextyp mit 80256 Werten.
        //        Gegenbeispiel: `indextyp_deckt_nicht_nur_belegte`.
        //   M-2  der GEHALT liegt woanders: nicht im Typ, sondern in den SCHREIBSTELLEN --
        //        jede erzeugte Schreibstelle bleibt im Typ (`schreibstellen_im_typ`). Genau
        //        diese Haelfte braucht `table.induktion`, und sie stand nirgends.
        //   M-3  `die Absenkung legt N Slots an` ist eine Aussage ueber die EMISSION. Es gibt
        //        keinen Erzeuger -> eigener Eintrag `table.absenkung`.
        pflicht: "Der erzeugte Indextyp ist `{i. i < N}` -- er ENTHAELT jeden belegten Slot \
                  (`belegt_liegt_im_indextyp`) und deckt ihn NICHT genau: ein Index im Typ \
                  muss nicht belegt sein. Und die tragende Haelfte ist die ueber den \
                  SCHREIBSTELLEN: jedes erzeugte Verkettungsfeld eines belegten Slots zeigt \
                  in den Typ (`schreibstellen_im_typ`, `kette_bleibt_im_typ`). Daraus faellt \
                  `im_bereich` fuer `table.induktion` (`im_bereich_folgt_aus_indexschranke`).",
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "jede erzeugte Schreibstelle bleibt im Typ (`schreibstellen_im_typ`)", durch: Some("M103 (m1.rs)"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, A3, 2026-08-14",
    },
    Schablone {
        name: "table.absenkung",
        haengt_an: &["table.indexschranke"],
        konstrukt: "table … count N (Emission)",
        // **Abgespalten am 2026-08-16.** Der Satz stand in `table.indexschranke` und ist dort
        // nicht beweisbar: er redet ueber den ERZEUGTEN C-Code, und einen Erzeuger gibt es
        // nicht (`mutiere-pruefer.py`: 0 Mutationen auf der Emissionsflaeche).
        //
        // *Die Abspaltung VERGROESSERT das Register, und das ist der ehrliche Preis: eine
        // Zusage, die zur Haelfte beweisbar und zur Haelfte ueber einem Nichts ist, war als
        // EIN Eintrag zu klein gebucht.*
        pflicht: "Die Absenkung legt genau N Slots an -- nicht weniger (dann waere ein \
                  Index im Typ ohne Speicher, `zu_kurz_laesst_einen_index_ohne_speicher`) \
                  und nicht mehr (dann waere Speicher ohne Index, \
                  `zu_lang_laesst_speicher_ohne_index`). **Und der Gehalt liegt eine Stufe \
                  weiter:** aus `m = N` und der Indexschranke faellt, dass KEIN Zugriff des \
                  erzeugten Programms aus dem Feld laeuft \
                  (`kein_zugriff_laeuft_aus_dem_feld`) -- erst das ist die Aussage, um \
                  derentwillen die Absenkung ein festes Feld nimmt und keinen Zeiger mit \
                  Laenge. **OFFEN bleibt, dass der ERZEUGER `m = N` herstellt** -- eine \
                  Aussage ueber `emit.rs`, und sie faellt in die Bruecke (PL.3): eine \
                  Mutation, die die Feldlaenge von der Kapazitaet loest, muss fallen.",
        // **Getragen seit 2026-08-17**: `emit.rs` senkt eine `table … count N` zu einem festen
        // C-Feld ab, und `pruefe-emission.sh` misst es an der Ausfuehrung. *Damit ist dieser
        // Satz keine Zusage ueber einen kuenftigen Erzeuger mehr -- der Uebersetzer stuetzt
        // sich JETZT darauf.*
        // **Maschinell geprueft 2026-08-17** (`beweise/Table_Absenkung.thy`, K11.3.2) -- der
        // erste der vier LEBEND getragenen Saetze, und der, auf dem die anderen aufsitzen:
        // `option.sonderwert` braucht die Laenge fuer den Sonderwert, `table.induktion` die
        // Schranke fuer die Terminierung.
        //
        // > *`lebend_ungedeckt()` faellt damit von 4 auf 3* -- und das ist die einzige Zahl
        // > dieses Ordners, die kleiner zu werden ETWAS kostet.
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "jeder Index liegt im Typ (`i : indextyp N`)", durch: Some("M103 (m1.rs)"), braeuchte: None },
            Voraussetzung { was: "`count N` steht da -- sonst haette das Feld keine Groesse", durch: Some("C001, emit.rs:938"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, ERGEBNIS III (2026-08-16), Befund M-3; \
                     beweise/Table_Absenkung.thy",
    },
    // ---- Kandidaten aus der Nachpruefung vom 2026-08-14. Noch kein Konstrukt, aber die
    // ---- Pflicht steht schon fest -- und genau das ist der Punkt dieser Liste.
    Schablone {
        name: "ops.suche",
        haengt_an: &[],
        konstrukt: "ops finde … (Kandidat, aus «B10»)",
        // **F-2, Redaktion 2026-08-17.** *„die Ordnung der Domaene"* -- Singular, und
        // fuer `chain(a,b) in` gibt es keine: die Domaene hat ZWEI Kantenarten (N-4 bei S4),
        // also keinen kanonischen ERSTEN Treffer ohne zusaetzliche Festlegung.
        pflicht: "Die erzeugte Suche gibt den ersten Treffer in einer **erzeugten, \
                  benannten Aufzaehlungsreihenfolge** und laesst die Menge unveraendert. \
                  **Fuer Domaenen mit mehreren Kantenarten (`chain(a,b) in`) ist diese \
                  Reihenfolge zusaetzlich festzulegen** -- sie faellt nicht aus der Domaene.",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "state.reset",
        haengt_an: &[],
        konstrukt: "erzeugtes reset (Kandidat, aus «B26»)",
        // **F-1, Redaktion 2026-08-17.** *„gilt aus JEDEM Zustand"* -- falsch, sobald
        // lineare Werte im Spiel sind: ein `reset` aus einem Zustand, der einen linearen
        // Wert haelt, LECKT ihn, und M2 verbietet genau das. Der Eintrag versprach eine
        // Totalitaet, die die Sprache an anderer Stelle ausschliesst.
        pflicht: "Der erzeugte Uebergang in den Anfangszustand gilt aus jedem Zustand, \
                  **in dem kein linearer Wert gehalten wird**, und ist selbst ein \
                  `transset`. *Aus einem Zustand mit gehaltenem linearem Wert ist er ein \
                  Leck und muss abgelehnt werden -- M2, nicht diese Schablone.*",
        stand: Stand::Entworfen,
        voraussetzungen: &[],
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "verbund.konstruktor",
        haengt_an: &[],
        konstrukt: "P(a: …, b: …) -- der markierte Ruf (Absenkung)",
        // **Maschinell geprueft 2026-08-17** (`beweise/Verbund_Konstruktor.thy`), und zwar
        // VOR dem Konstrukt: das Verbundliteral («B7») zu bauen haette diesen Eintrag von
        // `Entworfen` auf `Getragen` gehoben und damit `L` auf 5 -- das Tor aus K100.
        //
        // **Ausgespuelt (M-1):** die zwei Haelften des Satzes sind EINE, sobald die
        // Deklaration wohlgeformt ist. Und der Gehalt liegt eine Stufe weiter, als der
        // Eintrag sagte: nicht *„jedes Feld gesetzt"*, sondern **die Ablesung ist eindeutig**.
        pflicht: "UNTER `distinct fs`: wenn die Zuordnungsliste des Konstruktors genau die \
                  Feldliste als Schluesselfolge hat (`map fst zs = fs`), ist jedes Feld genau \
                  einmal gesetzt UND keins uninitialisiert -- die beiden Haelften fallen \
                  zusammen. **Und die Ablesung ist eindeutig**: `liest zs f = Some v` fuer \
                  genau den Wert, den der Konstruktor dort hingeschrieben hat \
                  (`ablesung_ist_eindeutig`, `jedes_feld_hat_einen_wert`). **OFFEN bleibt, \
                  dass der ERZEUGER `deckt` herstellt** -- das ist eine Aussage ueber \
                  `emit.rs`, und sie faellt in die Bruecke (PLAN.md, PL.3): eine Mutation, \
                  die ein Feld doppelt oder gar nicht setzt, muss fallen. **Sie steht seit \
                  dem 2026-08-17 da** (`verbundmarken-nur-als-menge`, \
                  `verbund-ohne-marken-geht-durch`) -- die erste beschaedigt genau die \
                  Reihenfolgefassung, die der Beweis gegen die Mengenfassung gewaehlt hat.",
        // **Getragen seit dem 2026-08-17**, seit «B7» gebaut ist: `m1::marken_pruefen`
        // stellt `deckt` her, und `emit::ruf` senkt es zu benannten Bestimmern ab. Der
        // Beweis lag VORHER -- so verlangt es das zweite Tor von K100, und deshalb bewegt
        // dieser Schritt `lebend_ungedeckt()` nicht.
        stand: Stand::Bewiesen,
        voraussetzungen: &[
            Voraussetzung { was: "`deckt`: die Zuordnung hat genau die Feldliste als Schluesselfolge", durch: Some("M106/M107"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung; beweise/Verbund_Konstruktor.thy; \
                     m1.rs::marken_pruefen; emit.rs::verbund",
    },
    Schablone {
        name: "gruppe.ops",
        haengt_an: &["gruppe.sperrabdruck"],
        konstrukt: "Gruppen-ops ueber mehreren Tabellen (Kandidat, aus «B13»)",
        // **F-4, Redaktion 2026-08-17.** Der Eintrag fuehrt ZWEI Pflichten: die ERHALTUNG
        // der Invariante und den SPERRABDRUCK, unter dem sie gilt. Seit dem 2026-08-16 hat
        // der Abdruck einen eigenen Eintrag (`gruppe.sperrabdruck`, S17) mit drei benannten
        // Teilen -- und damit steht er hier ein zweites Mal. *Zwei Eintraege, die dieselbe
        // Pflicht fuehren, sind dieselbe Fehlerklasse wie zwei Zahlen ueber verschiedenen
        // Grundgesamtheiten: keiner von beiden kann fallen, ohne dass der andere so aussieht,
        // als trage er weiter.*
        pflicht: "Die Verbindungs-Invariante der Gruppe bleibt unter jeder Gruppenoperation \
                  erhalten. **Der Sperrabdruck, unter dem das gilt, steht NICHT hier, \
                  sondern in `gruppe.sperrabdruck`** -- diese Schablone setzt ihn voraus. Auf einem Mehrkerner ist das die eigentliche Pflicht. \
                  **Diese Schablone hat als einzige eine VORLAGE statt eines leeren Blatts**: \
                  Verification/capability-system/proofs/cap_space.rs fuehrt cap_inv als EINE \
                  spec fn ueber den Klauseln 1-7 und beweist je Operation die Erhaltung ALLER \
                  zugleich -- die Schablone haette das zu ERZEUGEN statt zu erfinden. \
                  ABER: die Vorlage fuehrt refcount als `nat`. Sie beweist die Vorbedingung \
                  `oldrc >= 1` (Zeile 792) aus der Invariante -- richtig, aber es ist EIN \
                  Netz. Gabbros `u32 in 0 ..= NSLOTS` gibt ein zweites, das ohne die \
                  Invariante haelt. Uebernommen wird die KLAUSELSTRUKTUR, nicht der TYP; \
                  sonst sieht die Pflichtliste vollstaendig aus, waehrend das zweite Netz \
                  fehlt -- und eine Emission koennte die Bereichspruefung weglassen, WEIL \
                  der Beweis sagt, es koenne nicht negativ werden.",
        // **Maschinell geprueft am 2026-08-19** (`beweise/Gruppe_Erhaltung.thy`), und zwar
        // an dem Tag, an dem `Table_Ops_Erhaltung.thy` `verbindung_nicht_gedeckt` bewies:
        // eine Operation erhaelt jede Invariante IHRES Traegers und bricht die verbindende.
        // *Damit war `gruppe.ops` nicht mehr eine Bequemlichkeit, sondern notwendig -- und
        // die Frage nicht mehr ob, sondern unter welcher Bedingung.*
        //
        // Zuordnung Satz -> Zeile:
        //   die Invariante gilt, wo sie BEOBACHTET werden kann  -> `beobachtbares_gilt`
        //   der Zwischenzustand ist erlaubt, weil unsichtbar    -> dasselbe (Locale `zug`)
        //
        // **Und der Stand bleibt ENTWORFEN**, aus demselben Grund wie bei
        // `table.ops.erhaltung`: es gibt keine Gruppen-`ops`. `U001`-`U007` pruefen die
        // FORM, in der die Frage gestellt werden kann, nicht die Erhaltung.
        stand: Stand::Entworfen,
        voraussetzungen: &[
            Voraussetzung { was: "der Sperrabdruck steht ueber dem ganzen Zwischenzustand (`abdruck_innen`)", durch: Some("gruppe.sperrabdruck, und im Pass U001-U005"), braeuchte: None },
            // **Eingeloest am 2026-08-21.** Die Adresse lautete *„braeuchte: die
            // AXIOMSCHICHT"*, und sie ist jetzt bezogen: `manifest.rs::sperrabdruckannahme`
            // erzeugt `sperrabdruck_haelt_fremde_kerne_fern`, sobald eine `group` im Baum
            // steht -- NICHT FALSIFIZIERBAR mit Grund, wie `release_stellt_sichtbarkeit_her`.
            //
            // *Ein Pass stellt sie nicht her und kann es nicht: ein Speichermodell ist
            // keine Aussage ueber Zustaende.* Was sich geaendert hat, ist, dass ein Leser
            // des Beweises sie SIEHT, statt sie zu unterstellen -- `Gruppe_Erhaltung.thy`
            // nennt sie beim Namen, und sie steht in der Annahmenmenge des Erzeugnisses.
            Voraussetzung { was: "ein gehaltener Abdruck haelt einen fremden Kern wirklich fern", durch: Some("die AXIOMSCHICHT: `sperrabdruck_haelt_fremde_kerne_fern`, nicht falsifizierbar mit Grund (manifest.rs)"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, Papiertest CapSpace/CDT, 2026-08-14",
    },
    Schablone {
        name: "gruppe.sperrabdruck",
        haengt_an: &[],
        konstrukt: "Gruppen-ops ueber Traegern MIT VERSCHIEDENEN SPERREN (aus «B41»-Sweep)",
        // **Warum das eine ZWEITE Schablone ist und kein Zusatz zur ersten.**
        //
        // Der Sweep vom 2026-08-16 hat vier Verbindungs-Invarianten gefunden, und drei davon
        // (V1 refcount, V2 Spendenkanten, V3 queued gegen Bereitliste) liegen unter EINER
        // Sperre. `gruppe.ops` deckt sie. **V4 nicht:** die Endpoint-Warteschlange steht
        // unter `EPS[i]`, der Thread-Zustand unter `SCHEDS[core]` -- zwei Klassen, zwei
        // Kisten, eine deklarierte Ordnung.
        //
        // Eine Schablone, die beide Faelle als einen fuehrt, versteckt genau den Unterschied,
        // an dem sie scheitern kann: unter einer Sperre ist die Erhaltung ein sequenzielles
        // Argument, unter zweien haengt sie an der ORDNUNG und daran, dass zwischen den zwei
        // Nahmen kein fremder Schreiber dazwischenkommt.
        pflicht: "Die Gruppenoperation nimmt ALLE Sperren ihrer Traeger, in aufsteigender \
                  `rank`-Ordnung, und haelt sie ueber den ganzen Zug. Der Erzeuger beweist: \
                  (a) die Reihenfolge ist die deklarierte -- sonst ist die Deadlockfreiheit \
                  des Bestands verloren, nicht bloss die Invariante; (b) die \
                  Verbindungs-Invariante gilt am ANFANG und am ENDE des Zuges, NICHT \
                  zwischendrin -- der Zwischenzustand ist genau der Grund, warum es eine \
                  Gruppenoperation gibt; (c) kein Zwischenaustritt (`return`, `leave`, \
                  Fehlerpfad) verlaesst den Zug im Zwischenzustand. \
                  **Der Bestand traegt (a) heute von Hand:** caprock-microkit/src/lib.rs:1303 \
                  ist ein Kommentar, der erklaert, warum eine Funktion dort steht, wo sie \
                  steht -- naehme sie `EPS` unter `SCHEDS`, drehte sie die Ordnung um. \
                  *Eine Gruppe mit deklariertem Abdruck haette diesen Kommentar ueberfluessig \
                  gemacht; das ist der gemessene Bedarf, nicht ein Entwurfswunsch.*",
        // **Maschinell geprueft am 2026-08-19** (`beweise/Gruppe_Erhaltung.thy`). Die drei
        // benannten Teile der Pflicht sind drei Saetze geworden:
        //
        //   (a) die Reihenfolge      -> `rangordnung_azyklisch` und, als Gegenrichtung,
        //                               `eine_kante_gegen_die_ordnung_reicht`
        //   (b) Anfang und Ende      -> `beobachtbares_gilt` (Locale `zug`)
        //   (c) kein Zwischenaustritt-> `abgebrochener_ist_kein_zug` -- GEGENBEISPIEL
        //
        // **Und (a) traegt mehr als die Invariante**, wie der Eintrag selbst sagt: die
        // Wartekanten liegen in `less_than`, also ist der Wartegraph wohlfundiert und damit
        // azyklisch. *Eine einzige Kante gegen die Ordnung genuegt fuer einen Zyklus, und
        // auch das steht als Satz da statt als Warnung.*
        //
        // **Der eigentliche Fund ist S20s Existenzgrund, formal:** `halber_abdruck_ist_kein_zug`.
        // Unter EINER Sperre steht der Abdruck ab dem ersten Nehmen; unter ZWEIEN steht er
        // zwischen den beiden Nahmen NICHT, und dann laesst sich das Locale nicht erfuellen
        // -- nicht weil der Beweis schwerer waere, sondern weil die Voraussetzung falsch ist.
        //
        // Stand bleibt ENTWORFEN: es gibt keine Gruppen-`ops`.
        stand: Stand::Entworfen,
        voraussetzungen: &[
            Voraussetzung { was: "jeder Teilnehmer nimmt in aufsteigender `rank`-Ordnung -- sonst ist der Wartegraph nicht in `less_than`", durch: Some("U003/U005 im Gruppenpass, und H006 an der Sperrordnung"), braeuchte: None },
            Voraussetzung { was: "kein Zwischenaustritt verlaesst den Zug im Zwischenzustand", durch: Some("U006 -- der Zug hat keinen Zwischenaustritt"), braeuchte: None },
        ],
        fundstelle: "MESSUNGEN.md, SWEEP der Verbindungs-Invarianten, 2026-08-16 (V4)",
    },
];

// ===========================================================================================
// A THEORY WITH NO ENTRY, AND WHY -- `beweise/Table_Zaehlung.thy` (2026-08-28)
//
// **It is recorded here rather than only in `beweise/`, because a proof this register does
// not name grows the trust surface unseen** -- which is what `instrumente/zaehle-theorien.py`
// counts. This note is not a template: it takes no seat, binds no premise, and nothing rests
// on it.
//
// WHAT IT PROVES. That a generated counting loop delivers the cardinality of the hit set
// below the bound (`zaehle_ist_kardinalitaet`), that it is bounded by it (`zaehle_beschraenkt`
// -- what `M104` in the checker needs at a counter field), and the PRESERVATION question: a mutation
// one slot from `a` to `b` lowers the count of `a` by exactly one, raises that of `b` by
// exactly one, and leaves every other untouched -- so `buchfuehrung_erhaelt` lets a generator
// write a decrement and an increment instead of two loops. Two boundaries stand as
// counterexamples: without `s0 < n` the preservation FALLS, and the count says nothing about
// occupancy.
//
// WHY IT HAS NO ENTRY, AND THE REASON IS THE RATCHETS AT WORK.
//
// K100's second gate wants the proof before a template is carried -- satisfied. **Tooth 3
// wants a PROVED template to bind every premise to a pass**, and of the three premises of
// `buchfuehrung_erhaelt` only one is bindable: `s0 < n`, see `M103` in the checker, through
// `table.indexschranke`). The other two -- that the mutation really writes a different object
// (`b != a`), and the cost rule -- would be redeemed by a GENERATOR, and `count(x in domain :
// pred)` has none: `messung/AGGREGATION.md` §4 refuses the construct.
//
// An entry carrying those two would have raised tooth 3 from 6 to 8, and a ratchet whose mark
// one lifts when it binds is none. Writing them out of the entry would have been the quiet
// weakening tooth 3 exists against -- *with an unread clause nobody knows anything; there one
// would know something false.*
//
// > **Hence the finding, and it stood nowhere before: a template for a construct with no
// > generator is not registrable as PROVED** -- not because the proof is missing, but because
// > the premises a generator would redeem belong to nobody without one.
//
// `messung/AGGREGATION.md` §6 measures it and carries the commands.
// ===========================================================================================

/// **DIE MARKE — der zweite Zahn der Ratsche, seit 2026-08-16.**
///
/// Bis heute hatte dieses Register **einen Zaehler und sonst nichts**. Der Wortschatz hat
/// seine Ratsche (189 gegen 189), die Axiomschicht ihre Klassen mit Falsifikatorpflicht, die
/// Kennzahl ihre Latte — **die Schablonen hatten keine Abbruchbedingung.** Und ohne sie ist
/// die ehrlichste Beschreibung des Projektstands unangenehm:
///
/// > Eine Sprache, deren Syntax konvergiert, deren Beweise aber vollstaendig in eine Flaeche
/// > delegiert sind, die **monoton waechst** — strukturell dieselbe Kurve wie seL4s
/// > Beweisberg, nur dass sie Schablonenliste heisst und noch niemand angefangen hat, sie
/// > abzutragen.
///
/// **Der Unterschied zum Beweisberg ist einzig das Amortisierungsargument** (eine Schablone
/// faellt EINMAL, nicht je Programm) — **und das gilt erst ab der ersten BEWIESENEN
/// Schablone.** Bis dahin ist es eine Zusage ueber eine Flaeche, die niemand betreten hat.
///
/// Deshalb die Marke: **solange KEINE einzige Schablone bewiesen ist, darf das Register
/// achtzehn nicht ueberschreiten.** Die Zahl ist nicht heilig — sie ist die heutige plus
/// eins, also *ein* weiterer Eintrag Luft. Wer den neunzehnten braucht, muss vorher den
/// ersten beweisen.
///
/// *Der erste ist benannt und war es die ganze Zeit:* `table.induktion` — das erzeugte
/// Induktionsschema, seit der INDUKTION-Eintragung als L3-Posten markiert, die kleinste
/// Schablone der Liste.
///
/// # BERICHTIGT 2026-08-17: der Zahn war seit dem 16.8. stumpf
///
/// Die erste Fassung las `alle unbewiesen && len > MARKE`. **Mit der ersten bewiesenen
/// Schablone wurde die linke Haelfte fuer immer falsch** — und damit die Marke wirkungslos,
/// unabhaengig davon, wie gross das Register noch wird. Der Mechanismus fiel also genau an
/// dem Tag aus, an dem das Ereignis eintrat, auf das er wartete; das Register wuchs
/// **am selben Tag** von 17 auf 19.
///
/// > *Eine Ratsche mit einer einzigen Raste ist ein Anschlag, keine Ratsche.*
///
/// **Repariert als die woertliche Verallgemeinerung des Satzes, der schon dastand**
/// (*„wer den neunzehnten braucht, muss vorher den ersten beweisen"*): das Register darf die
/// Grundmarke um **hoechstens so viele Eintraege ueberschreiten, wie Schablonen bewiesen
/// sind.** Jeder weitere Eintrag kostet einen Beweis, dauerhaft und nicht nur einmal.
///
/// **Die Luft ist heute drei Plaetze, und das gehoert dazugesagt:** zwei der vier Beweise
/// entstanden aus dem AUFTEILEN von Eintraegen (17 → 19) und haben damit selbst Eintraege
/// erzeugt. Die Regel ist bei ihrer ersten Anwendung absichtlich grosszuegig — sie zieht sich
/// mit jedem weiteren Eintrag von selbst zu.
pub const MARKE_OHNE_BEWEIS: usize = 18;

/// Wieviele Schablonen sind maschinell bewiesen?
pub fn bewiesen_in(liste: &[Schablone]) -> usize {
    liste.iter().filter(|s| s.stand == Stand::Bewiesen).count()
}

/// Wieviele Eintraege sind heute zulaessig: die Grundmarke plus je einen je Beweis.
pub fn zulaessig_in(liste: &[Schablone]) -> usize {
    MARKE_OHNE_BEWEIS + bewiesen_in(liste)
}

/// Ist das Register ueber seiner Marke? **Ein gefallenes Tor, kein Hinweis.**
///
/// Nimmt die Liste als Argument, damit der Mechanismus **unabhaengig von den heutigen Daten**
/// gepruefbar ist: ein Tor, das nur auf gesunden Daten laeuft, ist nie rot gewesen.
pub fn marke_gerissen_in(liste: &[Schablone]) -> bool {
    liste.len() > zulaessig_in(liste)
}

pub fn bewiesen() -> usize {
    bewiesen_in(SCHABLONEN)
}

pub fn zulaessig() -> usize {
    zulaessig_in(SCHABLONEN)
}

pub fn marke_gerissen() -> bool {
    marke_gerissen_in(SCHABLONEN)
}

/// **Der ERSTE Zahn, ausgesprochen:** kein neuer Eintrag ohne gemessenen Bedarf. Er gilt de
/// facto schon — `gruppe.sperrabdruck` (S17) kam aus dem Sweep, nicht aus einem Entwurf —
/// und steht hier, damit er nicht bloss Gewohnheit ist. Jede Schablone traegt ihre
/// `fundstelle`; ist sie leer oder nennt sie kein Dokument, faellt der Test.
///
/// Auch dieser nimmt die Liste als Argument, aus demselben Grund wie oben.
pub fn ohne_fundstelle_in(liste: &[Schablone]) -> Vec<&'static str> {
    liste
        .iter()
        .filter(|s| s.fundstelle.trim().is_empty())
        .map(|s| s.name)
        .collect()
}

pub fn ohne_fundstelle() -> Vec<&'static str> {
    ohne_fundstelle_in(SCHABLONEN)
}

/// **Die LEBENDE Vertrauensflaeche — und sie ist die Zahl, auf die es ankommt.**
///
/// `ungedeckt()` zaehlt alles, was nicht bewiesen ist, und wirft damit zwei sehr verschiedene
/// Zustaende zusammen:
///
/// * **`Entworfen`** — in der Spezifikation benannt, **kein Erzeugercode**. Eine Zusage ueber
///   etwas, das niemand gebaut hat. Sie kann falsch sein, ohne dass heute etwas davon abhaengt.
/// * **`Getragen`** — **der Uebersetzer stuetzt sich JETZT darauf.** Ist der Satz falsch, ist
///   das erzeugte C falsch, und zwar ab dem naechsten Lauf.
///
/// > *Die zweite Zahl ist die gefaehrliche, und bis zum 2026-08-17 stand sie nirgends.* Der
/// > Erzeuger hat an diesem Tag zwei Eintraege von `Entworfen` nach `Getragen` bewegt
/// > (`table.absenkung`, `format.roundtrip`) und einen neuen als `Getragen` angelegt
/// > (`option.sonderwert`) — **die lebende Flaeche ist an einem Tag von 1 auf 4 gewachsen**,
/// > waehrend `ungedeckt()` sich um eins bewegte.
///
/// *Wer die Kennzahl liest, liest bisher die harmlosere Haelfte.*
pub fn lebend_ungedeckt() -> usize {
    SCHABLONEN
        .iter()
        .filter(|s| s.stand == Stand::Getragen)
        .count()
}

/// **ZAHN 3 -- die RUECKRICHTUNG, seit 2026-08-18.**
///
/// Zahn 1 zaehlt Eintraege (kein Eintrag ohne gemessenen Bedarf), Zahn 2 begrenzt die
/// unbewiesenen. **Beide sehen nach VORNE.** Was keiner von beiden fragt: *ein Satz ist
/// gefuehrt -- und wer stellt seine Praemissen her?*
///
/// Der Fund, der den Zahn erzwungen hat: `device.konstruktor` ist bewiesen, und
/// `getrennte_register_treffen_getrennte_zellen` setzt `getrennt r s` voraus. **Kein Pass
/// rechnet das nach.** Wer das Zeugnis liest, sieht die Schablone als bewiesen und schliesst
/// auf Ueberlappungsfreiheit -- *der Beweis deckt die Luecke zu, statt sie zu zeigen.*
///
/// > Bei einer ungelesenen Klausel weiss niemand etwas. Hier weiss man etwas Falsches.
pub fn ohne_rueckrichtung_in(liste: &[Schablone]) -> Vec<&'static str> {
    liste
        .iter()
        .filter(|s| s.stand == Stand::Bewiesen && s.voraussetzungen.is_empty())
        .map(|s| s.name)
        .collect()
}

pub fn ohne_rueckrichtung() -> Vec<&'static str> {
    ohne_rueckrichtung_in(SCHABLONEN)
}

/// **Die Praemissen, die NIEMAND herstellt** -- Schablone und Praemisse.
///
/// Das ist die Zahl neben `lebend_ungedeckt()`, und sie misst die andere Richtung: dort ein
/// Satz ohne Beweis, hier ein Beweis ohne Pass. *Sie darf fallen und nicht steigen.*
pub fn in_der_luft_in(liste: &[Schablone]) -> Vec<(&'static str, &'static str)> {
    liste
        .iter()
        .flat_map(|s| {
            s.voraussetzungen
                .iter()
                .filter(|v| v.durch.is_none())
                .map(move |v| (s.name, v.was))
        })
        .collect()
}

pub fn in_der_luft() -> Vec<(&'static str, &'static str)> {
    in_der_luft_in(SCHABLONEN)
}

/// Wieviele Schablonen tragen heute, ohne bewiesen zu sein?
pub fn ungedeckt() -> usize {
    SCHABLONEN
        .iter()
        .filter(|s| s.stand != Stand::Bewiesen)
        .count()
}

pub fn zeige() -> String {
    let mut out = String::new();
    out.push_str(
        "-- The generator templates: the third counting column beside vocabulary and \
            axiom layer.\n",
    );
    for (n, s) in SCHABLONEN.iter().enumerate() {
        out.push_str(&format!(
            "S{}\t{}\t{}\t{}\n",
            n + 1,
            s.name,
            s.stand.text(),
            s.konstrukt
        ));
    }
    out.push_str(&format!(
        "-- {} templates, {} of them unproved, {} machine-checked.\n\
         --   of those CARRIED unproved (the compiler rests on them): {}\n",
        SCHABLONEN.len(),
        ungedeckt(),
        bewiesen(),
        lebend_ungedeckt()
    ));
    let luft = in_der_luft();
    out.push_str(&format!(
        "--   of those PREMISES WITHOUT A PASS (tooth 3): {} -- a proof nothing \
         establishes.\n",
        luft.len()
    ));
    for (schablone, was) in &luft {
        out.push_str(&format!("--     {schablone}: {was}\n"));
        // **Und was sie herstellen WUERDE.** Eine Liste von Loechern ohne die Angabe, womit
        // man sie fuellt, ist eine Klage und kein Arbeitsauftrag.
        if let Some(b) = SCHABLONEN
            .iter()
            .filter(|s| s.name == *schablone)
            .flat_map(|s| s.voraussetzungen.iter())
            .find(|v| v.was == *was)
            .and_then(|v| v.braeuchte)
        {
            out.push_str(&format!("--       braeuchte: {b}\n"));
        }
    }
    out.push_str(&format!(
        "-- The one Isabelle item is therefore not a number 1 but this list.\n\
         -- If it grows, the trust base grows -- however well the metric reads.\n\
         -- RATCHET, TOOTH 1: no entry without a measured need (a site is obligatory).\n\
         -- RATCHET, TOOTH 2: base mark {} plus one seat per PROVED template.\n\
         --   Today: {} entries, {} admissible. Every further one costs a proof.\n\
         --   The way out is not to raise the mark -- it is to prove the next one.\n\
         -- An entry leaves this list only PROVED or TOGETHER WITH ITS CONSTRUCT.\n\
         --   Not by rewording, not by merging.\n\
         -- RATCHET, TOOTH 3: every PROVED template binds its premises to a pass.\n",
        MARKE_OHNE_BEWEIS,
        SCHABLONEN.len(),
        zulaessig()
    ));
    out
}
