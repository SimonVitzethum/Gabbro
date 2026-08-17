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
];

/// **Die Liste.** Jeder Eintrag ist eine Beweispflicht, die der Erzeuger schuldet — einmal,
/// nicht je Aufrufstelle. Ein neues Konstrukt mit erzeugter Form **gehoert hierher, bevor es
/// in die Grammatik kommt**.
pub const SCHABLONEN: &[Schablone] = &[
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
        pflicht: "UNTER DER PRAEMISSE `N < 2^w` (w = Breite des Indexworts, heute 32): der \
                  Sonderwert `N` liegt ausserhalb der Indexdomaene `0 ..< N`, und die \
                  Kodierung `None -> N`, `Some i -> i` ist injektiv -- **maschinell geprueft** \
                  (`kodiere_wort_injektiv`). Bei `N = 2^w` faellt sie zusammen, und `None` ist \
                  von `Some 0` nicht mehr zu unterscheiden \
                  (`sonderwert_kollidiert_bei_vollem_wort`). **OFFEN bleibt die zweite \
                  Haelfte:** dass keine erzeugte Rechnung den Sonderwert HERSTELLT. Ihr \
                  Gegenstand ist `emit.rs`, nicht eine Menge; heute weigert sich der Erzeuger \
                  fuer `None` als Ausdruck, und *solange er das tut*, kann keine Rechnung ihn \
                  erzeugen.",
        stand: Stand::Getragen,
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
        pflicht: "Eine erzeugte Mutation, die Kanten HINZUFUEGT (Umhaengen von \
                  Geschwister-/Kindzeigern), erhaelt die Wohlfundiertheit -- und das ist \
                  NICHT durch `wf_subset` gedeckt, sondern je Mutation einzeln zu zeigen. \
                  **Die pauschale Fassung ist widerlegt**, nicht offen.",
        stand: Stand::Entworfen,
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
        stand: Stand::Entworfen,
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
        pflicht: "Mehrere Orte in EINEM Zug: kein Zwischenzustand ist beobachtbar **fuer \
                  einen benannten Beobachter** -- auf einem Kern der Kontrollfluss, auf \
                  mehreren jeder Kern, der die Sperre des Zuges nicht haelt. **Ohne \
                  benannten Beobachter ist die Zusage auf einem Mehrkerner leer.**",
        stand: Stand::Entworfen,
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
                  wartet auf einen Erzeuger.*",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §11.4",
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
        stand: Stand::Entworfen,
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
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, SWEEP der Verbindungs-Invarianten, 2026-08-16 (V4)",
    },
];

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
        "-- Die Erzeuger-Schablonen: die dritte Zaehlspalte neben Wortschatz und Axiomschicht.\n\
         -- Jede Zeile ist eine Beweispflicht des ERZEUGERS -- einmal, nicht je Aufrufstelle.\n\
         -- Nr\tName\tStand\tKonstrukt\n",
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
        "-- {} Schablonen, {} davon unbewiesen, {} maschinell bewiesen.\n\
         --   davon LEBEND unbewiesen (der Uebersetzer stuetzt sich darauf): {}\n\
         --   der Rest ist entworfen -- benannt, aber ohne Erzeugercode.\n",
        SCHABLONEN.len(),
        ungedeckt(),
        bewiesen(),
        lebend_ungedeckt()
    ));
    out.push_str(&format!(
        "-- Der eine Isabelle-Posten ist damit keine Zahl 1, sondern diese Liste.\n\
         -- Waechst sie, waechst die Vertrauensbasis -- auch wenn die Kennzahl glaenzt.\n\
         -- RATSCHE, ZAHN 1: kein Eintrag ohne gemessenen Bedarf (Fundstelle pflichtig).\n\
         -- RATSCHE, ZAHN 2: Grundmarke {} plus je ein Platz je BEWIESENER Schablone.\n\
         --   Heute: {} Eintraege, {} zulaessig. Jeder weitere kostet einen Beweis.\n\
         --   Der Ausweg ist nicht, die Marke zu heben -- er ist, die naechste zu beweisen.\n\
         -- Ein Eintrag verlaesst die Liste nur BEWIESEN oder MITSAMT SEINEM KONSTRUKT.\n\
         --   Nicht durch Umformulierung, nicht durch Zusammenfassen.\n",
        MARKE_OHNE_BEWEIS,
        SCHABLONEN.len(),
        zulaessig()
    ));
    out
}
