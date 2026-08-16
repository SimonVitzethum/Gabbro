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
//! Emissionspass statt einer je Konstrukt. **Heute ist sie eine Vorabfestlegung** — der
//! Emissionspass ist nicht gebaut, `mutiere-pruefer.py` weist ihn mit 0 Mutationen aus, und
//! was 0 Mutationen hat, ist nicht gedeckt, sondern unbeschaedigbar.

/// Wie weit eine Schablone ist.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stand {
    /// In der Spezifikation benannt, kein Erzeugercode.
    Entworfen,
    /// Der Uebersetzer stuetzt sich heute darauf.
    Getragen,
    /// Einmal nach Isabelle gebracht. **Der einzige Stand, der die Vertrauensbasis
    /// verkleinert** — und heute erreicht ihn keine.
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
    "ops.suche",
    "state.reset",
    "verbund.konstruktor",
    "gruppe.ops",
    "gruppe.sperrabdruck",
];

/// **Die Liste.** Jeder Eintrag ist eine Beweispflicht, die der Erzeuger schuldet — einmal,
/// nicht je Aufrufstelle. Ein neues Konstrukt mit erzeugter Form **gehoert hierher, bevor es
/// in die Grammatik kommt**.
pub const SCHABLONEN: &[Schablone] = &[
    Schablone {
        name: "consuming.ordnung",
        haengt_an: &["table.induktion"],
        konstrukt: "traverse … by consuming",
        pflicht: "Die Domaene liefert ihre Zeugen in der erzeugten wohlfundierten Ordnung, \
                  und die Ordnung bleibt unter der erzeugten Mutation erhalten. Daraus faellt \
                  die Blattheit zum Verbrauchszeitpunkt.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "consuming.leermenge",
        haengt_an: &[],
        konstrukt: "traverse … by consuming",
        pflicht: "Die erzeugte Zeugenmenge ist VOLLSTAENDIG: ist sie leer, ist die Domaene \
                  leer. Ohne diese Richtung koennte eine Traversierung Elemente auslassen und \
                  trotzdem terminieren -- sie waere dann total, aber nicht erschoepfend.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "table.ops.erhaltung",
        haengt_an: &[],
        konstrukt: "table … ops",
        pflicht: "Je erzeugter Mutation bleibt jede `online`-Invariante erhalten — einmal \
                  ueber der Deklaration, nicht je Aufrufstelle.",
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
        pflicht: "Mehrere Orte in EINEM Zug: kein Zwischenzustand ist beobachtbar, in dem \
                  ein Teil gesetzt ist und ein anderer nicht.",
        stand: Stand::Entworfen,
        fundstelle: "SYNTAX.md §10",
    },
    Schablone {
        name: "exchange.rmw",
        haengt_an: &[],
        konstrukt: "exchange update(v) { … } / … when … returns",
        pflicht: "Die erzeugte Lese-Aendere-Schreibe-Folge ist atomar und der Rumpf rein.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md Teil III §1",
    },
    Schablone {
        name: "accumulates.monoid",
        haengt_an: &[],
        konstrukt: "accumulates … merge",
        pflicht: "Die Merge-Menge ist ein kommutatives Monoid, und die Absenkung (je Kern \
                  eine Zelle, Zusammenfuehrung beim Lesen) ergibt denselben Wert wie ein \
                  atomares RMW.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §11.4",
    },
    Schablone {
        name: "walk.mappings",
        haengt_an: &[],
        konstrukt: "walk … levels / mappings of",
        pflicht: "Die erzeugte Domaene `mappings of` trifft genau die erreichbaren \
                  Blatteintraege, samt va und level.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §5.4, §6",
    },
    Schablone {
        name: "format.roundtrip",
        haengt_an: &[],
        konstrukt: "format",
        pflicht: "`lesen(schreiben(x)) == x`, und der Leser prueft die Pufferlaenge genau \
                  einmal am Eintritt.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §10.1",
    },
    Schablone {
        name: "entry.abdruck",
        haengt_an: &[],
        konstrukt: "entry … dispatch",
        pflicht: "Der erzeugte Eintrittspfad erhaelt `preserves`, zerstoert hoechstens \
                  `clobbers`, und der Stapelwechsel ist korrekt. **Kein nachgelagerter \
                  Beweiser** -- das Vertrauen schrumpft auf eine Stelle, es verschwindet nicht.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md Teil II §2",
    },
    Schablone {
        name: "device.konstruktor",
        haengt_an: &[],
        konstrukt: "device D(params) at space",
        pflicht: "Aus der Adresse entsteht ein typisierter Griff, und die Registerlagen des \
                  Blocks treffen die Hardware-Lagen.",
        stand: Stand::Getragen,
        fundstelle: "MESSUNGEN.md, Der Ursprung, 2026-08-14",
    },
    Schablone {
        name: "table.indexschranke",
        haengt_an: &[],
        konstrukt: "table … count N / index into T",
        pflicht: "Der erzeugte Indextyp `0 ..< N` deckt genau die belegten Slots, und die \
                  Absenkung legt N Slots an.",
        stand: Stand::Getragen,
        fundstelle: "MESSUNGEN.md, A3, 2026-08-14",
    },
    // ---- Kandidaten aus der Nachpruefung vom 2026-08-14. Noch kein Konstrukt, aber die
    // ---- Pflicht steht schon fest -- und genau das ist der Punkt dieser Liste.
    Schablone {
        name: "ops.suche",
        haengt_an: &[],
        konstrukt: "ops finde … (Kandidat, aus «B10»)",
        pflicht: "Die erzeugte Suche gibt den ERSTEN Treffer in der Ordnung der Domaene und \
                  laesst die Menge unveraendert.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "state.reset",
        haengt_an: &[],
        konstrukt: "erzeugtes reset (Kandidat, aus «B26»)",
        pflicht: "Der erzeugte Uebergang in den Anfangszustand gilt aus JEDEM Zustand und \
                  ist selbst ein `transset`.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "verbund.konstruktor",
        haengt_an: &[],
        konstrukt: "erzeugter Konstruktor (Kandidat, aus «B7»)",
        pflicht: "Der aus der Felderliste erzeugte Konstruktor setzt jedes Feld genau einmal \
                  und laesst keins uninitialisiert.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "gruppe.ops",
        haengt_an: &[],
        konstrukt: "Gruppen-ops ueber mehreren Tabellen (Kandidat, aus «B13»)",
        pflicht: "Die Verbindungs-Invariante der Gruppe bleibt unter jeder Gruppenoperation \
                  erhalten -- und zwar unter dem deklarierten Sperrabdruck der Operation, \
                  nicht sequenziell. Auf einem Mehrkerner ist das die eigentliche Pflicht. \
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
/// Schablone der Liste. **Sie kommt seit Tagen nicht dran, weil sie mit nichts konkurriert
/// ausser mit allem.**
pub const MARKE_OHNE_BEWEIS: usize = 18;

/// Ist das Register ueber seiner Marke? **Ein gefallenes Tor, kein Hinweis.**
pub fn marke_gerissen() -> bool {
    SCHABLONEN.iter().all(|s| s.stand != Stand::Bewiesen) && SCHABLONEN.len() > MARKE_OHNE_BEWEIS
}

/// **Der ERSTE Zahn, ausgesprochen:** kein neuer Eintrag ohne gemessenen Bedarf. Er gilt de
/// facto schon — `gruppe.sperrabdruck` (S17) kam aus dem Sweep, nicht aus einem Entwurf —
/// und steht hier, damit er nicht bloss Gewohnheit ist. Jede Schablone traegt ihre
/// `fundstelle`; ist sie leer oder nennt sie kein Dokument, faellt der Test.
pub fn ohne_fundstelle() -> Vec<&'static str> {
    SCHABLONEN
        .iter()
        .filter(|s| s.fundstelle.trim().is_empty())
        .map(|s| s.name)
        .collect()
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
        "-- {} Schablonen, {} davon unbewiesen.\n",
        SCHABLONEN.len(),
        ungedeckt()
    ));
    out.push_str(
        "-- Der eine Isabelle-Posten ist damit keine Zahl 1, sondern diese Liste.\n\
         -- Waechst sie, waechst die Vertrauensbasis -- auch wenn die Kennzahl glaenzt.\n\
         -- RATSCHE, ZAHN 1: kein Eintrag ohne gemessenen Bedarf (Fundstelle pflichtig).\n\
         -- RATSCHE, ZAHN 2: solange KEINE bewiesen ist, sind hoechstens 18 zulaessig.\n\
         --   Der Ausweg ist nicht, die Marke zu heben -- er ist, die erste zu beweisen.\n\
         --   Benannt und seit langem faellig: `table.induktion`, die kleinste der Liste.\n\
         -- Ein Eintrag verlaesst die Liste nur BEWIESEN oder MITSAMT SEINEM KONSTRUKT.\n\
         --   Nicht durch Umformulierung, nicht durch Zusammenfassen.\n",
    );
    out
}
