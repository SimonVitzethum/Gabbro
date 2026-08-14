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
];

/// **Die Liste.** Jeder Eintrag ist eine Beweispflicht, die der Erzeuger schuldet — einmal,
/// nicht je Aufrufstelle. Ein neues Konstrukt mit erzeugter Form **gehoert hierher, bevor es
/// in die Grammatik kommt**.
pub const SCHABLONEN: &[Schablone] = &[
    Schablone {
        name: "consuming.ordnung",
        konstrukt: "traverse … by consuming",
        pflicht: "Die Domaene liefert ihre Zeugen in der erzeugten wohlfundierten Ordnung, \
                  und die Ordnung bleibt unter der erzeugten Mutation erhalten. Daraus faellt \
                  die Blattheit zum Verbrauchszeitpunkt.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "consuming.leermenge",
        konstrukt: "traverse … by consuming",
        pflicht: "Die erzeugte Zeugenmenge ist VOLLSTAENDIG: ist sie leer, ist die Domaene \
                  leer. Ohne diese Richtung koennte eine Traversierung Elemente auslassen und \
                  trotzdem terminieren -- sie waere dann total, aber nicht erschoepfend.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §9.2",
    },
    Schablone {
        name: "table.ops.erhaltung",
        konstrukt: "table … ops",
        pflicht: "Je erzeugter Mutation bleibt jede `online`-Invariante erhalten — einmal \
                  ueber der Deklaration, nicht je Aufrufstelle.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §10.2",
    },
    Schablone {
        name: "table.induktion",
        konstrukt: "by induction over <domain>",
        pflicht: "Das aus der `table`-Deklaration erzeugte Induktionsschema ist wohlfundiert \
                  und vollstaendig.",
        stand: Stand::Entworfen,
        fundstelle: "SYNTAX.md §5, SPRACHE.md Teil V",
    },
    Schablone {
        name: "transition.transset",
        konstrukt: "transition { a: … , b: … }",
        pflicht: "Mehrere Orte in EINEM Zug: kein Zwischenzustand ist beobachtbar, in dem \
                  ein Teil gesetzt ist und ein anderer nicht.",
        stand: Stand::Entworfen,
        fundstelle: "SYNTAX.md §10",
    },
    Schablone {
        name: "exchange.rmw",
        konstrukt: "exchange update(v) { … } / … when … returns",
        pflicht: "Die erzeugte Lese-Aendere-Schreibe-Folge ist atomar und der Rumpf rein.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md Teil III §1",
    },
    Schablone {
        name: "accumulates.monoid",
        konstrukt: "accumulates … merge",
        pflicht: "Die Merge-Menge ist ein kommutatives Monoid, und die Absenkung (je Kern \
                  eine Zelle, Zusammenfuehrung beim Lesen) ergibt denselben Wert wie ein \
                  atomares RMW.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §11.4",
    },
    Schablone {
        name: "walk.mappings",
        konstrukt: "walk … levels / mappings of",
        pflicht: "Die erzeugte Domaene `mappings of` trifft genau die erreichbaren \
                  Blatteintraege, samt va und level.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §5.4, §6",
    },
    Schablone {
        name: "format.roundtrip",
        konstrukt: "format",
        pflicht: "`lesen(schreiben(x)) == x`, und der Leser prueft die Pufferlaenge genau \
                  einmal am Eintritt.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md §10.1",
    },
    Schablone {
        name: "entry.abdruck",
        konstrukt: "entry … dispatch",
        pflicht: "Der erzeugte Eintrittspfad erhaelt `preserves`, zerstoert hoechstens \
                  `clobbers`, und der Stapelwechsel ist korrekt. **Kein nachgelagerter \
                  Beweiser** -- das Vertrauen schrumpft auf eine Stelle, es verschwindet nicht.",
        stand: Stand::Entworfen,
        fundstelle: "SPRACHE.md Teil II §2",
    },
    Schablone {
        name: "device.konstruktor",
        konstrukt: "device D(params) at space",
        pflicht: "Aus der Adresse entsteht ein typisierter Griff, und die Registerlagen des \
                  Blocks treffen die Hardware-Lagen.",
        stand: Stand::Getragen,
        fundstelle: "MESSUNGEN.md, Der Ursprung, 2026-08-14",
    },
    Schablone {
        name: "table.indexschranke",
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
        konstrukt: "ops finde … (Kandidat, aus «B10»)",
        pflicht: "Die erzeugte Suche gibt den ERSTEN Treffer in der Ordnung der Domaene und \
                  laesst die Menge unveraendert.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "state.reset",
        konstrukt: "erzeugtes reset (Kandidat, aus «B26»)",
        pflicht: "Der erzeugte Uebergang in den Anfangszustand gilt aus JEDEM Zustand und \
                  ist selbst ein `transset`.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "verbund.konstruktor",
        konstrukt: "erzeugter Konstruktor (Kandidat, aus «B7»)",
        pflicht: "Der aus der Felderliste erzeugte Konstruktor setzt jedes Feld genau einmal \
                  und laesst keins uninitialisiert.",
        stand: Stand::Entworfen,
        fundstelle: "MESSUNGEN.md, B13-Nachpruefung",
    },
    Schablone {
        name: "gruppe.ops",
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
];

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
         -- RATSCHE: ein Eintrag geht nur BEWIESEN oder MITSAMT SEINEM KONSTRUKT.\n\
         --          Nicht durch Umformulierung, nicht durch Zusammenfassen.\n",
    );
    out
}
