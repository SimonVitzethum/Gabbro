//! **Der Korpuslauf als Test** -- Tor P2, gemessen statt behauptet.
//!
//! Was hier festgehalten wird, ist nicht die *Zahl* der Fehler (die soll fallen), sondern
//! **ihre Art**: jeder Befund am Korpus muss ein Code sein, den dieser Uebersetzer benannt
//! hat. Ein neuer, unbenannter Code ist ein Befund ueber den Uebersetzer, kein Rauschen --
//! und genau so faellt der Test.
//!
//! Die gemessenen Zahlen stehen in `MESSUNGEN.md`, mit Datum. Sie hier zu wiederholen hiesse,
//! eine Zahl an zwei Stellen zu fuehren.

use gabbro_check::korpus;

fn lies(datei: &str) -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(datei);
    std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()))
}

/// Jeder Code, den der Korpuslauf hervorbringen darf. Ein Eintrag hier ist eine Aussage:
/// *diese Absage ist gemeint und ihr Text ist geprueft.*
const BENANNT: &[&str] = &[
    "L001", "L002", "L003", "L004", "L005", "L006", // Lexik
    "P001", "P002", "P003", "P004", "P005", "P006", "P007", "P008", "P009", "P010", "P011",
    "P012", "P013", "P014", "P015", "P016", "P017", "P018", "P019", "P020", "P021", "P022",
    "P023", "P024", "P025", "P026", "P027", "P028", "P029", "P030", "P031", "P033", "P034",
    "P032", "P035", // Grammatik
    "M101", "M102", "M103", "M104", "M105", // M1 + V1-V3
    "N001", "N002", "N003", // Namen
    "S001", "S002", // Schleifen und Kontrollfluss
    "K001", "K002", "K003", // Kosten
    "E001", "E002", "E003", "E004", "E005", "E006", "E007", "E008", "E009", // Wirkungen
    "H001", "H002", "H003", "H004", "H005", // geteilter Halt
    "K004", "D001", "M105", // Haltezeit geteilt, K-Bedingung, narrow-Zweig
    "V001", "V002", "V003", "V004", // Paarung
];

#[test]
fn der_korpus_bringt_nur_benannte_absagen() {
    for datei in ["FRAGMENTE.md", "SYNTAX.md", "SPRACHE.md", "README.md"] {
        let md = lies(datei);
        for b in korpus::messe(datei, &md) {
            for (code, zeile) in b.fehler.iter().chain(b.hinweise.iter()) {
                assert!(
                    BENANNT.contains(code),
                    "{datei}:{zeile}: unbenannte Absage `{code}` -- \
                     jede Absage braucht ihren Eintrag, sonst zaehlt niemand sie"
                );
            }
        }
    }
}

#[test]
fn f2_das_geraetefragment_bleibt_sauber() {
    // F2 (VT-d als `device`) ist das eine Fragment, das gegen die heutige Grammatik
    // vollstaendig durchgeht. Faellt es, ist eine Regel zurueckgegangen.
    let md = lies("FRAGMENTE.md");
    let befunde = korpus::messe("FRAGMENTE.md", &md);
    // **Am INHALT verankert, nicht an der Zeilennummer.** Bis 2026-08-15 stand hier
    // `erste_zeile > 330 && < 350`; jede Aenderung weiter oben in der Datei brach den Test,
    // ohne dass an F2 etwas falsch war. Eine Probe, die an einer Zeilennummer haengt, ist
    // dieselbe Sorte Zahl wie eine, die ein Mensch parallel zur Wahrheit fuehrt.
    // `Befund.text` ist der gerenderte BERICHT, nicht die Quelle -- der Inhalt muss aus
    // den geschnittenen Bloecken kommen.
    let quelle = korpus::schneide(&md);
    let f2_zeile = quelle
        .iter()
        .find(|b| b.text.contains("device Vtd"))
        .map(|b| b.erste_zeile)
        .expect("F2 ist das VT-d-Fragment -- erkennbar an `device Vtd`");
    let f2 = befunde
        .iter()
        .find(|b| b.erste_zeile == f2_zeile)
        .expect("zu jedem geschnittenen Block gehoert ein Befund");
    assert!(
        f2.sauber(),
        "F2 war sauber und ist es nicht mehr:\n{}",
        f2.text
    );
}

#[test]
fn jeder_block_wird_gefunden() {
    let md = lies("FRAGMENTE.md");
    let bloecke = korpus::schneide(&md);
    assert_eq!(
        bloecke.len(),
        md.matches("\n```gabbro").count(),
        "der Schneider verliert Bloecke"
    );
    // Die Zeilennummern muessen die der Markdown-Datei sein -- sonst zeigt eine Absage
    // auf eine Zeile, die es nicht gibt.
    for b in &bloecke {
        let vorspann = b.text.chars().take_while(|c| *c == '\n').count();
        assert_eq!(vorspann + 1, b.erste_zeile);
    }
}
