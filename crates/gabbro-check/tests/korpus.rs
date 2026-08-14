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
    "E001", "E002", "E003", "E004", "E005", "E006", // Wirkungen
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
    let f2 = befunde
        .iter()
        .find(|b| b.erste_zeile > 330 && b.erste_zeile < 350)
        .expect("F2 faengt kurz nach Zeile 340 an");
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
