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
    "P023", "P024", "P025", "P026", "P027", "P028", "P029", "P030", "P031", "P033", "P034", "P035",
    "P032", "P035", // Grammatik
    "M101", "M102", "M103", "M104", "M105", // M1 + V1-V3
    "N001", "N002", "N003", // Namen
    "S001", "S002", // Schleifen und Kontrollfluss
    // **`progress` bekam am 2026-08-18 seinen ersten Leser** -- und `S003` faellt sofort im
    // Korpus (`FRAGMENTE.md`:887, die `virtq`-Wartestelle). Das ist KEINE Fehlmessung: ein
    // Fragment traegt keine Annahmenschicht, also nennt sein `progress` einen Zeugen, den
    // niemand erklaert. *In einem ganzen Programm waere genau das der Fehler.*
    "S003", "S004",
    // «F»: f32/f64. `F002` trifft das stillschweigend inexakte Literal -- die Regel kam aus
    // dem Korpus (FRAGMENTE.md, «F0»/FF4), nicht aus dem Entwurf.
    "F001", "F002", "F004", "F005", "F006",
    "K001", "K002", "K003", // Kosten
    "E001", "E002", "E003", "E004", "E005", "E006", "E007", "E008", "E009",
    "E010", // Wirkungen -- E010 ist die Lesehaelfte (Lesart A, 2026-08-16)
    "H001", "H002", "H003", "H004", "H005", "H006", // geteilter Halt, Rangordnung
    // K11.2.1: `protects` beisst (`H007`) und eine nie genommene Sperre faellt auf (`H008`).
    "H007", "H008",
    // «K2»: RCU ist keine Sperre -- H009 Leseseite benannt, H010 Schreiber braucht eine.
    "H009", "H010", "H011", "H012",
    // «B37» und K11.1: die Ordnung auf einer linearen Geistmarke. `O005` ist ZURUECKGEZOGEN --
    // der Hinweis „dieser Pass entscheidet das nicht" ist durch `O006` ersetzt, und der Code
    // bleibt frei: eine Absage, die heimlich ihre Bedeutung wechselt, ist schlimmer als eine
    // Nummer, die ungenutzt bleibt.
    "O001", "O002", "O003", "O004", "O006",
    // «B7»: der Verbundkonstruktor.
    "M106", "M107", "M108", "P036", "P037",
    // Punkt 3: `ensures` wird gelesen -- Wohlgeformtheit, nicht Beweis.
    "M109", "M110", "M111",
    "K004", "K005", "D001", "D002", "D003", "D004", "M105", // Haltezeit geteilt, K-Bedingung, narrow-Zweig
    "V001", "V002", "V003", "V004", // Paarung
    "L101", "L102", "L103", "L104", "L105", // M2, echte Linearitaet
    "R001", "R002", "R003", // M3, Raeume und Rechte
    "U001", "U002", "U003", "U004", "U005", "U006", "U007", // Traegergruppe: Sperrabdruck, Zug und Verbindungsaussage
];

#[test]
fn der_korpus_bringt_nur_benannte_absagen() {
    for datei in ["dokumente/FRAGMENTE.md", "dokumente/SYNTAX.md", "dokumente/SPRACHE.md", "README.md",
                  // Der Memo BEHAUPTET „heute schreibbar" -- dann wird sein Block auch gemessen.
                  "dokumente/MEMO-GLEITKOMMA.md"] {
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
    let md = lies("dokumente/FRAGMENTE.md");
    let befunde = korpus::messe("dokumente/FRAGMENTE.md", &md);
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
    let md = lies("dokumente/FRAGMENTE.md");
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

#[test]
fn die_beispiele_der_grammatik_gehen_selbst_durch() {
    // **SYNTAX.md ist das Grammatikdokument -- seine eigenen Uebersetzungseinheiten muessen
    // uebersetzen.** Bis 2026-08-16 hat das niemand verlangt, und es standen drei echte
    // Fehler darin: `Duty(check)` (der Parameter ist der NAME einer Pruefung, nicht das
    // Wort), und zweimal eine Wortschatzkollision in einem Beispiel.
    //
    // *Ein Grammatikdokument, dessen Beispiele die Grammatik verletzen, ist die teuerste
    // Sorte Prosa: es sieht aus wie ein Beleg.*
    let md = lies("dokumente/SYNTAX.md");
    for b in korpus::messe("dokumente/SYNTAX.md", &md) {
        if b.vollstaendig {
            assert!(
                b.sauber(),
                "SYNTAX.md, Block ab Zeile {}: das Grammatikdokument bricht seine eigene \
                 Grammatik:\n{}",
                b.erste_zeile,
                b.text
            );
        }
    }
}

#[test]
fn jeder_gebaute_pass_ist_auch_angemeldet() {
    // **Gegen den entzogenen Halbcommit.** Am 2026-08-16 loeste ein `git stash` die
    // Registrierung des Paarungspasses aus dem Index; der Commit trug den Pass ohne seine
    // Anmeldung, und `gabbro paesse` haette ihn weiter als OFFEN gefuehrt. Niemand haette
    // es gemerkt -- die Proben liefen gruen, weil `pruefe()` ihn ja aufrief.
    //
    // Dieselbe mechanische Loesung wie fuer die Kennungen: der Abgleich steht in der
    // Waechterkette, nicht in der Aufmerksamkeit.
    let quelle = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs"),
    )
    .expect("lib.rs");
    // Jedes `<name>::pass(` in `pruefe()` muss einen Eintrag in `passliste()` haben, der
    // NICHT `Zustand::Offen` ist -- ein aufgerufener Pass, der als offen gilt, ist eine
    // Zusage in die falsche Richtung: er prueft mehr, als er zugibt.
    let rumpf = quelle
        .split("pub fn pruefe(")
        .nth(1)
        .and_then(|s| s.split("\n}").next())
        .expect("pruefe()");
    for zeile in rumpf.lines() {
        let Some(modul) = zeile.trim().strip_suffix("::pass(baum, absagen);") else {
            continue;
        };
        let name = match modul {
            "m1" => "M1",
            "m2" => "M2",
            "m3" => "M3",
            "paarung" => "Paarung",
            "wirkungen" => "effects",
            "kosten" => "costs",
            "schleifen" => "M4",
            "namen" => "Namen",
            _ => continue, // Hilfspaesse ohne eigene Nummer (kbedingung, geteilt)
        };
        let eintrag = gabbro_check::passliste()
            .into_iter()
            .find(|p| p.name.starts_with(name))
            .unwrap_or_else(|| panic!("`{modul}::pass` laeuft, steht aber in keiner Passliste"));
        assert!(
            !matches!(eintrag.zustand, gabbro_check::Zustand::Offen(_)),
            "`{modul}::pass` wird gerufen, `gabbro paesse` fuehrt `{}` aber als OFFEN -- \
             ein Pass, der prueft und sich als ungebaut ausgibt, ist eine Zusage in die \
             falsche Richtung",
            eintrag.name
        );
    }
}

/// **Diese Probe kam aus einer Mutation, die ueberlebt hat (2026-08-17).**
///
/// `eine-einheit-faengt-mit-irgendwas-an` machte `ist_uebersetzungseinheit` blind fuer die
/// Frage, womit ein Block anfaengt — und **nichts fiel**. Die Regel *„eine
/// Uebersetzungseinheit faengt mit einem Item an"* war damit unbewacht, obwohl Tor P2 auf
/// ihr steht: sie entscheidet, was ueberhaupt gezaehlt wird.
///
/// > *Ein Nenner, den niemand prueft, ist die billigste Art, eine Quote zu verbessern.*
#[test]
fn eine_uebersetzungseinheit_faengt_mit_einem_item_an() {
    use gabbro_check::korpus::ist_uebersetzungseinheit;

    assert!(
        ist_uebersetzungseinheit("module t {\nconst A : u32 = 1;\n}"),
        "ein Modul ist eine Uebersetzungseinheit"
    );
    assert!(
        ist_uebersetzungseinheit("const A : u32 = 1;"),
        "ein Item auf oberster Ebene auch"
    );

    // **Ausschnitte, und genau sie sind der Grund fuer die Unterscheidung.** SPRACHE.md und
    // SYNTAX.md zeigen ueberwiegend einzelne Anweisungen; wer sie als Programm liest, meldet
    // Fehler, die es nicht gibt — und wer sie MITZAEHLT, rechnet die Quote von Tor P2 schoen.
    for ausschnitt in [
        "let x : u32 = 1;",
        "return 0;",
        "if a < b { return 0; }",
        "traverse s over slots of c by unvisited { }",
        "match a { Eins(x) => { } }",
    ] {
        assert!(
            !ist_uebersetzungseinheit(ausschnitt),
            "`{ausschnitt}` faengt mit einer ANWEISUNG an und ist kein Programm"
        );
    }

    // Und der Fall, der die erste Fassung dieser Regel aufgeflogen hat: `…` im KOMMENTAR
    // ist erlaubt (der Lexer trennt Code von Kommentar), `…` im CODE nicht.
    assert!(
        ist_uebersetzungseinheit("-- hier waere noch mehr …\nconst A : u32 = 1;"),
        "`…` im Kommentar macht aus einem Programm keine Skizze (W9, gemessene Richtung)"
    );
    assert!(
        !ist_uebersetzungseinheit("const A : u32 = …;"),
        "`…` im Code ist eine Auslassung, kein Programm"
    );
}
