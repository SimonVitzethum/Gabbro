//! `gabbro fragmente` -- **das Messgeraet fuer Tor P2.**
//!
//! Die Arbeit steckt in `gabbro_check::korpus`; hier steht nur, wie das Ergebnis aussieht.

use gabbro_check::korpus;

pub fn befehl(dateien: &[String]) -> std::process::ExitCode {
    if dateien.is_empty() {
        eprintln!("gabbro fragmente: keine Datei genannt");
        return std::process::ExitCode::from(2);
    }
    let mut voll_gesamt = 0usize;
    let mut voll_sauber = 0usize;
    let mut aus_gesamt = 0usize;
    let mut aus_sauber = 0usize;
    let mut zeilen_gesamt = 0usize;
    for datei in dateien {
        let quelle = match std::fs::read_to_string(datei) {
            Ok(q) => q,
            Err(e) => {
                eprintln!("gabbro: {datei}: {e}");
                return std::process::ExitCode::from(1);
            }
        };
        let befunde = korpus::messe(datei, &quelle);
        if befunde.is_empty() {
            println!("{datei}: no ```gabbro block");
            continue;
        }
        println!("{datei}:");
        for b in &befunde {
            zeilen_gesamt += b.zeilen;
            if b.vollstaendig {
                voll_gesamt += 1;
                if b.sauber() {
                    voll_sauber += 1;
                }
            } else {
                aus_gesamt += 1;
                if b.sauber() {
                    aus_sauber += 1;
                }
            }
            println!(
                "  {} ab Zeile {:<5} {:>3} Zeilen  {:>2} Fehler  {:>2} Hinweise",
                if b.vollstaendig {
                    "Einheit  "
                } else {
                    "Ausschnitt"
                },
                b.erste_zeile,
                b.zeilen,
                b.fehler.len(),
                b.hinweise.len()
            );
            print!("{}", b.text);
        }
    }
    println!(
        "\nUebersetzungseinheiten: {voll_sauber} von {voll_gesamt} ohne Fehler ({:.0} %) \
         -- das ist Tor P2, und es verlangt 100 %.",
        if voll_gesamt == 0 {
            0.0
        } else {
            100.0 * voll_sauber as f64 / voll_gesamt as f64
        }
    );
    println!(
        "Ausschnitte:            {aus_sauber} von {aus_gesamt} ohne Fehler -- sie zaehlen \
         NICHT gegen das Tor;"
    );
    println!(
        "                        ein Ausschnitt faengt mitten in einer Form an, und der \
         Parser sagt das nur als Fehler."
    );
    println!("Zusammen {zeilen_gesamt} Zeilen Gabbro.");
    if voll_sauber == voll_gesamt {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::from(1)
    }
}
