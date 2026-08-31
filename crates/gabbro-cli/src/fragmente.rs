//! `gabbro fragmente` -- **das Messgeraet fuer Tor P2.**
//!
//! Die Arbeit steckt in `gabbro_check::korpus`; hier steht nur, wie das Ergebnis aussieht.

use gabbro_check::korpus;

pub fn befehl(dateien: &[String]) -> std::process::ExitCode {
    if dateien.is_empty() {
        eprintln!("gabbro fragmente: no file named");
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
                "  {} from line {:<5} {:>3} lines  {:>2} errors  {:>2} hints",
                if b.vollstaendig {
                    "unit      "
                } else {
                    "excerpt   "
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
        "\nTranslation units:      {voll_sauber} of {voll_gesamt} with no errors ({:.0} %) \
         -- that is gate P2, and it demands 100 %.",
        if voll_gesamt == 0 {
            0.0
        } else {
            100.0 * voll_sauber as f64 / voll_gesamt as f64
        }
    );
    println!(
        "Excerpts:               {aus_sauber} of {aus_gesamt} with no errors -- they do \
         NOT count against the gate;"
    );
    println!(
        "                        an excerpt starts in the middle of a form, and the \
         parser can only say so as an error."
    );
    println!("{zeilen_gesamt} lines of Gabbro in total.");
    if voll_sauber == voll_gesamt {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::from(1)
    }
}
