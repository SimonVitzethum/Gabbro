//! `gabbro` -- die Kommandozeile.
//!
//! Vier Befehle, und der wichtigste ist `paesse`: er sagt, **was dieser Uebersetzer nicht
//! prueft.** Ein Werkzeug, das nur meldet, was es gefunden hat, laesst ungeprueftes Schweigen
//! wie ein Gruen aussehen.

use gabbro_check::{manifest, passliste, pruefe, Zustand};
use gabbro_syntax::diag::Stufe;

mod fragmente;

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        hilfe();
        return std::process::ExitCode::from(2);
    }
    let (befehl, rest) = args.split_first().expect("nicht leer");
    match befehl.as_str() {
        "pruefe" => befehl_pruefe(rest),
        "fragmente" => fragmente::befehl(rest),
        "annahmen" => befehl_annahmen(rest),
        "k-bedingung" => {
            if rest.is_empty() {
                eprintln!("gabbro k-bedingung: keine Datei genannt");
                return std::process::ExitCode::from(2);
            }
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    continue;
                };
                let (baum, _) = gabbro_syntax::lies(datei, &quelle);
                println!("== {datei} ==");
                print!(
                    "{}",
                    gabbro_check::kbedingung::zeige(&gabbro_check::kbedingung::erhebe(&baum))
                );
            }
            std::process::ExitCode::SUCCESS
        }
        "kosten" => {
            if rest.is_empty() {
                eprintln!("gabbro kosten: keine Datei genannt");
                return std::process::ExitCode::from(2);
            }
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    continue;
                };
                let (baum, _) = gabbro_syntax::lies(datei, &quelle);
                println!("== {datei} ==");
                print!("{}", gabbro_check::kosten::bericht(&baum));
            }
            std::process::ExitCode::SUCCESS
        }
        "schablonen" => {
            print!("{}", gabbro_check::schablonen::zeige());
            std::process::ExitCode::SUCCESS
        }
        "paesse" => {
            befehl_paesse();
            std::process::ExitCode::SUCCESS
        }
        "--hilfe" | "-h" | "hilfe" => {
            hilfe();
            std::process::ExitCode::SUCCESS
        }
        anderes => {
            eprintln!("gabbro: unbekannter Befehl `{anderes}`");
            hilfe();
            std::process::ExitCode::from(2)
        }
    }
}

fn hilfe() {
    eprintln!(
        "gabbro -- Uebersetzer und Pruefer fuer Gabbro (Stufe P2 + drei Paesse)

  gabbro pruefe     <datei.gab>…    liest, parst und faehrt die gebauten Paesse
  gabbro fragmente  <datei.md>…     jeden ```gabbro-Block einer Markdown-Datei, einzeln
  gabbro annahmen   <datei.gab>…    das Annahmenmanifest: bewiesen unter A1…An
  gabbro paesse                     die Passliste -- gebaut UND offen
  gabbro schablonen                 die Erzeuger-Schablonen: die dritte Zaehlspalte
  gabbro k-bedingung <datei.gab>…   je Traeger: sind ALLE Schreibstellen erzeugt? (Messung 2)

Rueckgabe: 0 wenn kein Fehler, 1 bei Fehlern, 2 bei falschem Aufruf."
    );
}

fn befehl_paesse() {
    println!("Die Pruefpaesse in fester Reihenfolge (SPRACHE.md Teil III, §6):\n");
    for p in passliste() {
        let (marke, note) = match p.zustand {
            Zustand::Gebaut => ("gebaut", String::new()),
            Zustand::Teilgebaut(w) => ("TEIL  ", format!("\n         kommt durch: {w}")),
            Zustand::Offen(w) => ("OFFEN ", format!("\n         ungeprueft: {w}")),
        };
        println!("  {} {}  {:<14} {}{}", marke, p.nummer, p.name, p.quelle, note);
    }
    let voll = passliste()
        .iter()
        .filter(|p| p.zustand == Zustand::Gebaut)
        .count();
    let teil = passliste()
        .iter()
        .filter(|p| matches!(p.zustand, Zustand::Teilgebaut(_)))
        .count();
    println!(
        "\n  {voll} of {} passes are fully built, {teil} partial. What is OPEN is",
        passliste().len()
    );
    println!("  NICHT geprueft, und was TEIL ist, nur so weit wie danebensteht --");
    println!("  a green run is therefore not a proof but the absence of the findings");
    println!("  that the built passes are able to see.");
}

fn befehl_pruefe(dateien: &[String]) -> std::process::ExitCode {
    if dateien.is_empty() {
        eprintln!("gabbro pruefe: keine Datei genannt");
        return std::process::ExitCode::from(2);
    }
    let mut fehler = 0usize;
    for datei in dateien {
        let quelle = match std::fs::read_to_string(datei) {
            Ok(q) => q,
            Err(e) => {
                eprintln!("gabbro: {datei}: {e}");
                fehler += 1;
                continue;
            }
        };
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
        let bericht = pruefe(&baum, &mut absagen);
        if !absagen.leer() {
            print!("{}", absagen.zeige(&quelle));
        }
        let f = absagen.fehler_zahl();
        let h = absagen.absagen.len() - f;
        fehler += f;
        println!(
            "{datei}: {} Items, {f} Fehler, {h} Hinweise",
            zaehle_items(&baum)
        );
        // Die Deckung steht NEBEN dem Ergebnis: „nichts gefunden" und „nichts angesehen"
        // sehen sonst gleich aus.
        if bericht.m1.gesamt() == 0 {
            println!("  M1 saw no expression -- this file has no function body");
        } else {
            println!(
                "  M1 sah {} Ausdruecke, {} davon ohne Typ ({:.0} % Deckung)",
                bericht.m1.gesamt(),
                bericht.m1.unbekannt,
                bericht.m1.deckung()
            );
        }
    }
    println!();
    println!("Nicht geprueft in diesem Lauf:");
    for p in gabbro_check::ungeprueft() {
        match p.zustand {
            Zustand::Offen(w) => println!("  {} {:<14} {w}", p.nummer, p.name),
            Zustand::Teilgebaut(w) => {
                println!("  {} {:<14} NUR TEILWEISE -- {w}", p.nummer, p.name)
            }
            Zustand::Gebaut => {}
        }
    }
    if fehler == 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::from(1)
    }
}

fn befehl_annahmen(dateien: &[String]) -> std::process::ExitCode {
    if dateien.is_empty() {
        eprintln!("gabbro annahmen: keine Datei genannt");
        return std::process::ExitCode::from(2);
    }
    let mut alle = Vec::new();
    for datei in dateien {
        let quelle = match std::fs::read_to_string(datei) {
            Ok(q) => q,
            Err(e) => {
                eprintln!("gabbro: {datei}: {e}");
                return std::process::ExitCode::from(1);
            }
        };
        let (baum, absagen) = gabbro_syntax::lies(datei, &quelle);
        if absagen.absagen.iter().any(|a| a.stufe == Stufe::Fehler) {
            eprintln!("gabbro: {datei} has errors -- the manifest would be incomplete");
            print!("{}", absagen.zeige(&quelle));
            return std::process::ExitCode::from(1);
        }
        alle.extend(manifest::sammle(&baum));
    }
    alle.sort_by(|a, b| a.name.cmp(&b.name));
    print!("{}", manifest::zeige(&alle));
    std::process::ExitCode::SUCCESS
}

fn zaehle_items(baum: &gabbro_syntax::ast::Programm) -> usize {
    fn geh(items: &[gabbro_syntax::ast::Item]) -> usize {
        items
            .iter()
            .map(|i| {
                1 + match &i.art {
                    gabbro_syntax::ast::ItemArt::Modul(m) => geh(&m.items),
                    _ => 0,
                }
            })
            .sum()
    }
    geh(&baum.items)
}
