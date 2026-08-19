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
        // **The emitter, since 2026-08-17.** It covers one fragment, not ten, and refuses by
        // name (`C001`) for every form it does not know -- a generator that guesses undoes
        // every pass in front of it.
        "emit" => {
            if rest.is_empty() {
                eprintln!("gabbro emit: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                // **The checker runs first, and that is the point.** Emitting from a tree the
                // passes have not accepted would produce C for a program Gabbro rejects.
                gabbro_check::pruefe(&baum, &mut absagen);
                let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro emit: {datei} has errors -- no C written");
                    schlecht = true;
                    continue;
                }
                print!("{c}");
            }
            if schlecht {
                std::process::ExitCode::from(1)
            } else {
                std::process::ExitCode::SUCCESS
            }
        }
        "fragmente" => fragmente::befehl(rest),
        "annahmen" => befehl_annahmen(rest),
        "k-bedingung" => {
            if rest.is_empty() {
                eprintln!("gabbro k-bedingung: no file named");
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
                eprintln!("gabbro kosten: no file named");
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
        // **K100.4, Weg (b): das Uebersetzungszeugnis.** Je Datei die Liste dessen, worauf
        // ihre Absenkung ruht -- Annahmen, Schablonen, direkte Formen. *Es beweist die
        // Uebersetzung nicht; es macht aus „der Erzeuger wird schon" eine Aufzaehlung mit
        // Laenge.* Der Pruefer laeuft davor, aus demselben Grund wie bei `emit`.
        // **P6, die Messsonde (2026-08-19).** Die Kennzahl ist zurueckgezogen, weil sie an
        // Verus-Zeilen gemessen war. Was sie ersetzt, braucht eine Beweispflicht, die
        // ENTSTANDEN ist statt erfunden -- und dieses Register zaehlt sie. Der Pruefer laeuft
        // davor, aus demselben Grund wie bei `emit`.
        "kontexte" => {
            if rest.is_empty() {
                eprintln!("gabbro kontexte: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                gabbro_check::pruefe(&baum, &mut absagen);
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro kontexte: {datei} has errors -- no register");
                    schlecht = true;
                    continue;
                }
                print!("{}", gabbro_check::kontexte::zeige(&baum, datei));
            }
            if schlecht {
                return std::process::ExitCode::from(1);
            }
            std::process::ExitCode::SUCCESS
        }
        "pflichten" => {
            if rest.is_empty() {
                eprintln!("gabbro pflichten: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                gabbro_check::pruefe(&baum, &mut absagen);
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro pflichten: {datei} has errors -- no register");
                    schlecht = true;
                    continue;
                }
                print!("{}", gabbro_check::pflichten::zeige(&baum, datei));
            }
            if schlecht {
                return std::process::ExitCode::from(1);
            }
            std::process::ExitCode::SUCCESS
        }
        "zeugnis" => {
            if rest.is_empty() {
                eprintln!("gabbro zeugnis: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                gabbro_check::pruefe(&baum, &mut absagen);
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro zeugnis: {datei} has errors -- no certificate");
                    schlecht = true;
                    continue;
                }
                print!("{}", gabbro_check::zeugnis::zeige(&baum, datei));
            }
            if schlecht {
                std::process::ExitCode::from(1)
            } else {
                std::process::ExitCode::SUCCESS
            }
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
        "gabbro -- compiler and checker for Gabbro (stage P2 + three passes)

  gabbro pruefe     <file.gab>…     read, parse and run the built passes
  gabbro fragmente  <file.md>…      every ```gabbro block of a markdown file, one by one
  gabbro annahmen   <file.gab>…     the assumption manifest: proved under A1…An
  gabbro paesse                     the pass list -- built AND open
  gabbro schablonen                 the generator templates: the third counting column
  gabbro k-bedingung <file.gab>…    per carrier: are ALL write sites generated? (measurement 2)
  gabbro pflichten  <file.gab>…     what a HUMAN still owes -- counted, not discharged
  gabbro kontexte   <file.gab>…     execution contexts per place -- and the COUNT beside it
  gabbro emit       <file.gab>…     lower to C -- and REFUSE by name (`C001`) for every
                                    form this emitter does not know
  gabbro zeugnis    <file.gab>…     what the translation RESTS ON: assumptions, templates
                                    with proof state, foreign bodies, `asm` lines

Exit: 0 when there is no error, 1 on errors, 2 on a wrong call."
    );
}

fn befehl_paesse() {
    println!("The checking passes in fixed order (SPRACHE.md part III, §6):\n");
    for p in passliste() {
        let (marke, note) = match p.zustand {
            Zustand::Gebaut => ("built ", String::new()),
            Zustand::Teilgebaut(w) => ("PART  ", format!("\n         gets through: {w}")),
            Zustand::Getragen(w) => ("CARRY ", format!("\n         the rest, NAMED: {w}")),
            Zustand::Offen(w) => ("OPEN  ", format!("\n         unchecked: {w}")),
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
    let getragen = passliste()
        .iter()
        .filter(|p| matches!(p.zustand, Zustand::Getragen(_)))
        .count();
    println!(
        "\n  {voll} of {} passes fully built, {getragen} CARRIED, {teil} partial.",
        passliste().len()
    );
    println!("  CARRIED means: what a pass can say, it says -- and where the rest lies");
    println!("  stands beside it, WITH AN ADDRESS (axiom layer, template, decision).");
    println!("  PARTIAL means something gets through that ought to fall. OPEN is unchecked.");
    println!("  A green run is therefore not a proof but the absence of the findings");
    println!("  that the built passes are able to see.");
}

fn befehl_pruefe(dateien: &[String]) -> std::process::ExitCode {
    if dateien.is_empty() {
        eprintln!("gabbro pruefe: no file named");
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
                "  M1 saw {} expressions, {} of them without a type ({:.0} % coverage)",
                bericht.m1.gesamt(),
                bericht.m1.unbekannt,
                bericht.m1.deckung()
            );
        }
    }
    println!();
    println!("Not checked in this run:");
    for p in gabbro_check::ungeprueft() {
        match p.zustand {
            Zustand::Offen(w) => println!("  {} {:<14} {w}", p.nummer, p.name),
            Zustand::Getragen(w) => {
                println!("  {} {:<14} CARRIED -- the rest is NAMED: {w}", p.nummer, p.name)
            }
            Zustand::Teilgebaut(w) => {
                println!("  {} {:<14} ONLY PARTIAL -- {w}", p.nummer, p.name)
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
        eprintln!("gabbro annahmen: no file named");
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
    // **Menge, nicht Liste** (`SYNTAX.md` §12). Zwei Dateien duerfen dieselbe Annahme
    // erklaeren -- aber sie zaehlt einmal. Erklaeren sie sie VERSCHIEDEN, ist das ein
    // Widerspruch und kein Duplikat, und dann faellt der Befehl.
    let (alle, streit) = manifest::vereinige(alle);
    if !streit.is_empty() {
        for s in &streit {
            eprintln!("gabbro annahmen: {s}");
        }
        return std::process::ExitCode::from(1);
    }
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
