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
        // **«ABI0»: die Schnittstelle schreiben.** Gueltiger Gabbro-Quelltext, kein zweites
        // Format -- derselbe Parser, dieselben Paesse, kein Register, das auseinanderlaufen
        // kann.
        "abi" => {
            if rest.is_empty() {
                eprintln!("gabbro abi: no file named");
                return std::process::ExitCode::from(2);
            }
            for datei in rest {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    return std::process::ExitCode::from(2);
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                gabbro_check::pruefe(&baum, &mut absagen);
                // **Eine Schnittstelle aus einer Einheit mit Fehlern ist ein Versprechen,
                // das die Einheit selbst nicht haelt.**
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro abi: {datei} has errors -- no interface written");
                    return std::process::ExitCode::from(1);
                }
                print!("{}", gabbro_check::abi::schreibe(&baum, &quelle));
            }
            std::process::ExitCode::SUCCESS
        }
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
        // **Blindstellen: eine Form, die der Korpus nicht ausloest.** Siehe
        // `gabbro_check::blindstellen` -- die Bauart von `mutiere-pruefer.py`, eine Ebene
        // hoeher. *Was 0 Fundstellen hat, ist nicht geprueft, sondern unerreichbar.*
        "blindstellen" => {
            if rest.is_empty() {
                eprintln!("gabbro blindstellen: no file named");
                return std::process::ExitCode::from(2);
            }
            // **Zwei Mengen: der saubere Korpus und das Gift.** Eine Zelle, die im
            // sauberen Korpus leer und im Gift besetzt ist, ist VERBOTEN und bewacht -- der
            // staerkste Zustand, den sie haben kann, und keine Arbeit.
            let (sauber, gift): (Vec<&String>, Vec<&String>) = {
                let mut a = Vec::new();
                let mut b = Vec::new();
                let mut nach_gift = false;
                for d in rest {
                    if d == "--" {
                        nach_gift = true;
                        continue;
                    }
                    if nach_gift { b.push(d) } else { a.push(d) }
                }
                (a, b)
            };
            let mut schlecht = false;
            let lies = |dateien: &[&String], schlecht: &mut bool| {
                let mut aus = Vec::new();
                for datei in dateien {
                    let Ok(quelle) = std::fs::read_to_string(datei) else {
                        eprintln!("gabbro: {datei} not readable");
                        *schlecht = true;
                        continue;
                    };
                    let (baum, _) = gabbro_syntax::lies(datei, &quelle);
                    aus.push(baum);
                }
                aus
            };
            let baeume = lies(&sauber, &mut schlecht);
            let gifte = lies(&gift, &mut schlecht);
            print!("{}", gabbro_check::blindstellen::zeige(&baeume, &gifte));
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
        // **Stufe 2: das erste Instrument fuer Ziel 3 (2026-08-20).** Von den vier Zielen
        // hatte „moeglichst gut nutzbar" als einziges keine Zahl. Der Befehl zaehlt jede
        // Klausel und jede Annotation -- und traegt seine **Kalibrierung mit**: Achse 1 ist
        // gemessen (steht die Tatsache ein zweites Mal da?), Achse 2 ist erklaert (darf die
        // Zahl sinken?). *Ohne die zweite misst „Nutzbarkeit" die Menge aller Klauseln und
        // draengt gegen die Zusage der Sprache.*
        "zeremonie" => {
            if rest.iter().any(|x| x == "--tafel") {
                print!("{}", gabbro_check::zeremonie::tafel());
                return std::process::ExitCode::SUCCESS;
            }
            let ausfuehrlich = rest.iter().any(|x| x == "--je-stelle");
            let dateien: Vec<&String> = rest.iter().filter(|x| !x.starts_with("--")).collect();
            if dateien.is_empty() {
                eprintln!("gabbro zeremonie: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in dateien {
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
                // **Der Pruefer laeuft davor, aus demselben Grund wie bei `emit`.** Eine
                // Zeremoniezahl ueber einem Baum, den die Paesse nicht angenommen haben,
                // zaehlt Klauseln eines Programms, das Gabbro ablehnt.
                gabbro_check::pruefe(&baum, &mut absagen);
                if absagen.fehler_zahl() > 0 {
                    eprint!("{}", absagen.zeige(&quelle));
                    eprintln!("gabbro zeremonie: {datei} has errors -- no count");
                    schlecht = true;
                    continue;
                }
                print!(
                    "{}",
                    gabbro_check::zeremonie::zeige(&baum, &quelle, datei, ausfuehrlich)
                );
            }
            if schlecht {
                return std::process::ExitCode::from(1);
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
        "gabbro -- compiler and checker for Gabbro (stage P2 + three passes)

  gabbro pruefe [--with L.gabi]… <file.gab>…
                                    read, parse and run the built passes
  gabbro abi        <file.gab>…     write the library interface: `pub` declarations,
                                    no bodies -- valid Gabbro, no second format
  gabbro fragmente  <file.md>…      every ```gabbro block of a markdown file, one by one
  gabbro annahmen   <file.gab>…     the assumption manifest: proved under A1…An
  gabbro paesse                     the pass list -- built AND open
  gabbro schablonen                 the generator templates: the third counting column
  gabbro k-bedingung <file.gab>…    per carrier: are ALL write sites generated? (measurement 2)
  gabbro pflichten  <file.gab>…     what a HUMAN still owes -- counted, not discharged
  gabbro kontexte   <file.gab>…     execution contexts per place -- and the COUNT beside it
  gabbro emit       <file.gab>…     lower to C -- and REFUSE by name (`C001`) for every
                                    form this emitter does not know
  gabbro blindstellen <clean>… [-- <poison>…]
                                    FORM x POSITION over a corpus -- and the EMPTY cells.
                                    What has 0 sites is not checked but UNREACHABLE
  gabbro zeugnis    <file.gab>…     what the translation RESTS ON: assumptions, templates
                                    with proof state, foreign bodies, `asm` lines
  gabbro zeremonie  [--je-stelle | --tafel] <file.gab>…
                                    every clause and annotation, in three columns --
                                    derivable / redundant / load-bearing. The CALIBRATION
                                    travels with the tool: `--tafel` prints, per rule,
                                    whether its number may fall AND why

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

fn befehl_pruefe(argumente: &[String]) -> std::process::ExitCode {
    // **«ABI1»: `--with <lib.gabi>` zieht eine Schnittstelle HINZU.**
    //
    // Die Datei ist Gabbro-Quelltext; sie wird vor die zu pruefende Einheit gestellt, und
    // damit loesen die Namen auf. *`E009` und `K003` verschwinden dann, WEIL geprueft wird
    // -- nicht, weil geschwiegen wird.*
    let mut dateien: Vec<String> = Vec::new();
    let mut mit: Vec<String> = Vec::new();
    let mut i = 0;
    while i < argumente.len() {
        if argumente[i] == "--with" {
            match argumente.get(i + 1) {
                Some(n) => mit.push(n.clone()),
                None => {
                    eprintln!("gabbro pruefe: `--with` needs a `.gabi` file");
                    return std::process::ExitCode::from(2);
                }
            }
            i += 2;
        } else {
            dateien.push(argumente[i].clone());
            i += 1;
        }
    }
    if dateien.is_empty() {
        eprintln!("gabbro pruefe: no file named");
        return std::process::ExitCode::from(2);
    }
    let mut vorspann = String::new();
    for m in &mit {
        match std::fs::read_to_string(m) {
            Ok(q) => {
                if !q.starts_with(gabbro_check::abi::MARKE) {
                    eprintln!("gabbro pruefe: {m} is not a `.gabi` (missing `{}`)",
                              gabbro_check::abi::MARKE);
                    return std::process::ExitCode::from(2);
                }
                vorspann.push_str(&q);
                vorspann.push('\n');
            }
            Err(e) => {
                eprintln!("gabbro: {m}: {e}");
                return std::process::ExitCode::from(2);
            }
        }
    }
    let mut fehler = 0usize;
    for datei in &dateien {
        let quelle = match std::fs::read_to_string(datei) {
            Ok(q) => q,
            Err(e) => {
                eprintln!("gabbro: {datei}: {e}");
                fehler += 1;
                continue;
            }
        };
        // **Der Vorspann steht VOR der Einheit**, damit die Spannen der Einheit stimmen --
        // sonst zeigt jede Meldung auf die falsche Zeile.
        let ganz = if vorspann.is_empty() {
            quelle.clone()
        } else {
            format!("{vorspann}\n{quelle}")
        };
        let versatz = ganz.len() - quelle.len();
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &ganz);
        let bericht = pruefe(&baum, &mut absagen);
        // Meldungen, die in den Vorspann zeigen, gehoeren der Bibliothek und nicht dieser
        // Einheit -- sie werden hier nicht gedruckt.
        // **Aber nur HINWEISE.** Ein FEHLER im Vorspann heisst, dass die Schnittstelle selbst
        // nicht traegt -- den zu verschlucken hiesse, dem Importeur eine kaputte Bibliothek
        // als sauber zu verkaufen. *Die erste Fassung filterte beides und hat damit ein
        // `N001` in der eigenen `.gabi` verdeckt.*
        if versatz > 0 {
            let kaputt = absagen
                .absagen
                .iter()
                .any(|a| (a.span.von as usize) < versatz && a.stufe == gabbro_syntax::Stufe::Fehler);
            if kaputt {
                print!("{}", absagen.zeige(&ganz));
                eprintln!("gabbro pruefe: the interface itself does not hold -- nothing checked");
                return std::process::ExitCode::from(1);
            }
            absagen.absagen.retain(|a| a.span.von as usize >= versatz);
        }
        if !absagen.leer() {
            print!("{}", absagen.zeige(&ganz));
        }
        let f = absagen.fehler_zahl();
        let h = absagen.absagen.len() - f;
        fehler += f;
        println!(
            "{datei}: {} Items, {f} Fehler, {h} Hinweise",
            zaehle_items(&baum)
        );
        // **Folgefehler: die Paesse laufen nach einer Absage des LESERS weiter** -- und
        // was sie danach melden, kann Truemmer sein. Der Ausschnitt `SYNTAX.md`:533
        // scheitert am Parser («B8»), damit wird seine `spec fn` nie erklaert, und
        // `maintains` meldet einen Namen, den es sehr wohl gibt.
        //
        // **Entschieden am 2026-08-20 (Stufe 2): NICHT anhalten, aber SAGEN.**
        //
        // > Anhalten hiesse, dass ein Lesefehler im dritten Item einen echten `M101` im
        // > ersten verdeckt -- **Rauschen gegen Schweigen getauscht**, und dieser Ordner
        // > haelt Schweigen fuer das teurere von beiden. *Die Zeile unten ist der dritte
        // > Zustand, dieselbe Bauart wie `E009` und `S007`: weder abgesagt noch bestaetigt,
        // > aber sichtbar.*
        let lesefehler: Vec<u32> = absagen
            .absagen
            .iter()
            .filter(|a| {
                a.stufe == gabbro_syntax::Stufe::Fehler
                    && (a.code.starts_with('P') || a.code.starts_with('L'))
            })
            .map(|a| a.span.von)
            .collect();
        if let Some(erste) = lesefehler.iter().min() {
            let danach = absagen
                .absagen
                .iter()
                .filter(|a| {
                    !(a.code.starts_with('P') || a.code.starts_with('L')) && a.span.von >= *erste
                })
                .count();
            println!(
                "  {} reader refusal(s), and the passes did NOT stop: {danach} later \
                 diagnostics may be CONSEQUENCES",
                lesefehler.len()
            );
            println!(
                "  a body that never parsed declares no names -- what a pass says about it \
                 is not a finding"
            );
        }
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
