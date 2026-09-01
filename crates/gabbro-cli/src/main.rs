//! `gabbro` -- die Kommandozeile.
//!
//! Vier Befehle, und der wichtigste ist `paesse`: er sagt, **was dieser Uebersetzer nicht
//! prueft.** Ein Werkzeug, das nur meldet, was es gefunden hat, laesst ungeprueftes Schweigen
//! wie ein Gruen aussehen.

use gabbro_check::{manifest, passliste, pruefe, Zustand};
use gabbro_syntax::diag::Stufe;

mod bau;
mod fragmente;

/// **A reader that stops reading must not look like a crash.**
///
/// Rust sets `SIGPIPE` to `SIG_IGN` before `main` runs, so a write into a closed pipe does
/// not end the process -- it fails with `EPIPE`, and `println!` turns that failure into a
/// panic. `gabbro pruefe f.gab | head` therefore ended with **`rc=101` and a panic message**,
/// for the most ordinary thing a reader can do to a long output. *Measured 2026-08-31: 101
/// through a pipe, 0 without one.*
///
/// **The usual repair is closed to this workspace twice over.** `signal(SIGPIPE, SIG_DFL)`
/// needs `unsafe`, and the workspace sets `unsafe_code = "forbid"`; it also needs `libc`, and
/// the dependency list is empty by policy -- std alone, nothing beside it. So the panic is
/// answered where it arrives instead of being prevented.
///
/// **The marker is std's own literal, not the operating system's message.** `std::io` panics
/// with `failed printing to stdout: {e}`: the prefix is a constant inside `std`, while the
/// `{e}` behind it comes from `strerror` and is therefore **locale-dependent**. Matching the
/// prefix holds under `de_DE.UTF-8`; matching `Broken pipe` would not -- the same class the
/// locale requirement in `pruefe-waechter.py` was written for, and the same class as the
/// linker emitting its own diagnostics in German.
///
/// > **What this does NOT tell apart:** a full disk reaches this hook by the same path as a
/// > closed pipe, and also ends quietly with 0. Separating them needs the `io::Error` kind,
/// > and a panic carries only a formatted string. *The limit is named here rather than
/// > hidden* (W10).
fn quiet_on_closed_output() {
    let vorher = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |lage| {
        let text = lage
            .payload()
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| lage.payload().downcast_ref::<&str>().copied())
            .unwrap_or("");
        // `stdout` and `stderr` both -- a pager closed early is not a fault of the checker.
        if text.starts_with("failed printing to std") {
            std::process::exit(0);
        }
        vorher(lage);
    }));
}

fn main() -> std::process::ExitCode {
    quiet_on_closed_output();
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
            // **«A4»: `--berechnet` prints the COMPUTED effect list, `--vergleich` the
            // difference to the written one.**
            //
            // The call graph has been computing the hull all along
            // (`huelle_der_gerufenen`), and until today this command printed the
            // DECLARATION straight back. *No elaborator is built here -- what is measured
            // is whether one would be worth building.*
            let berechnet = rest.iter().any(|a| a == "--berechnet");
            let vergleich = rest.iter().any(|a| a == "--vergleich");
            // **`--weit` also counts the reads over parameters.** The difference between
            // the two runs IS the measurement: it says how much still lies between the pass
            // that CHECKS the line and an elaborator that would WRITE it.
            let weit = rest.iter().any(|a| a == "--weit");
            let rest: Vec<&String> = rest.iter().filter(|a| !a.starts_with("--")).collect();
            if rest.is_empty() {
                eprintln!("gabbro abi: no file named");
                return std::process::ExitCode::from(2);
            }
            if vergleich {
                return befehl_abi_vergleich(&rest, weit);
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
                if berechnet {
                    print!("{}", gabbro_check::abi::schreibe_berechnet(&baum, &quelle));
                } else {
                    print!("{}", gabbro_check::abi::schreibe(&baum, &quelle));
                }
            }
            std::process::ExitCode::SUCCESS
        }
        "check" | "pruefe" => befehl_pruefe(befehl, rest),
        // **`gabbro build` -- the build out of a manifest** (German second name `bau`). The
        // reckoning that decided its shape stands in `dokumente/BAUSYSTEM.md`, and it was
        // written before the first line of `bau.rs`.
        "build" | "bau" => bau::befehl(rest),
        // The emitter, since 2026-08-17 -- what it covers and what it refuses stands at
        // `command_emit` below, where the code is.
        "emit" => command_emit(befehl, rest),
        "fragments" | "fragmente" => fragmente::befehl(rest),
        "assumptions" | "annahmen" => befehl_annahmen(rest),
        "k-condition" | "k-bedingung" => {
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
        // **«T1»: the DERIVED effect set, and it is retrievable** (`PLAN-HARDWARE.md` §25).
        //
        // Deriving the line instead of demanding it **trades locality for writing work**:
        // `E005` today quotes the very statement that breaks the frame, and after the
        // derivation the contradiction surfaces at a caller, at a lock-rank check, at a
        // `pure` three levels up. *The same shape as `op_zeichen`: a refusal that cannot
        // quote the line it is about.*
        //
        // That trade is payable, and this command is half the price: **whoever is refused
        // somewhere else can ask here where the effect comes from.** `--ursprung` prints the
        // path, hop by hop, down to the body that does the deed or to the edge where a
        // declaration is the source.
        "effects" | "wirkungen" => befehl_wirkungen(rest),
        "costs" | "kosten" => {
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
        // **`alias` counts an AREA and decides nothing.** It exists because `m3.rs` says of
        // itself that it is no alias analyser, and that sentence is honest without being a
        // number. *A measured area makes the later decision possible; an analysis built
        // without a decision is trust surface.*
        //
        // Unlike `kontexte` it does NOT abort on a unit with errors: a count over a corpus
        // must not shrink because one file in it is red -- that would make the figure depend
        // on the state of an unrelated pass.
        "alias" => {
            if rest.is_empty() {
                eprintln!("gabbro alias: no file named");
                return std::process::ExitCode::from(2);
            }
            let leise = rest.iter().any(|a| a == "--summe");
            let rest: Vec<&String> = rest.iter().filter(|a| a.as_str() != "--summe").collect();
            let mut schlecht = false;
            let mut summe = gabbro_check::alias::Flaeche::default();
            let mehrere = rest.len() > 1;
            for datei in &rest {
                let datei = datei.as_str();
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    schlecht = true;
                    continue;
                };
                let (baum, _) = gabbro_syntax::lies(datei, &quelle);
                let f = gabbro_check::alias::erhebe(&baum);
                if !leise {
                    print!("{}", gabbro_check::alias::tafel_von(&f, datei));
                }
                summe.dazu(f);
            }
            if mehrere || leise {
                print!(
                    "{}",
                    gabbro_check::alias::tafel(summe, &format!("TOTAL over {} units", rest.len()))
                );
            }
            if schlecht {
                return std::process::ExitCode::from(1);
            }
            std::process::ExitCode::SUCCESS
        }
        "contexts" | "kontexte" => {
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
        // **P6, the second half.** `pflichten` prints what a human still owes; `--isabelle`
        // prints the SAME register as an Isabelle theory. *Not a second subcommand, because
        // it is not a second register* -- `refinement::verdicts` walks exactly the list
        // `pflichten::sammle` counts, and the theory header carries the sum.
        "obligations" | "pflichten" => {
            let isabelle = rest.iter().any(|a| a == "--isabelle");
            // **`--lean` is the SAME register again, through the body channel.** Not a
            // second subcommand and not a second register: `lean::verdicts` walks exactly
            // the list `pflichten::sammle` counts, in the same order, and the two channels
            // can therefore be held against each other obligation by obligation.
            let lean = rest.iter().any(|a| a == "--lean");
            let rest: Vec<&String> = rest
                .iter()
                .filter(|a| a.as_str() != "--isabelle" && a.as_str() != "--lean")
                .collect();
            if isabelle && lean {
                eprintln!("gabbro pflichten: `--isabelle` and `--lean` name two provers -- pick one");
                return std::process::ExitCode::from(2);
            }
            if rest.is_empty() {
                eprintln!("gabbro pflichten: no file named");
                return std::process::ExitCode::from(2);
            }
            let mut schlecht = false;
            for datei in rest {
                let datei = datei.as_str();
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
                if isabelle {
                    print!("{}", gabbro_check::refinement::theory(&baum, datei));
                } else if lean {
                    print!("{}", gabbro_check::lean::module(&baum, datei));
                } else {
                    print!("{}", gabbro_check::pflichten::zeige(&baum, datei));
                }
            }
            if schlecht {
                return std::process::ExitCode::from(1);
            }
            std::process::ExitCode::SUCCESS
        }
        // **`gabbro lean` -- the whole PROGRAM as a Lean 4 datum, and it carries no
        // specification.** `pflichten --lean` writes the obligations Gabbro's own
        // `spec fn`/`refines` pair states; this one writes the program and stops, so that a
        // HAND-WRITTEN Lean specification can be held against it.
        //
        // *Several files become ONE program*, because a specification is about a program and
        // not about a file: a body in one unit and the table it writes in another are one
        // statement, and two modules could not say it.
        "lean" => {
            if rest.is_empty() {
                eprintln!("gabbro lean: no file named");
                return std::process::ExitCode::from(2);
            }
            // **The files are joined into ONE source and parsed ONCE**, and that is the whole
            // point of the subcommand. Checking each file on its own is what `pruefe` does,
            // and it is right there: a unit is a compilation unit. *But a specification is
            // about a PROGRAM* -- a body in one file and the table it writes in another are
            // one statement, and two separately checked units could not make it.
            //
            // The price is named rather than hidden: an error renders against the JOINED
            // text, so its line number is not the line number in the file it came from. A
            // per-file offset map would fix that and is not built -- `gabbro pruefe` is the
            // command for finding errors, and this one refuses rather than reports.
            let mut ganz = String::new();
            let mut quellen = Vec::new();
            for datei in rest {
                let datei = datei.as_str();
                let Ok(quelle) = std::fs::read_to_string(datei) else {
                    eprintln!("gabbro: {datei} not readable");
                    return std::process::ExitCode::from(1);
                };
                ganz.push_str(&format!("-- >>> {datei}\n"));
                ganz.push_str(&quelle);
                ganz.push('\n');
                quellen.push(datei.to_string());
            }
            let (baum, mut absagen) = gabbro_syntax::lies("<program>", &ganz);
            gabbro_check::pruefe(&baum, &mut absagen);
            // **A program with errors carries no export.** Stricter than `pflichten` on
            // purpose: one broken file leaves a program that is missing a table, and a
            // specification about a missing table is VACUOUS rather than false -- and
            // vacuous reads exactly like proved.
            if absagen.fehler_zahl() > 0 {
                eprint!("{}", absagen.zeige(&ganz));
                eprintln!(
                    "gabbro lean: the program has errors -- no export ({} files joined, in order: {})",
                    quellen.len(),
                    quellen.join(", ")
                );
                return std::process::ExitCode::from(1);
            }
            print!("{}", gabbro_check::lean::program(&baum, &quellen));
            std::process::ExitCode::SUCCESS
        }
        // **Blindstellen: eine Form, die der Korpus nicht ausloest.** Siehe
        // `gabbro_check::blindstellen` -- die Bauart von `mutiere-pruefer.py`, eine Ebene
        // hoeher. *Was 0 Fundstellen hat, ist nicht geprueft, sondern unerreichbar.*
        "blindspots" | "blindstellen" => {
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
        "certificate" | "zeugnis" => {
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
                print!("{}", gabbro_check::zeugnis::zeige(&baum, datei, &quelle));
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
        "ceremony" | "zeremonie" => {
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
        // **Zahn 3, mechanisch seit 2026-08-20 (Stufe 5).** Bis dahin war die Ratsche ein
        // Satz im Register: *„jede bewiesene Schablone bindet ihre Praemissen an einen
        // Pass."* Das Werkzeug druckte die haengenden ehrlich aus und gab **0** zurueck.
        //
        // > **Ein Beweis, dessen Voraussetzung niemand herstellt, ist gefaehrlicher als eine
        // > ungeprueufte Zusage -- weil ein Isabelle-Haekchen darueber steht.** Der
        // > Registerversatz war genau das: bewiesener Satz, keine Prueferzeile.
        //
        // `--tor` faellt, solange eine haengt. Es ist ausdruecklich KEIN Vorgabeverhalten:
        // ein Werkzeug, das jeden Tag rot ist, wird nicht gelesen -- die tägliche Wache ist
        // die Ratsche in `pruefe-schablonen.py`, und **dieses Tor ist das ZIEL.**
        "templates" | "schablonen" => {
            print!("{}", gabbro_check::schablonen::zeige());
            if rest.iter().any(|x| x == "--tor") {
                let luft = gabbro_check::schablonen::in_der_luft();
                if !luft.is_empty() {
                    eprintln!(
                        "gabbro schablonen --tor: {} premises of PROVED templates have no \
                         pass -- a proof nothing establishes",
                        luft.len()
                    );
                    return std::process::ExitCode::from(1);
                }
                println!("-- TOOTH 3 REACHED: every proved template binds its premises.");
            }
            std::process::ExitCode::SUCCESS
        }
        // **Das PASSREGISTER haengt hier dran, nicht an einem eigenen Befehl** (PL.1): der
        // Satz gehoert zum Pass, und zwei Befehle fuer eine Liste waeren zwei Wahrheiten.
        "passes" | "paesse" => {
            befehl_paesse();
            print!(
                "{}",
                gabbro_check::saetze::zeige(rest.iter().any(|x| x == "--je-satz"))
            );
            std::process::ExitCode::SUCCESS
        }
        "--help" | "help" | "--hilfe" | "-h" | "hilfe" => {
            hilfe();
            std::process::ExitCode::SUCCESS
        }
        anderes => {
            eprintln!("gabbro: unknown command `{anderes}`");
            hilfe();
            std::process::ExitCode::from(2)
        }
    }
}

fn hilfe() {
    eprintln!(
        "gabbro -- compiler and checker for Gabbro (stage P2 + three passes)

  gabbro check|pruefe [--with L.gabi]… [--unit] [--paesse] <file.gab>…
                                    read, parse and run the built passes. The \"not checked
                                    in this run\" register is SUMMARISED (count per state and
                                    a fingerprint); `--paesse` prints it in full. *It is a
                                    property of the binary, not of the file* -- printing
                                    1 122 words of it beside 20 words of finding, at every
                                    run, is a disclosure nobody reads
  gabbro abi        <file.gab>…     write the library interface: `pub` declarations,
                                    no bodies -- valid Gabbro, no second format
  gabbro fragments|fragmente <file.md>…
                                    every ```gabbro block of a markdown file, one by one
  gabbro assumptions|annahmen <file.gab>…
                                    the assumption manifest: proved under A1…An
  gabbro passes|paesse [--je-satz]  the pass list -- built AND open -- and THE PASS
                                    REGISTER: the sentence each pass owes, with its
                                    state. `--je-satz` prints each sentence in full
  gabbro templates|schablonen [--tor]
                                    the generator templates: the third counting column.
                                    `--tor` FALLS while a proved template has a premise
                                    no pass establishes (tooth 3)
  gabbro k-condition|k-bedingung <file.gab>…
                                    per carrier: are ALL write sites generated? (measurement 2)
  gabbro costs|kosten <file.gab>…   the cost report per routine
  gabbro build|bau [--testbuild] [--dry-run] [<manifest>]
                                    the build out of a manifest: it computes the unit graph
                                    from `module` and `use` -- never from a manifest line --
                                    and is incremental by CONTENT, not by timestamp. It
                                    prints what it built AND what it did not look at.
                                    The reckoning: `dokumente/BAUSYSTEM.md`
  gabbro obligations|pflichten [--isabelle | --lean] <file.gab>…
                                    what a HUMAN still owes -- counted, not discharged.
                                    `--isabelle` writes the SAME register as an Isabelle
                                    theory: every obligation appears, as a goal or as a
                                    NAMED refusal, and the header carries `goals + refused
                                    = total`
  gabbro contexts|kontexte <file.gab>…
                                    execution contexts per place -- and the COUNT beside it
  gabbro alias      <file.gab>…     the ALIAS SURFACE in five strata -- how much of a corpus
                                    a missing alias analysis could be about. Two upper
                                    bounds and two lower ones, printed together; no refusal
  gabbro emit [--with L.gabi]… [--testbuild] <file.gab>…
                                    lower to C -- and REFUSE by name (`C001`) for every
                                    form this emitter does not know. A `.gabi` lowers to a
                                    C HEADER: typedefs and prototypes, no objects.
                                    WITHOUT `--testbuild` this is the SHIPPING build: an
                                    item marked `when TESTBUILD` produces no line of C
  gabbro lean       <file.gab>…     the whole PROGRAM as a Lean 4 module: every body, every
                                    precondition, and the shape of every declared place --
                                    and NO specification. What is to hold is said in Lean,
                                    by a person. Several files become ONE program
  gabbro blindspots|blindstellen <clean>… [-- <poison>…]
                                    FORM x POSITION over a corpus -- and the EMPTY cells.
                                    What has 0 sites is not checked but UNREACHABLE
  gabbro certificate|zeugnis <file.gab>…
                                    what the translation RESTS ON: assumptions, templates
                                    with proof state, foreign bodies, `asm` lines
  gabbro ceremony|zeremonie [--je-stelle | --tafel] <file.gab>…
                                    every clause and annotation, in three columns --
                                    derivable / redundant / load-bearing. The CALIBRATION
                                    travels with the tool: `--tafel` prints, per rule,
                                    whether its number may fall AND why

Every subcommand has an ENGLISH first name; the German second name keeps working and is
printed after the `|`. A refusal names the spelling that was TYPED, not the first name --
otherwise a run under the second name would report a command nobody called (W16).

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

/// **Split `--with <lib.gabi>` off from the files.** Since 2026-08-21 `pruefe` and `emit`
/// cross the SAME bridge -- two parsers for one flag would be two registers over the same
/// thing, and this folder is written against exactly that class.
fn split_with(
    befehl: &str,
    argumente: &[String],
) -> Result<(Vec<String>, Vec<String>), std::process::ExitCode> {
    let mut dateien: Vec<String> = Vec::new();
    let mut mit: Vec<String> = Vec::new();
    let mut i = 0;
    while i < argumente.len() {
        if argumente[i] == "--with" {
            match argumente.get(i + 1) {
                Some(n) => mit.push(n.clone()),
                None => {
                    eprintln!("gabbro {befehl}: `--with` needs a `.gabi` file");
                    return Err(std::process::ExitCode::from(2));
                }
            }
            i += 2;
        } else {
            dateien.push(argumente[i].clone());
            i += 1;
        }
    }
    if dateien.is_empty() {
        eprintln!("gabbro {befehl}: no file named");
        return Err(std::process::ExitCode::from(2));
    }
    Ok((dateien, mit))
}

/// **The interfaces as ONE preamble.** It is put in front of the unit, so the same parser
/// reads them and the same passes check them.
///
/// *The marker is demanded, not guessed:* taking an arbitrary `.gab` file as `--with` would
/// mean fusing two translation units and calling the result a library.
fn read_preamble(befehl: &str, mit: &[String]) -> Result<String, std::process::ExitCode> {
    let mut vorspann = String::new();
    for m in mit {
        match std::fs::read_to_string(m) {
            Ok(q) => {
                if !q.starts_with(gabbro_check::abi::MARKE) {
                    eprintln!(
                        "gabbro {befehl}: {m} is not a `.gabi` (missing `{}`)",
                        gabbro_check::abi::MARKE
                    );
                    return Err(std::process::ExitCode::from(2));
                }
                vorspann.push_str(&q);
                vorspann.push('\n');
            }
            Err(e) => {
                eprintln!("gabbro: {m}: {e}");
                return Err(std::process::ExitCode::from(2));
            }
        }
    }
    Ok(vorspann)
}

/// **The emitter, since 2026-08-17.** It covers one fragment, not ten, and refuses by name
/// (`C001`) for every form it does not know -- a generator that guesses undoes every pass in
/// front of it.
///
/// **`--with` since 2026-08-21.** Without it the ABI was a half one: `pruefe --with` accepted
/// the library, `emit` did not -- a program of two files could be checked and not translated.
/// *Measured: a `.gabi` through the generator is exactly a C HEADER* -- `typedef`, `#define`
/// and prototypes, **not a single object**. So the preamble in the output is what it would be
/// in C anyway, and two units link without a duplicate symbol.
fn command_emit(getippt: &str, argumente: &[String]) -> std::process::ExitCode {
    // **`--testbuild` opens the build gate, and its ABSENCE is the shipping build.**
    //
    // *The default is the closed gate on purpose.* Whoever forgets the flag loses check code
    // out of a check build -- a missing symbol, and loud. The other default would put the
    // check harness into the shipped artefact, and nothing would say so.
    let pruefbau = argumente.iter().any(|a| a == "--testbuild");
    let argumente: Vec<String> =
        argumente.iter().filter(|a| a.as_str() != "--testbuild").cloned().collect();
    let (dateien, mit) = match split_with(getippt, &argumente) {
        Ok(x) => x,
        Err(c) => return c,
    };
    let bau = if pruefbau {
        gabbro_check::gatter::Bau::Pruefbau
    } else {
        gabbro_check::gatter::Bau::Auslieferung
    };
    let vorspann = match read_preamble(getippt, &mit) {
        Ok(v) => v,
        Err(c) => return c,
    };
    let mut schlecht = false;
    // **A build is more than one file** (the ABI work, 2026-08-25). The C name is the
    // Gabbro name, and two units of ONE run that both carry a `pub fn lesen` emit the same
    // symbol twice. *Within one tree `bindung::pass` catches that; across the trees it takes
    // a register, and it stands here because the file list stands here.*
    //
    // **The refusal still comes out of `gabbro-check`** -- a code belongs to exactly one
    // file, or every poison probe on it is ambiguous.
    let mut register = gabbro_check::bindung::Bindungsregister::neu();
    for datei in &dateien {
        let Ok(quelle) = std::fs::read_to_string(datei) else {
            eprintln!("gabbro: {datei} not readable");
            schlecht = true;
            continue;
        };
        let ganz = if vorspann.is_empty() {
            quelle.clone()
        } else {
            format!("{vorspann}\n{quelle}")
        };
        let versatz = ganz.len() - quelle.len();
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &ganz);
        // **The checker runs first, and that is the point.** Emitting from a tree the
        // passes have not accepted would produce C for a program Gabbro rejects.
        gabbro_check::pruefe(&baum, &mut absagen);
        register.nimm_auf(datei, &baum, versatz, &mut absagen);
        let c = gabbro_check::emit::emittiere_mit(&baum, &mut absagen, bau);
        if absagen.fehler_zahl() > 0 {
            eprint!("{}", absagen.zeige(&ganz));
            eprintln!("gabbro {getippt}: {datei} has errors -- no C written");
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

/// One file of a joined unit, and where its text sits in the joined source.
///
/// **The byte range is the whole point.** Without it a refusal that comes out of the joined
/// parse carries a line number from the CONCATENATION -- which is a line number in no file
/// at all. `gabbro lean` names that price in its own comment and pays it; this map is the
/// thing it says is not built.
pub(crate) struct Stueck {
    pub datei: String,
    pub quelle: String,
    pub von: usize,
    pub bis: usize,
}

/// **The refusals of a joined parse, rendered into the files they came from.**
///
/// One bucket per piece, every refusal shifted back by that piece's start offset and rendered
/// against that piece's OWN source -- so the site is the site in the file, not in the
/// concatenation. Returns the refusals that fitted into no piece; **they are handed back
/// rather than dropped**, because a partition that swallows what it cannot place looks
/// exactly like a clean run.
///
/// `gabbro build` renders the same way, out of the same function -- two renderings of one
/// joined parse would be a second register over the same thing.
pub(crate) fn zeige_je_stueck(
    absagen: &gabbro_syntax::Absagen,
    stuecke: &[Stueck],
    je_datei: &mut dyn FnMut(&str, &gabbro_syntax::Absagen),
) -> Vec<gabbro_syntax::diag::Absage> {
    let mut gezeigt = vec![false; absagen.absagen.len()];
    for s in stuecke {
        let mut eigene = gabbro_syntax::Absagen::neu(&s.datei);
        for (i, a) in absagen.absagen.iter().enumerate() {
            let v = a.span.von as usize;
            if v < s.von || v >= s.bis {
                continue;
            }
            gezeigt[i] = true;
            let mut a = a.clone();
            a.span.von -= s.von as u32;
            a.span.bis = a.span.bis.saturating_sub(s.von as u32);
            eigene.schiebe(a);
        }
        if !eigene.leer() {
            print!("{}", eigene.zeige(&s.quelle));
        }
        je_datei(&s.datei, &eigene);
    }
    (0..absagen.absagen.len())
        .filter(|i| !gezeigt[*i])
        .map(|i| absagen.absagen[i].clone())
        .collect()
}

/// **`gabbro pruefe --unit a.gab b.gab` -- the named files as ONE translation unit.**
///
/// Why this is a flag and not the default: *a unit is a compilation unit*, and the file list
/// on a command line is not by itself a statement that these files belong together. The
/// tooling in `instrumente/` runs ONE PROCESS PER FILE on purpose
/// (`zaehle-gifttreffer.py`:146), and joining the whole corpus would make every module name
/// that appears twice in two unrelated files an `N039`. **What files form a unit is a
/// manifest line, not a shell glob.**
///
/// What it buys is measured in `messung/EINHEITENSICHT.md`: over five units of the corpus
/// eleven refusals fall away *because the names resolve*, and two appear that no per-file run
/// can see -- a lock ring across library boundaries (`H012`). *Silence is not the only thing
/// joining buys; it also buys a finding.*
///
/// The resolver needed no change. `umgebung.rs::kandidaten` walks the module chain outward
/// and follows the `use` lines; it was module-aware and `use`-aware all along. **What it never
/// got was the other file.**
fn pruefe_als_einheit(
    getippt: &str,
    dateien: &[String],
    vorspann: &str,
    voll: bool,
) -> std::process::ExitCode {
    let mut ganz = String::new();
    if !vorspann.is_empty() {
        ganz.push_str(vorspann);
        ganz.push('\n');
    }
    // Everything before this offset belongs to the interfaces, not to the unit.
    let vorspann_ende = ganz.len();
    let mut stuecke: Vec<Stueck> = Vec::new();
    for datei in dateien {
        let quelle = match std::fs::read_to_string(datei) {
            Ok(q) => q,
            Err(e) => {
                eprintln!("gabbro: {datei}: {e}");
                return std::process::ExitCode::from(2);
            }
        };
        let von = ganz.len();
        ganz.push_str(&quelle);
        // **Always a newline, never a conditional one.** A file that ends without one would
        // otherwise glue its last token to the next file's first, and the joined parse would
        // read a construct that stands in no source.
        ganz.push('\n');
        let bis = ganz.len();
        stuecke.push(Stueck { datei: datei.clone(), quelle, von, bis });
    }

    let (baum, mut absagen) = gabbro_syntax::lies("<unit>", &ganz);
    let bericht = pruefe(&baum, &mut absagen);
    // **One unit, one name in the register.** Passing each file separately here would report
    // the unit's own second carrier of a name as a cross-unit collision -- which is what
    // `bindung::nimm_auf` already guards against for the same file named twice.
    let mut register = gabbro_check::bindung::Bindungsregister::neu();
    register.nimm_auf("<unit>", &baum, vorspann_ende, &mut absagen);

    // A FEHLER inside the preamble means the interface itself does not hold. Same rule as in
    // the per-file path, and for the same reason: swallowing it sells a broken library as
    // clean.
    if vorspann_ende > 0 {
        let kaputt = absagen.absagen.iter().any(|a| {
            (a.span.von as usize) < vorspann_ende && a.stufe == gabbro_syntax::Stufe::Fehler
        });
        if kaputt {
            print!("{}", absagen.zeige(&ganz));
            eprintln!("gabbro {getippt}: the interface itself does not hold -- nothing checked");
            return std::process::ExitCode::from(1);
        }
    }

    // **Every refusal goes into exactly one bucket, and what fits nowhere is PRINTED.**
    // A partition that drops what it cannot place looks exactly like a clean run.
    let mut fehler = 0usize;
    let mut hinweise = 0usize;
    let mut items_gesamt = 0usize;
    let bereiche: Vec<(usize, usize)> = stuecke.iter().map(|s| (s.von, s.bis)).collect();
    let mut i_stueck = 0usize;
    let rest = zeige_je_stueck(&absagen, &stuecke, &mut |datei, eigene| {
        let f = eigene.fehler_zahl();
        let h = eigene.absagen.len() - f;
        fehler += f;
        hinweise += h;
        let (von, bis) = bereiche[i_stueck];
        i_stueck += 1;
        let items = items_im_bereich(&baum, von, bis);
        items_gesamt += items;
        println!("{datei}: {items} items, {f} errors, {h} hints");
    });
    // Refusals that landed in the preamble (hints only -- the errors aborted above) or
    // carry a span outside every piece. **They are named, not dropped.**
    if !rest.is_empty() {
        let mut fremd = gabbro_syntax::Absagen::neu("<interface>");
        for a in &rest {
            fremd.schiebe(a.clone());
        }
        let f = fremd.fehler_zahl();
        println!(
            "  {} refusal(s) fell outside every file of the unit ({f} of them errors) -- \
             they belong to the `--with` preamble, and their line numbers are the \
             PREAMBLE's, not any file's",
            rest.len()
        );
        fehler += f;
    }
    println!(
        "unit of {} file(s): {items_gesamt} items, {fehler} errors, {hinweise} hints",
        stuecke.len()
    );
    if bericht.m1.gesamt() == 0 {
        println!("  M1 saw no expression -- this unit has no function body");
    } else {
        println!(
            "  M1 saw {} expressions, {} of them without a type ({:.0} % coverage)",
            bericht.m1.gesamt(),
            bericht.m1.unbekannt,
            bericht.m1.deckung()
        );
    }
    println!();
    if voll {
        print!("{}", register_voll());
    } else {
        print!("{}", register_kurz());
    }
    if fehler == 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::from(1)
    }
}

/// Items whose site lies inside the half-open byte range of the joined source, nested ones
/// counted the way `zaehle_items` counts them.
fn items_im_bereich(baum: &gabbro_syntax::ast::Programm, von: usize, bis: usize) -> usize {
    fn geh(items: &[gabbro_syntax::ast::Item], von: usize, bis: usize) -> usize {
        items
            .iter()
            .map(|i| {
                let drin = (i.span.von as usize) >= von && (i.span.von as usize) < bis;
                usize::from(drin)
                    + match &i.art {
                        gabbro_syntax::ast::ItemArt::Modul(m) => geh(&m.items, von, bis),
                        _ => 0,
                    }
            })
            .sum()
    }
    geh(&baum.items, von, bis)
}

fn befehl_pruefe(getippt: &str, argumente: &[String]) -> std::process::ExitCode {
    // **`--paesse` prints the FULL register, and since 2026-08-25 it no longer prints
    // itself.** See `register_kurz` for the measurement and the reason.
    let voll = argumente.iter().any(|a| a == "--paesse");
    // **`--unit` checks the named files as ONE translation unit** (German second name
    // `--einheit`; NOT called an alias here -- `gabbro alias` is a subcommand about POINTER
    // aliasing, and one word for two things is how a register starts to drift). Without it every file is its own unit -- see the loop below, and see
    // `pruefe_als_einheit` for what changes and what the flag costs.
    let einheit = argumente.iter().any(|a| a == "--unit" || a == "--einheit");
    let argumente: Vec<String> = argumente
        .iter()
        .filter(|a| !matches!(a.as_str(), "--paesse" | "--unit" | "--einheit"))
        .cloned()
        .collect();
    // **«ABI1»: `--with <lib.gabi>` zieht eine Schnittstelle HINZU.**
    //
    // Die Datei ist Gabbro-Quelltext; sie wird vor die zu pruefende Einheit gestellt, und
    // damit loesen die Namen auf. *`E009` und `K003` verschwinden dann, WEIL geprueft wird
    // -- nicht, weil geschwiegen wird.*
    let (dateien, mit) = match split_with(getippt, &argumente) {
        Ok(x) => x,
        Err(c) => return c,
    };
    let vorspann = match read_preamble(getippt, &mit) {
        Ok(v) => v,
        Err(c) => return c,
    };
    if einheit {
        return pruefe_als_einheit(getippt, &dateien, &vorspann, voll);
    }
    let mut fehler = 0usize;
    // See `command_emit`: the build spans the file list, not one file.
    let mut register = gabbro_check::bindung::Bindungsregister::neu();
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
        register.nimm_auf(datei, &baum, versatz, &mut absagen);
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
                eprintln!("gabbro {getippt}: the interface itself does not hold -- nothing checked");
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
            "{datei}: {} items, {f} errors, {h} hints",
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
    if voll {
        print!("{}", register_voll());
    } else {
        print!("{}", register_kurz());
    }
    if fehler == 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::from(1)
    }
}

/// **The full "not checked in this run" register** -- unchanged, what `pruefe` printed on
/// EVERY run until 2026-08-25. Since then it stands behind `--paesse`.
fn register_voll() -> String {
    use std::fmt::Write;
    let mut s = String::new();
    let _ = writeln!(s, "Not checked in this run:");
    for p in gabbro_check::ungeprueft() {
        let _ = match p.zustand {
            Zustand::Offen(w) => writeln!(s, "  {} {:<14} {w}", p.nummer, p.name),
            Zustand::Getragen(w) => {
                writeln!(s, "  {} {:<14} CARRIED -- the rest is NAMED: {w}", p.nummer, p.name)
            }
            Zustand::Teilgebaut(w) => {
                writeln!(s, "  {} {:<14} ONLY PARTIAL -- {w}", p.nummer, p.name)
            }
            Zustand::Gebaut => Ok(()),
        };
    }
    s
}

/// **The disclosure, in four lines instead of 1 122 words** (2026-08-25).
///
/// **Measured on `beispiele/16-by-ops-am-feld.gab`, a CLEAN file of 39 lines:** the whole run
/// printed **1 142 words**, and **1 122 of them (98.2 %) were this register.** The result --
/// the one line somebody ran the command for -- was twenty. *A disclosure that drowns the
/// finding by a factor of 56 is not read the twentieth time, and is therefore guaranteed to
/// have no effect.*
///
/// **And the decisive point is that this text can NEVER differ between two runs.**
/// `ungeprueft()` reads `passliste()`, a static list inside the binary -- it does not depend
/// on the file checked, on the result, or on the day. *Writing it out every time discloses
/// nothing that was not already disclosed the first time.*
///
/// > **The principle stays, the default turns around.** The number is still there, every
/// > state is counted, every pass is named, and the fingerprint makes a change of wording
/// > visible without printing it -- *two runs with different fingerprints have different
/// > registers, and that is exactly the question "did it change?" asks.* The full text
/// > stands behind `--paesse` and behind `gabbro paesse`, where it already stood.
fn register_kurz() -> String {
    use std::fmt::Write;
    let paesse = gabbro_check::ungeprueft();
    let mut offen = 0usize;
    let mut getragen = 0usize;
    let mut teil = 0usize;
    for p in &paesse {
        match p.zustand {
            Zustand::Offen(_) => offen += 1,
            Zustand::Getragen(_) => getragen += 1,
            Zustand::Teilgebaut(_) => teil += 1,
            Zustand::Gebaut => {}
        }
    }
    let namen: Vec<String> = paesse
        .iter()
        .map(|p| format!("{} {}", p.nummer, p.name))
        .collect();
    let mut s = String::new();
    let _ = writeln!(
        s,
        "Not checked in this run: {} passes -- {offen} open, {getragen} CARRIED (the rest is \
         NAMED), {teil} only partial",
        paesse.len()
    );
    let _ = writeln!(s, "  {}", namen.join(", "));
    let _ = writeln!(
        s,
        "  register {:08x} -- the FULL text with `gabbro pruefe --paesse` or `gabbro paesse`",
        abdruck(&register_voll())
    );
    let _ = writeln!(
        s,
        "  it is a property of this BINARY, not of the file just checked -- and it did not \
         shrink, it moved"
    );
    s
}

/// **FNV-1a, 32 bit, by hand** -- so that a change in the register's wording is visible
/// without the register being printed.
///
/// *By hand and not from a crate:* this fingerprint stands in output a human compares, not
/// in a promise that carries something. **Taking on a dependency for it would be trust
/// surface bought for convenience** -- and this folder counts its trust surface.
fn abdruck(text: &str) -> u32 {
    let mut h: u32 = 0x811c_9dc5;
    for b in text.as_bytes() {
        h ^= u32::from(*b);
        h = h.wrapping_mul(0x0100_0193);
    }
    h
}

/// **«A4», the measurement: does the computed hull agree with the written list?**
///
/// Reported in four parts, and **not as one quota** -- the third and fourth columns are the
/// interesting ones:
///
/// | | |
/// |---|---|
/// | **identical** | the line could have been computed |
/// | **narrower** | the declaration promises MORE than the body does -- blunt, not wrong |
/// | **broader** | the declaration promises TOO LITTLE -- **this column belongs empty**, `E005`/`E008`/`E010` stand in front of it |
/// | **incomplete** | the hull tears, and the edge is NAMED (R16) |
fn befehl_abi_vergleich(dateien: &[&String], weit: bool) -> std::process::ExitCode {
    use gabbro_check::abi::Urteil;
    let (mut ident, mut enger, mut breiter, mut unvoll) = (0usize, 0usize, 0usize, 0usize);
    // **And the same four numbers over the `impl fn` ONLY.** «A4» asks after them: a
    // `spec fn` carries no lowering, and a `prim`/`extern` has no body to compute over.
    // *The population belongs next to the quota.*
    let mut i4 = [0usize; 4];
    let mut breiter_welt = 0usize;
    let mut gruende: std::collections::BTreeMap<String, usize> = Default::default();
    let mut zeilen: Vec<String> = Vec::new();
    let mut dateien_gelesen = 0usize;
    let mut dateien_abgewiesen: Vec<String> = Vec::new();
    // **The tally per ENTRY -- the population the target mark counts.** Six numbers, and
    // they do not add up to one quota on purpose: `zu_eng` is a count of DERIVED effects
    // that no line covers, and those are not among the written entries.
    let mut e_tragend = 0usize;
    let mut e_zu_weit = 0usize;
    let mut e_zu_eng = 0usize;
    let mut e_rein = 0usize;
    let mut e_rein_falsch = 0usize;
    let mut e_ausserhalb = 0usize;
    let mut e_ungemessen = 0usize;
    let mut b_mit = 0usize;
    let mut b_ohne = 0usize;
    let mut b_fn_mit = 0usize;
    let mut b_fn_ohne = 0usize;
    let mut weit_zeilen: Vec<String> = Vec::new();
    for datei in dateien {
        let Ok(quelle) = std::fs::read_to_string(datei.as_str()) else {
            eprintln!("gabbro: {datei} not readable");
            return std::process::ExitCode::from(2);
        };
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        // **A unit with errors does NOT count, and it is NAMED.** Over a tree the passes
        // rejected, the comparison measures a list nobody has to keep. *A silently skipped
        // file is a number without its population.*
        if absagen.fehler_zahl() > 0 {
            dateien_abgewiesen.push((*datei).clone());
            continue;
        }
        dateien_gelesen += 1;
        let b = gabbro_check::abi::bestand(&baum);
        b_mit += b.mit_rumpf;
        b_ohne += b.ohne_rumpf;
        b_fn_mit += b.fn_mit_rumpf;
        b_fn_ohne += b.fn_ohne_rumpf;
        for v in gabbro_check::abi::vergleiche_mit(&baum, weit) {
            let e = gabbro_check::abi::eintraege(&v);
            e_tragend += e.tragend.len();
            e_zu_weit += e.zu_weit.len();
            e_zu_eng += e.zu_eng.len();
            e_rein += e.rein_stimmt.len();
            e_rein_falsch += e.rein_falsch.len();
            e_ausserhalb += e.ausserhalb.len();
            e_ungemessen += e.ungemessen.len();
            for w in &e.zu_weit {
                weit_zeilen.push(format!("  too wide   {}::{}   {w}", v.modul, v.name));
            }
            let ort = format!("{}::{}", v.modul, v.name);
            let ist_impl = v.klasse == Some(gabbro_syntax::ast::FnKlasse::Impl);
            let mut buche = |i: usize| { if ist_impl { i4[i] += 1; } };
            match &v.urteil {
                Urteil::Identisch => {
                    ident += 1;
                    buche(0);
                    zeilen.push(format!("  identical      {ort}"));
                }
                Urteil::Enger(w) => {
                    enger += 1;
                    buche(1);
                    zeilen.push(format!("  narrower       {ort}   unwarranted: {}", w.join(", ")));
                }
                Urteil::Breiter(w, bekannt) => {
                    breiter += 1;
                    buche(2);
                    if *bekannt {
                        breiter_welt += 1;
                    }
                    zeilen.push(format!(
                        "  BROADER        {ort}   undeclared: {}{}",
                        w.join(", "),
                        if *bekannt { "   [known world name -- a REAL frame breach]" }
                        else { "   [no known world name -- E008/E010 stay silent, with reason]" }
                    ));
                }
                Urteil::Unvollstaendig(g) => {
                    unvoll += 1;
                    buche(3);
                    let kurz = g.split(" -- ").next().unwrap_or(g).to_string();
                    *gruende.entry(kurz).or_default() += 1;
                    zeilen.push(format!("  incomplete     {ort}   {g}"));
                }
                Urteil::Nichts => {}
            }
        }
    }
    let n = ident + enger + breiter + unvoll;
    println!("== «A4»: the COMPUTED effect hull against the WRITTEN one ==");
    println!("   reads through parameters and undeclared names: {}",
             if weit { "COUNTED IN (`--weit`)" } else { "left out, as in `E010`" });
    for z in &zeilen {
        println!("{z}");
    }
    println!();
    println!("  units read  {dateien_gelesen}");
    if !dateien_abgewiesen.is_empty() {
        println!("  units REJECTED (errors -- not counted)  {}:", dateien_abgewiesen.len());
        for d in &dateien_abgewiesen {
            println!("      {d}");
        }
    }
    println!("  functions with `effects` and a body  {n}");
    if n == 0 {
        println!();
        println!("  NO FUNCTION LOOKED AT -- this number is no measurement (W1/R16).");
        return std::process::ExitCode::from(1);
    }
    let q = |x: usize| 100.0 * x as f64 / n as f64;
    println!("  ---------------------------------------------");
    println!("  identical          {ident:>4}   {:>5.1} %", q(ident));
    println!("  computed NARROWER  {enger:>4}   {:>5.1} %", q(enger));
    println!("  computed BROADER   {breiter:>4}   {:>5.1} %", q(breiter));
    println!("      of those a known world name  {breiter_welt:>4}   <- ONLY THESE are a frame breach");
    println!("      of those a place undeclared  {:>4}   <- `E008`/`E010` stay silent here, with reason",
             breiter - breiter_welt);
    println!("  incomplete         {unvoll:>4}   {:>5.1} %", q(unvoll));
    if !gruende.is_empty() {
        println!();
        println!("  where the hull tears:");
        let mut g: Vec<_> = gruende.iter().collect();
        g.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
        for (grund, k) in g {
            println!("    {k:>3}x  {grund}");
        }
    }
    let ni: usize = i4.iter().sum();
    println!();
    println!("  of those `impl fn` -- the population «A4» asks after:  {ni}");
    if ni > 0 {
        let qi = |x: usize| 100.0 * x as f64 / ni as f64;
        println!("  ---------------------------------------------");
        println!("  identical          {:>4}   {:>5.1} %", i4[0], qi(i4[0]));
        println!("  computed NARROWER  {:>4}   {:>5.1} %", i4[1], qi(i4[1]));
        println!("  computed BROADER   {:>4}   {:>5.1} %", i4[2], qi(i4[2]));
        println!("  incomplete         {:>4}   {:>5.1} %", i4[3], qi(i4[3]));
    }
    println!();
    println!("  **BROADER belongs empty.** `E005`, `E008` and `E010` demand that every");
    println!("  performed effect stand in the list -- should this column move off zero, the");
    println!("  finding is not one about the elaborator but one about those three.");
    println!();
    println!("== PER ENTRY -- the population the target mark counts ==");
    for z in &weit_zeilen {
        println!("{z}");
    }
    if !weit_zeilen.is_empty() {
        println!();
    }
    println!("  `effects` entries in the whole corpus       {:>4}", b_mit + b_ohne);
    println!("      on a function WITH a body               {b_mit:>4}   ({b_fn_mit} functions)");
    println!("      on `extern`/`prim` -- NO body           {b_ohne:>4}   ({b_fn_ohne} functions)");
    println!("        ^ these can never go to zero: no body, nothing to derive from.");
    println!("          An `extern fn` effect line is the TRUST SURFACE, not bookkeeping.");
    println!();
    let messbar =
        e_tragend + e_zu_weit + e_rein + e_rein_falsch + e_ausserhalb + e_ungemessen;
    println!("  entries the comparison could look at        {messbar:>4}");
    println!("  ---------------------------------------------");
    println!("  RIGHT   -- covers a derived effect          {e_tragend:>4}");
    println!("  RIGHT   -- `pure`, derived set empty        {e_rein:>4}");
    println!("  TOO WIDE-- covers nothing derived           {e_zu_weit:>4}");
    println!("  TOO NARROW -- `pure` contradicted           {e_rein_falsch:>4}");
    println!("  outside -- `diverges`, not a place          {e_ausserhalb:>4}");
    println!("  UNMEASURED -- the hull tears (R16)          {e_ungemessen:>4}");
    if messbar != b_mit {
        println!("  !! the columns do not add up to {b_mit} -- the partition is broken");
    }
    println!();
    println!("  TOO NARROW -- derived, covered by no line   {e_zu_eng:>4}");
    println!("     ^ counted on the DERIVED side. These are holes, and a hole is not one of");
    println!("       the written entries -- adding it into the quota above would divide by a");
    println!("       population that does not contain it.");
    std::process::ExitCode::SUCCESS
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

/// **`gabbro effects` -- what the compiler would WRITE, and where each entry comes from.**
///
/// Four shapes, and the flags stay German like `abi`'s (`ERSTNAMEN.md`: the sub-command's
/// first name is English, the flags of this family are not):
///
/// | | |
/// |---|---|
/// | *(nothing)* | one derived `effects` line per function |
/// | `--ursprung` | each entry with its origin path, hop by hop |
/// | `--vergleich` | the derived set held against the WRITTEN one, per entry |
/// | `--eng` | leave out reads through parameters, exactly as `E010` does |
///
/// **`--eng` is an opt-OUT here and `--weit` an opt-IN at `abi`, and that is not an
/// inconsistency but the difference between the two questions.** `abi --vergleich` asks
/// *"does the written line agree with what the passes check?"* -- and the passes leave
/// parameter reads out, with a reason. This command asks *"what would an elaborator have to
/// write?"*, and it has to write `reads p.slots`: the caller wants to know what happens to
/// his pointer. *A default that answered the other question would make every measurement
/// taken with it wrong in the same direction.*
fn befehl_wirkungen(rest: &[String]) -> std::process::ExitCode {
    let ursprung = rest.iter().any(|a| a == "--ursprung");
    let vergleich = rest.iter().any(|a| a == "--vergleich");
    let weit = !rest.iter().any(|a| a == "--eng");
    let nur: Option<&String> = rest
        .iter()
        .position(|a| a == "--fn")
        .and_then(|i| rest.get(i + 1));
    let dateien: Vec<&String> = rest
        .iter()
        .enumerate()
        .filter(|(i, a)| {
            !a.starts_with("--") && Some(*i) != rest.iter().position(|x| x == "--fn").map(|p| p + 1)
        })
        .map(|(_, a)| a)
        .collect();
    if dateien.is_empty() {
        eprintln!("gabbro effects: no file named");
        return std::process::ExitCode::from(2);
    }
    if vergleich {
        return wirkungen_vergleich(&dateien, weit);
    }
    let mut gefunden = 0usize;
    let mut runden_max = 0usize;
    let mut verbreitert = 0usize;
    for datei in &dateien {
        let Ok(quelle) = std::fs::read_to_string(datei.as_str()) else {
            eprintln!("gabbro: {datei} not readable");
            return std::process::ExitCode::from(2);
        };
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        // **A unit with errors is not silently skipped, and it is not silently used
        // either.** The derivation runs over a tree the passes rejected -- the set it
        // produces is a statement about a program that does not compile.
        if absagen.fehler_zahl() > 0 {
            eprintln!("gabbro effects: {datei} has errors -- the derivation would speak about a program that does not compile");
            return std::process::ExitCode::from(1);
        }
        let ab = gabbro_check::ableitung::leite_ab(&baum, weit);
        runden_max = runden_max.max(ab.runden);
        verbreitert += ab.verbreitert;
        if ab.abgebrochen {
            eprintln!("gabbro effects: {datei}: the fixpoint did not settle -- every set below is a LOWER BOUND");
        }
        if dateien.len() > 1 && nur.is_none() {
            println!("== {datei} ==");
        }
        for (name, a) in &ab.je {
            if let Some(n) = nur {
                if name != n && !name.ends_with(&format!("::{n}")) {
                    continue;
                }
            }
            gefunden += 1;
            println!("{name}");
            println!("    {}", gabbro_check::ableitung::zeile(a));
            if let Some(g) = &a.unvollstaendig {
                println!("    -- LOWER BOUND (R16): {g}");
            }
            if ursprung {
                for w in &a.wirkungen {
                    println!("    {w}");
                    for (wo, was, weg) in ab.pfad(name, w) {
                        println!(
                            "        {wo}  `{was}`  --  {}",
                            gabbro_check::ableitung::weg_text(&weg)
                        );
                    }
                }
            }
        }
    }
    if let Some(n) = nur {
        if gefunden == 0 {
            eprintln!("gabbro effects: no function named `{n}` in the files given");
            return std::process::ExitCode::from(1);
        }
    }
    println!();
    println!("  fixpoint: at most {runden_max} rounds, widening fired {verbreitert}x");
    println!("  reads through parameters: {}",
             if weit { "counted in (an elaborator has to write them)" } else { "left out (`--eng`, as in `E010`)" });
    std::process::ExitCode::SUCCESS
}

/// The entry tally over the DERIVATION -- the same six columns as `abi --vergleich`, over a
/// basis that cannot inherit a callee's over-declaration.
fn wirkungen_vergleich(dateien: &[&String], weit: bool) -> std::process::ExitCode {
    let mut e_tragend = 0usize;
    let mut e_zu_weit = 0usize;
    let mut e_zu_eng = 0usize;
    let mut e_rein = 0usize;
    let mut e_rein_falsch = 0usize;
    let mut e_ausserhalb = 0usize;
    let mut e_ungemessen = 0usize;
    let mut b_mit = 0usize;
    let mut b_ohne = 0usize;
    let mut b_fn_mit = 0usize;
    let mut b_fn_ohne = 0usize;
    let mut gelesen = 0usize;
    let mut abgewiesen: Vec<String> = Vec::new();
    let mut weit_zeilen: Vec<String> = Vec::new();
    let mut runden_max = 0usize;
    let mut verbreitert = 0usize;
    for datei in dateien {
        let Ok(quelle) = std::fs::read_to_string(datei.as_str()) else {
            eprintln!("gabbro: {datei} not readable");
            return std::process::ExitCode::from(2);
        };
        let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        if absagen.fehler_zahl() > 0 {
            abgewiesen.push((*datei).clone());
            continue;
        }
        gelesen += 1;
        let ab = gabbro_check::ableitung::leite_ab(&baum, weit);
        runden_max = runden_max.max(ab.runden);
        verbreitert += ab.verbreitert;
        let b = gabbro_check::abi::bestand(&baum);
        b_mit += b.mit_rumpf;
        b_ohne += b.ohne_rumpf;
        b_fn_mit += b.fn_mit_rumpf;
        b_fn_ohne += b.fn_ohne_rumpf;
        for v in gabbro_check::abi::vergleiche_abgeleitet(&baum, weit) {
            let e = gabbro_check::abi::eintraege(&v);
            e_tragend += e.tragend.len();
            e_zu_weit += e.zu_weit.len();
            e_zu_eng += e.zu_eng.len();
            e_rein += e.rein_stimmt.len();
            e_rein_falsch += e.rein_falsch.len();
            e_ausserhalb += e.ausserhalb.len();
            e_ungemessen += e.ungemessen.len();
            for w in &e.zu_weit {
                weit_zeilen.push(format!("  too wide   {}::{}   {w}", v.modul, v.name));
            }
        }
    }
    println!("== «T1»: the DERIVED effect set against the WRITTEN one, PER ENTRY ==");
    println!("   basis: the fixpoint over the BODIES (`ableitung.rs`), not the hull over the");
    println!("   declarations -- a callee's over-declaration cannot leak into a caller here.");
    println!();
    for z in &weit_zeilen {
        println!("{z}");
    }
    println!();
    println!("  units read  {gelesen}");
    if !abgewiesen.is_empty() {
        println!("  units REJECTED (errors -- not counted)  {}:", abgewiesen.len());
        for d in &abgewiesen {
            println!("      {d}");
        }
    }
    println!("  `effects` entries in those units            {:>4}", b_mit + b_ohne);
    println!("      on a function WITH a body               {b_mit:>4}   ({b_fn_mit} functions)");
    println!("      on `extern`/`prim` -- NO body           {b_ohne:>4}   ({b_fn_ohne} functions)");
    println!("        ^ TRUST SURFACE. No body, nothing to derive from -- these can never go");
    println!("          to zero, and counting them into the mark would promise a saving that");
    println!("          no build can deliver.");
    println!();
    let messbar =
        e_tragend + e_zu_weit + e_rein + e_rein_falsch + e_ausserhalb + e_ungemessen;
    println!("  entries the comparison could look at        {messbar:>4}");
    println!("  ---------------------------------------------");
    println!("  RIGHT   -- covers a derived effect          {e_tragend:>4}");
    println!("  RIGHT   -- `pure`, derived set empty        {e_rein:>4}");
    println!("  TOO WIDE-- covers nothing derived           {e_zu_weit:>4}");
    println!("  TOO NARROW -- `pure` contradicted           {e_rein_falsch:>4}");
    println!("  outside -- `diverges`, not a place          {e_ausserhalb:>4}");
    println!("  UNMEASURED -- lower bound (R16)             {e_ungemessen:>4}");
    if messbar != b_mit {
        println!("  !! the columns do not add up to {b_mit} -- the partition is broken");
    }
    println!();
    println!("  TOO NARROW -- derived, covered by no line   {e_zu_eng:>4}");
    println!("     ^ counted on the DERIVED side; a hole is not one of the written entries.");
    println!();
    println!("  fixpoint: at most {runden_max} rounds, widening fired {verbreitert}x");
    std::process::ExitCode::SUCCESS
}
