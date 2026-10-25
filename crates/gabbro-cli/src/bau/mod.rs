//! **The build system, after Meson: a project file, a build directory per configuration, and
//! the LLVM tool chain.** `dokumente/BUILD-SYSTEM.md` is the long form.
//!
//! ```text
//!   gabbro setup build                 -- configure `build/` from `./gabbro.build`
//!   gabbro setup build-arm . -Dtarget=aarch64
//!   gabbro compile -C build            -- build every target (or the ones named)
//!   gabbro test -C build               -- build, then run the declared tests
//!   gabbro install -C build            -- build, then copy `install: true` programs
//!   gabbro configure -C build -Dbuildtype=testbuild
//!   gabbro introspect -C build         -- the evaluated project as JSON
//!   gabbro build                       -- `setup build` if needed, then `compile -C build`
//! ```
//!
//! **A build directory is ONE configuration**: its options (target, build type, the project's
//! own) are fixed at `setup` and changed only by `configure`; two configurations are two
//! directories. The project file is evaluated again at every run, so an edit to a build file
//! needs no reconfigure step.
//!
//! **Every edge between targets is COMPUTED, never written** (W7): a library's files go into
//! a unit because the unit's `use` lines reach the library's modules, not because a list says
//! so. Separate compilation across units is not implemented in the LLVM backend (the generator
//! defines every item a `.gabi` preamble declares), so a library is a SOURCE library: its files
//! are translated inside each unit that uses it, and alone once to be checked alone. A program
//! or object whose modules another unit uses is refused by name -- make it a library.

mod einheit;
pub mod sprache;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use sprache::{Art, Option_, Projekt, Wert};

const ZUSTAND: &str = "gabbro-setup.txt";
const BAUDATEI: &str = "gabbro.build";
const OPTIONSDATEI: &str = "gabbro.options";
const VORGABE_VERZEICHNIS: &str = "build";

// ---------------------------------------------------------------- arguments

struct Argumente {
    verzeichnis: Option<String>,
    setzen: Vec<(String, String)>,
    frei: Vec<String>,
    trocken: bool,
}

fn lies_argumente(befehl: &str, rest: &[String]) -> Result<Argumente, String> {
    let mut a = Argumente { verzeichnis: None, setzen: Vec::new(), frei: Vec::new(), trocken: false };
    let mut i = 0;
    while i < rest.len() {
        let x = &rest[i];
        if x == "-C" {
            let Some(d) = rest.get(i + 1) else {
                return Err(format!("gabbro {befehl}: `-C` takes the build directory"));
            };
            a.verzeichnis = Some(d.clone());
            i += 2;
            continue;
        }
        if let Some(d) = x.strip_prefix("-C") {
            a.verzeichnis = Some(d.to_string());
        } else if let Some(kv) = x.strip_prefix("-D") {
            let Some((k, v)) = kv.split_once('=') else {
                return Err(format!("gabbro {befehl}: `{x}` -- an option is set as `-D<name>=<value>`"));
            };
            a.setzen.push((k.to_string(), v.to_string()));
        } else if x == "--dry-run" || x == "--trocken" {
            a.trocken = true;
        } else if x.starts_with('-') {
            return Err(format!("gabbro {befehl}: `{x}` is no flag of this command"));
        } else {
            a.frei.push(x.clone());
        }
        i += 1;
    }
    Ok(a)
}

// ---------------------------------------------------------------- the build directory

/// What `setup` fixed: the build file and the options set by `-D`.
struct Zustand {
    baudatei: PathBuf,
    gesetzt: BTreeMap<String, String>,
}

fn lies_zustand(verzeichnis: &Path) -> Result<Zustand, String> {
    let pfad = verzeichnis.join(ZUSTAND);
    let text = std::fs::read_to_string(&pfad).map_err(|_| {
        format!(
            "`{}` is no build directory (no `{ZUSTAND}`) -- `gabbro setup {}` makes one",
            verzeichnis.display(),
            verzeichnis.display()
        )
    })?;
    let mut baudatei = None;
    let mut gesetzt = BTreeMap::new();
    for (nr, z) in text.lines().enumerate() {
        let z = z.trim();
        if z.is_empty() || z.starts_with('#') {
            continue;
        }
        if let Some(q) = z.strip_prefix("source ") {
            baudatei = Some(PathBuf::from(q));
        } else if let Some(o) = z.strip_prefix("option ") {
            let Some((k, v)) = o.split_once(' ') else {
                return Err(format!("{}:{}: `option <name> <value>`", pfad.display(), nr + 1));
            };
            gesetzt.insert(k.to_string(), v.to_string());
        } else {
            return Err(format!(
                "{}:{}: `{z}` -- this file is written by `gabbro setup`/`configure`, not by hand",
                pfad.display(),
                nr + 1
            ));
        }
    }
    let Some(baudatei) = baudatei else {
        return Err(format!("{}: no `source` line", pfad.display()));
    };
    Ok(Zustand { baudatei, gesetzt })
}

fn schreibe_zustand(verzeichnis: &Path, z: &Zustand) -> Result<(), String> {
    let mut text = String::from(
        "# The configuration of this build directory, written by `gabbro setup`.\n\
         # Change it with `gabbro configure -C <dir> -D<name>=<value>`, not by hand.\n",
    );
    text.push_str(&format!("source {}\n", z.baudatei.display()));
    for (k, v) in &z.gesetzt {
        text.push_str(&format!("option {k} {v}\n"));
    }
    std::fs::create_dir_all(verzeichnis).map_err(|e| format!("{}: {e}", verzeichnis.display()))?;
    // As Meson does: a build directory says itself that nothing in it belongs to a repository,
    // whatever its name and wherever it stands.
    let ignorieren = verzeichnis.join(".gitignore");
    std::fs::write(&ignorieren, "# written by `gabbro setup`: a build directory is no source\n*\n")
        .map_err(|e| format!("{}: {e}", ignorieren.display()))?;
    let pfad = verzeichnis.join(ZUSTAND);
    std::fs::write(&pfad, text).map_err(|e| format!("{}: {e}", pfad.display()))
}

/// The options of the project with the `-D` values laid over the defaults.
fn optionen(
    baudatei: &Path,
    gesetzt: &BTreeMap<String, String>,
) -> Result<(Vec<Option_>, BTreeMap<String, Wert>), String> {
    let wurzel = baudatei.parent().unwrap_or(Path::new("."));
    let alle = sprache::lies_optionen(&wurzel.join(OPTIONSDATEI))?;
    let mut werte = BTreeMap::new();
    for o in &alle {
        werte.insert(o.name.clone(), o.vorgabe.clone());
    }
    for (k, v) in gesetzt {
        let Some(o) = alle.iter().find(|o| &o.name == k) else {
            return Err(format!(
                "`-D{k}={v}`: `{k}` is no option of this project (built-in: target, buildtype, \
                 prefix, bindir; the project's own stand in `{OPTIONSDATEI}`)"
            ));
        };
        werte.insert(k.clone(), sprache::lies_optionswert(o, v)?);
    }
    Ok((alle, werte))
}

/// The build file a `setup` argument names: a directory holding `gabbro.build`, or a file.
fn finde_baudatei(quelle: &str) -> Result<PathBuf, String> {
    let p = PathBuf::from(quelle);
    let datei = if p.is_dir() { p.join(BAUDATEI) } else { p };
    if !datei.is_file() {
        return Err(format!("`{}` holds no build file", datei.display()));
    }
    std::fs::canonicalize(&datei).map_err(|e| format!("{}: {e}", datei.display()))
}

/// Everything one run needs: the state, the options, the evaluated project.
struct Geladen {
    verzeichnis: PathBuf,
    alle: Vec<Option_>,
    werte: BTreeMap<String, Wert>,
    projekt: Projekt,
}

fn lade(verzeichnis: &Path) -> Result<Geladen, String> {
    let z = lies_zustand(verzeichnis)?;
    let (alle, werte) = optionen(&z.baudatei, &z.gesetzt)?;
    let projekt = sprache::werte_aus(&z.baudatei, &werte)?;
    for m in &projekt.meldungen {
        println!("{m}");
    }
    Ok(Geladen { verzeichnis: verzeichnis.to_path_buf(), alle, werte, projekt })
}

fn text_option(werte: &BTreeMap<String, Wert>, name: &str) -> String {
    match werte.get(name) {
        Some(Wert::Text(t)) => t.clone(),
        _ => String::new(),
    }
}

// ---------------------------------------------------------------- the plan

/// One unit to build: the target, and every file the translation sees.
struct Einheit {
    ziel: usize,
    quellen: Vec<(String, String)>,
    bibliotheken: Vec<usize>,
}

/// Computes the units: reads every source once, maps modules to targets, follows `use` edges
/// to libraries. **A refusal here names the targets it is about.**
fn plane(p: &Projekt) -> Result<Vec<Einheit>, String> {
    let mut texte: BTreeMap<String, String> = BTreeMap::new();
    let mut karten: Vec<(BTreeSet<String>, BTreeSet<String>)> = Vec::new();
    for z in &p.ziele {
        let mut quellen = Vec::new();
        for d in &z.dateien {
            let t = match texte.get(d) {
                Some(t) => t.clone(),
                None => {
                    let t = std::fs::read_to_string(p.wurzel.join(d)).map_err(|e| {
                        format!("{}: `{d}` (target `{}`): {e}", z.ort, z.name)
                    })?;
                    texte.insert(d.clone(), t.clone());
                    t
                }
            };
            quellen.push((d.clone(), t));
        }
        karten.push(einheit::modulkarte(&quellen));
    }
    // Which target declares which module. A library's module must be unique among libraries;
    // a program's or object's module only within the units it ends up in.
    let mut modul_bib: BTreeMap<String, usize> = BTreeMap::new();
    let mut modul_sonst: BTreeMap<String, usize> = BTreeMap::new();
    for (i, z) in p.ziele.iter().enumerate() {
        for m in &karten[i].0 {
            if z.art == Art::Bibliothek {
                if let Some(j) = modul_bib.insert(m.clone(), i) {
                    return Err(format!(
                        "module `{m}` is declared in library `{}` AND in library `{}` -- a `use` \
                         edge onto it would have two targets",
                        p.ziele[j].name, z.name
                    ));
                }
            } else {
                modul_sonst.entry(m.clone()).or_insert(i);
            }
        }
    }
    let mut einheiten = Vec::new();
    for (i, z) in p.ziele.iter().enumerate() {
        // The libraries this target rests on, transitively, deepest first.
        let mut bibs: Vec<usize> = Vec::new();
        let mut offen: Vec<usize> = vec![i];
        let mut gesehen: BTreeSet<usize> = BTreeSet::from([i]);
        while let Some(k) = offen.pop() {
            for m in &karten[k].1 {
                if karten[k].0.contains(m) {
                    continue;
                }
                if let Some(&b) = modul_bib.get(m) {
                    if gesehen.insert(b) {
                        bibs.push(b);
                        offen.push(b);
                    }
                } else if let Some(&o) = modul_sonst.get(m) {
                    if o != i && !karten[i].0.contains(m) {
                        return Err(format!(
                            "{}: target `{}` uses module `{m}` of {} `{}` -- only a library's \
                             modules reach another target; make `{}` a `library` (separate \
                             compilation across units is not implemented in the LLVM backend)",
                            z.ort,
                            z.name,
                            p.ziele[o].art.wort(),
                            p.ziele[o].name,
                            p.ziele[o].name
                        ));
                    }
                }
            }
        }
        bibs.reverse();
        let mut quellen: Vec<(String, String)> = Vec::new();
        let mut module: BTreeMap<String, usize> = BTreeMap::new();
        for &k in bibs.iter().chain(std::iter::once(&i)) {
            for m in &karten[k].0 {
                if let Some(j) = module.insert(m.clone(), k) {
                    if j != k {
                        return Err(format!(
                            "{}: module `{m}` is declared in `{}` AND in `{}`, and both end up in \
                             the unit of `{}`",
                            z.ort, p.ziele[j].name, p.ziele[k].name, z.name
                        ));
                    }
                }
            }
            for d in &p.ziele[k].dateien {
                if !quellen.iter().any(|(q, _)| q == d) {
                    quellen.push((d.clone(), texte[d].clone()));
                }
            }
        }
        einheiten.push(Einheit { ziel: i, quellen, bibliotheken: bibs });
    }
    Ok(einheiten)
}

/// The coverage line: "nothing found" and "nothing looked at" look the same otherwise.
fn deckungszeile(p: &Projekt, gebaut: usize, aktuell: usize, abgesagt: usize) {
    let genannt: BTreeSet<&String> = p.ziele.iter().flat_map(|z| z.dateien.iter()).collect();
    println!(
        "built {gebaut} target(s), {aktuell} up to date, {abgesagt} refused -- {} file(s) named \
         by this project",
        genannt.len()
    );
    let alle = zaehle_gab(&p.wurzel);
    let ungesehen = alle.saturating_sub(genannt.len());
    println!(
        "NOT looked at: {ungesehen} `.gab` file(s) below the project root stand in no target \
         ({alle} below the root)"
    );
}

fn zaehle_gab(wurzel: &Path) -> usize {
    let mut n = 0;
    let Ok(eintraege) = std::fs::read_dir(wurzel) else {
        return 0;
    };
    for e in eintraege.flatten() {
        let p = e.path();
        let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if name.starts_with('.') || name == "target" || p.join(ZUSTAND).exists() {
            continue;
        }
        if p.is_dir() {
            n += zaehle_gab(&p);
        } else if p.extension().and_then(|s| s.to_str()) == Some("gab") {
            n += 1;
        }
    }
    n
}

// ---------------------------------------------------------------- compile

/// Builds the targets named in `auswahl` (all if empty). `Ok(true)` when nothing was refused.
fn kompiliere(g: &Geladen, auswahl: &[String], trocken: bool) -> Result<bool, String> {
    let p = &g.projekt;
    for n in auswahl {
        if !p.ziele.iter().any(|z| &z.name == n) {
            return Err(format!("`{n}` is no target of project `{}`", p.name));
        }
    }
    let ziel_name = text_option(&g.werte, "target");
    let Some(ziel) = gabbro_check::llvm::ziel_fuer(&ziel_name) else {
        return Err(format!("unknown target `{ziel_name}`"));
    };
    let bau = if text_option(&g.werte, "buildtype") == "testbuild" {
        gabbro_check::gatter::Bau::Pruefbau
    } else {
        gabbro_check::gatter::Bau::Auslieferung
    };
    let einheiten = plane(p)?;
    // Libraries first: a refusal inside one names the library before its users fall with it.
    let mut reihe: Vec<&Einheit> = einheiten
        .iter()
        .filter(|e| auswahl.is_empty() || auswahl.contains(&p.ziele[e.ziel].name))
        .collect();
    reihe.sort_by_key(|e| (p.ziele[e.ziel].art != Art::Bibliothek, e.ziel));

    if trocken {
        println!("project  {} {}", p.name, p.version);
        println!("  build directory {}", g.verzeichnis.display());
        println!("  target   {}", ziel.triple);
        for e in &reihe {
            let z = &p.ziele[e.ziel];
            let bibs: Vec<&str> = e.bibliotheken.iter().map(|b| p.ziele[*b].name.as_str()).collect();
            println!(
                "  {} {} ({} file(s){})",
                z.art.wort(),
                z.name,
                e.quellen.len(),
                if bibs.is_empty() { String::new() } else { format!(", computed: {}", bibs.join(", ")) }
            );
        }
        deckungszeile(p, 0, 0, 0);
        return Ok(true);
    }
    std::fs::create_dir_all(&g.verzeichnis).map_err(|e| format!("{}: {e}", g.verzeichnis.display()))?;
    let (mut gebaut, mut aktuell, mut abgesagt) = (0usize, 0usize, 0usize);
    for e in reihe {
        let z = &p.ziele[e.ziel];
        match einheit::baue(&g.verzeichnis, &z.name, z.art, &e.quellen, bau, ziel) {
            einheit::Ergebnis::Gebaut => {
                gebaut += 1;
                println!("built    {}", z.name);
            }
            einheit::Ergebnis::Aktuell => {
                aktuell += 1;
                println!("current  {}  -- content unchanged, artefact present", z.name);
            }
            einheit::Ergebnis::Abgesagt(grund) => {
                abgesagt += 1;
                println!("REFUSED  {}: {grund}", z.name);
            }
        }
    }
    deckungszeile(p, gebaut, aktuell, abgesagt);
    Ok(abgesagt == 0)
}

fn verzeichnis_von(a: &Argumente) -> PathBuf {
    PathBuf::from(a.verzeichnis.clone().unwrap_or_else(|| VORGABE_VERZEICHNIS.to_string()))
}

fn melde(befehl: &str, r: Result<bool, String>) -> ExitCode {
    match r {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("gabbro {befehl}: {e}");
            ExitCode::from(2)
        }
    }
}

// ---------------------------------------------------------------- commands

/// `gabbro setup <builddir> [<sourcedir|build file>] [-D<name>=<value>]…`
pub fn setup(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("setup", rest)?;
        let (verzeichnis, quelle) = match a.frei.as_slice() {
            [v] => (PathBuf::from(v), ".".to_string()),
            [v, q] => (PathBuf::from(v), q.clone()),
            _ => return Err("`gabbro setup <builddir> [<sourcedir|build file>] [-D<name>=<value>]…`".into()),
        };
        if verzeichnis.join(ZUSTAND).exists() {
            return Err(format!(
                "`{}` is already a build directory -- change it with `gabbro configure -C {}`",
                verzeichnis.display(),
                verzeichnis.display()
            ));
        }
        let baudatei = finde_baudatei(&quelle)?;
        let gesetzt: BTreeMap<String, String> = a.setzen.into_iter().collect();
        let (_, werte) = optionen(&baudatei, &gesetzt)?;
        let projekt = sprache::werte_aus(&baudatei, &werte)?;
        for m in &projekt.meldungen {
            println!("{m}");
        }
        plane(&projekt)?;
        schreibe_zustand(&verzeichnis, &Zustand { baudatei: baudatei.clone(), gesetzt })?;
        println!("project  {} {}", projekt.name, projekt.version);
        println!("  source   {}", baudatei.display());
        println!("  build    {}", verzeichnis.display());
        println!(
            "  target   {}, buildtype {}",
            text_option(&werte, "target"),
            text_option(&werte, "buildtype")
        );
        println!("  {} target(s), {} test(s)", projekt.ziele.len(), projekt.tests.len());
        println!("configured -- now `gabbro compile -C {}`", verzeichnis.display());
        Ok(true)
    })();
    melde("setup", r)
}

/// `gabbro configure [-C <builddir>] [-D<name>=<value>]…` -- prints the options, or changes them.
pub fn configure(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("configure", rest)?;
        if !a.frei.is_empty() {
            return Err(format!("`{}` -- configure takes `-C <builddir>` and `-D` settings", a.frei[0]));
        }
        let v = verzeichnis_von(&a);
        let mut z = lies_zustand(&v)?;
        if !a.setzen.is_empty() {
            for (k, w) in a.setzen {
                z.gesetzt.insert(k, w);
            }
            // Validate before writing: a refused value never reaches the directory.
            let (_, werte) = optionen(&z.baudatei, &z.gesetzt)?;
            sprache::werte_aus(&z.baudatei, &werte)?;
            schreibe_zustand(&v, &z)?;
            println!("configured {}", v.display());
        }
        let (alle, werte) = optionen(&z.baudatei, &z.gesetzt)?;
        let zeilen: Vec<[String; 4]> = alle
            .iter()
            .map(|o| {
                let wo = if z.gesetzt.contains_key(&o.name) {
                    "-D"
                } else if o.eingebaut {
                    "built-in"
                } else {
                    "default"
                };
                let mut text = sprache::zeige_wert(&werte[&o.name]);
                if let sprache::OptionsArt::Auswahl(c) = &o.art {
                    text = format!("{text} [{}]", c.join("|"));
                }
                [o.name.clone(), text, wo.to_string(), o.beschreibung.clone()]
            })
            .collect();
        let breite = |i: usize, kopf: &str| {
            zeilen.iter().map(|z| z[i].len()).chain(std::iter::once(kopf.len())).max().unwrap_or(0)
        };
        let (b0, b1, b2) = (breite(0, "option"), breite(1, "value"), breite(2, "set by"));
        println!("{:<b0$}  {:<b1$}  {:<b2$}  description", "option", "value", "set by");
        for z in &zeilen {
            println!("{:<b0$}  {:<b1$}  {:<b2$}  {}", z[0], z[1], z[2], z[3]);
        }
        Ok(true)
    })();
    melde("configure", r)
}

/// `gabbro compile [-C <builddir>] [--dry-run] [<target>…]`
pub fn compile(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("compile", rest)?;
        let g = lade(&verzeichnis_von(&a))?;
        kompiliere(&g, &a.frei, a.trocken)
    })();
    melde("compile", r)
}

/// `gabbro build|bau [<sourcedir|build file>] [-D…] [--dry-run]`: `setup` of `build/` BESIDE THE
/// PROJECT FILE when it is no build directory yet, `configure` when `-D` is given, then
/// `compile` -- the same directory from wherever the command runs.
pub fn befehl(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("build", rest)?;
        let quelle = match a.frei.as_slice() {
            [] => ".".to_string(),
            [q] => q.clone(),
            _ => return Err("`gabbro build [<sourcedir|build file>] [-D<name>=<value>]…`".into()),
        };
        let baudatei = finde_baudatei(&quelle)?;
        let v = baudatei.parent().unwrap_or(Path::new(".")).join(VORGABE_VERZEICHNIS);
        let mut z = match lies_zustand(&v) {
            Ok(z) => {
                if z.baudatei != baudatei {
                    return Err(format!(
                        "`{}` is configured for `{}`, not for `{}` -- use `gabbro setup <dir> {}` \
                         and `gabbro compile -C <dir>`",
                        v.display(),
                        z.baudatei.display(),
                        baudatei.display(),
                        quelle
                    ));
                }
                z
            }
            Err(_) => Zustand { baudatei, gesetzt: BTreeMap::new() },
        };
        for (k, w) in &a.setzen {
            z.gesetzt.insert(k.clone(), w.clone());
        }
        let (_, werte) = optionen(&z.baudatei, &z.gesetzt)?;
        sprache::werte_aus(&z.baudatei, &werte)?;
        if !a.trocken {
            schreibe_zustand(&v, &z)?;
            let zeige = anzeige(&v);
            println!("build directory {zeige} (`gabbro configure -C {zeige}` shows its options)");
            kompiliere(&lade(&v)?, &[], false)
        } else {
            let projekt = sprache::werte_aus(&z.baudatei, &werte)?;
            let (alle, _) = optionen(&z.baudatei, &z.gesetzt)?;
            kompiliere(&Geladen { verzeichnis: v, alle, werte, projekt }, &[], true)
        }
    })();
    melde("build", r)
}

/// `gabbro test [-C <builddir>] [<test>…]`: builds what the tests need, then runs them.
pub fn test(rest: &[String]) -> ExitCode {
    let a = match lies_argumente("test", rest) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let g = match lade(&verzeichnis_von(&a)) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("gabbro test: {e}");
            return ExitCode::from(2);
        }
    };
    let p = &g.projekt;
    for n in &a.frei {
        if !p.tests.iter().any(|t| &t.name == n) {
            eprintln!("gabbro test: `{n}` is no test of project `{}`", p.name);
            return ExitCode::from(2);
        }
    }
    let tests: Vec<&sprache::Test> =
        p.tests.iter().filter(|t| a.frei.is_empty() || a.frei.contains(&t.name)).collect();
    if tests.is_empty() {
        println!("project `{}` declares no test -- nothing ran, and that is not a pass", p.name);
        return ExitCode::from(2);
    }
    let noetig: Vec<String> = tests
        .iter()
        .map(|t| p.ziele[t.ziel].name.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    match kompiliere(&g, &noetig, false) {
        Ok(true) => {}
        Ok(false) => {
            println!("the tests did not run: a target they need was refused");
            return ExitCode::from(1);
        }
        Err(e) => {
            eprintln!("gabbro test: {e}");
            return ExitCode::from(2);
        }
    }
    let ziel = text_option(&g.werte, "target");
    let ausfuehrer = match ausfuehrer_fuer(&ziel) {
        Ok(x) => x,
        Err(e) => {
            println!("NOT RUN  {} test(s): {e}", tests.len());
            return ExitCode::from(2);
        }
    };
    let (mut gut, mut schlecht) = (0usize, 0usize);
    for t in &tests {
        let programm = g.verzeichnis.join(&p.ziele[t.ziel].name);
        match fuehre_aus(&ausfuehrer, &programm, t) {
            Ok(()) => {
                gut += 1;
                println!("ok       {}", t.name);
            }
            Err(e) => {
                schlecht += 1;
                println!("FAIL     {} ({}): {e}", t.name, t.ort);
            }
        }
    }
    println!("{gut} ok, {schlecht} failed, {} test(s) declared in project `{}`", p.tests.len(), p.name);
    if schlecht > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

/// How a binary of `ziel` runs on this machine: natively, or under `qemu-<arch>`.
fn ausfuehrer_fuer(ziel: &str) -> Result<Option<String>, String> {
    if std::env::consts::ARCH == ziel {
        return Ok(None);
    }
    let qemu = format!("qemu-{ziel}");
    match std::process::Command::new(&qemu).arg("-version").output() {
        Ok(r) if r.status.success() => Ok(Some(qemu)),
        _ => Err(format!(
            "this machine is {} and `{qemu}` is not on PATH -- a {ziel} binary cannot run here",
            std::env::consts::ARCH
        )),
    }
}

fn fuehre_aus(ausfuehrer: &Option<String>, programm: &Path, t: &sprache::Test) -> Result<(), String> {
    use std::io::Read;
    let mut befehl = match ausfuehrer {
        Some(q) => {
            let mut b = std::process::Command::new(q);
            b.arg(programm);
            b
        }
        None => std::process::Command::new(programm),
    };
    let mut kind = befehl
        .args(&t.argumente)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .map_err(|e| format!("{} cannot be started: {e}", programm.display()))?;
    let mut stdout = kind.stdout.take().expect("piped");
    let leser = std::thread::spawn(move || {
        let mut v = Vec::new();
        let _ = stdout.read_to_end(&mut v);
        v
    });
    let frist = std::time::Instant::now() + std::time::Duration::from_secs(t.sekunden);
    let status = loop {
        if let Some(s) = kind.try_wait().map_err(|e| e.to_string())? {
            break s;
        }
        if std::time::Instant::now() > frist {
            let _ = kind.kill();
            let _ = kind.wait();
            return Err(format!("still running after {} s -- killed", t.sekunden));
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    let ausgabe = leser.join().unwrap_or_default();
    let code = status.code().map(i64::from);
    if code != Some(t.austritt) {
        return Err(match code {
            Some(c) => format!("exit {c}, expected {}", t.austritt),
            None => "ended by a signal".to_string(),
        });
    }
    if let Some(erwartet) = &t.ausgabe {
        let ist = String::from_utf8_lossy(&ausgabe);
        if ist != erwartet.as_str() {
            return Err(format!("stdout {ist:?}, expected {erwartet:?}"));
        }
    }
    Ok(())
}

/// `gabbro install [-C <builddir>]`: builds, then copies every `install: true` program into
/// `$DESTDIR<prefix>/<bindir>`.
pub fn install(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("install", rest)?;
        if !a.frei.is_empty() {
            return Err(format!("`{}` -- install takes `-C <builddir>` only", a.frei[0]));
        }
        let g = lade(&verzeichnis_von(&a))?;
        let p = &g.projekt;
        let zu: Vec<String> = p
            .ziele
            .iter()
            .filter(|z| z.installieren)
            .map(|z| z.name.clone())
            .collect();
        if zu.is_empty() {
            println!("project `{}` marks no program `install: true` -- nothing installed", p.name);
            return Ok(true);
        }
        if !kompiliere(&g, &zu, false)? {
            return Ok(false);
        }
        let praefix = text_option(&g.werte, "prefix");
        if !praefix.starts_with('/') {
            return Err(format!("`prefix` is `{praefix}` -- an install prefix is an absolute path"));
        }
        let mut ziel = PathBuf::from(std::env::var("DESTDIR").unwrap_or_default());
        ziel.push(praefix.trim_start_matches('/'));
        ziel.push(text_option(&g.werte, "bindir"));
        std::fs::create_dir_all(&ziel).map_err(|e| format!("{}: {e}", ziel.display()))?;
        for n in &zu {
            let nach = ziel.join(n);
            std::fs::copy(g.verzeichnis.join(n), &nach).map_err(|e| format!("{}: {e}", nach.display()))?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&nach, std::fs::Permissions::from_mode(0o755))
                    .map_err(|e| format!("{}: {e}", nach.display()))?;
            }
            println!("installed {}", nach.display());
        }
        Ok(true)
    })();
    melde("install", r)
}

/// `gabbro introspect [-C <builddir>]`: the evaluated project as JSON (targets with their
/// computed units, tests, options) -- for editors and scripts.
pub fn introspect(rest: &[String]) -> ExitCode {
    let r = (|| {
        let a = lies_argumente("introspect", rest)?;
        let g = lade(&verzeichnis_von(&a))?;
        let p = &g.projekt;
        let einheiten = plane(p)?;
        let mut j = String::from("{\n");
        j.push_str(&format!("  \"project\": {{\"name\": {}, \"version\": {}, \"root\": {}}},\n",
            js(&p.name), js(&p.version), js(&p.wurzel.display().to_string())));
        j.push_str("  \"targets\": [\n");
        for (n, e) in einheiten.iter().enumerate() {
            let z = &p.ziele[e.ziel];
            let datei = match z.art {
                Art::Programm => g.verzeichnis.join(&z.name),
                Art::Objekt => g.verzeichnis.join(format!("{}.o", z.name)),
                Art::Bibliothek => g.verzeichnis.join(format!("{}.lib.ll", z.name)),
            };
            j.push_str(&format!(
                "    {{\"name\": {}, \"type\": {}, \"defined_at\": {}, \"install\": {}, \"output\": {}, \"sources\": [{}], \"unit\": [{}], \"libraries\": [{}]}}{}\n",
                js(&z.name), js(z.art.wort()), js(&z.ort), z.installieren, js(&datei.display().to_string()),
                z.dateien.iter().map(|d| js(d)).collect::<Vec<_>>().join(", "),
                e.quellen.iter().map(|(d, _)| js(d)).collect::<Vec<_>>().join(", "),
                e.bibliotheken.iter().map(|b| js(&p.ziele[*b].name)).collect::<Vec<_>>().join(", "),
                if n + 1 < einheiten.len() { "," } else { "" }
            ));
        }
        j.push_str("  ],\n  \"tests\": [\n");
        for (n, t) in p.tests.iter().enumerate() {
            j.push_str(&format!(
                "    {{\"name\": {}, \"program\": {}, \"args\": [{}], \"exit\": {}, \"timeout\": {}}}{}\n",
                js(&t.name), js(&p.ziele[t.ziel].name),
                t.argumente.iter().map(|x| js(x)).collect::<Vec<_>>().join(", "),
                t.austritt, t.sekunden,
                if n + 1 < p.tests.len() { "," } else { "" }
            ));
        }
        j.push_str("  ],\n  \"options\": [\n");
        for (n, o) in g.alle.iter().enumerate() {
            j.push_str(&format!(
                "    {{\"name\": {}, \"value\": {}, \"builtin\": {}}}{}\n",
                js(&o.name), js(&sprache::zeige_wert(&g.werte[&o.name])), o.eingebaut,
                if n + 1 < g.alle.len() { "," } else { "" }
            ));
        }
        j.push_str("  ]\n}\n");
        print!("{j}");
        Ok(true)
    })();
    melde("introspect", r)
}

/// A path as the reader typed it: relative to the working directory where it lies below it.
fn anzeige(p: &Path) -> String {
    std::env::current_dir()
        .ok()
        .and_then(|d| std::fs::canonicalize(d).ok())
        .and_then(|d| p.strip_prefix(&d).ok().map(|r| r.display().to_string()))
        .filter(|r| !r.is_empty())
        .unwrap_or_else(|| p.display().to_string())
}

/// A JSON string literal.
fn js(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn der_abdruck_trennt_verschiedene_zerlegungen() {
        assert_ne!(einheit::abdruck64(&[b"ab", b"c"]), einheit::abdruck64(&[b"a", b"bc"]));
    }

    #[test]
    fn json_ist_maskiert() {
        assert_eq!(js("a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
    }
}
