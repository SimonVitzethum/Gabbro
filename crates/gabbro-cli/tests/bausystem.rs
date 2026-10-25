//! **The build system after Meson: `gabbro setup`, `compile`, `test`, `install`, `configure`,
//! `introspect`, and the one-step `build`.**
//!
//! `dokumente/BUILD-SYSTEM.md` is the long form. What is held here is the part that can be run:
//!
//! * the edges between targets are COMPUTED out of `module` and `use`, never read out of the
//!   project file (a library's files join the units that use it),
//! * the incremental decision is by CONTENT and not by timestamp -- **`touch` must not
//!   rebuild, and a deleted artefact must**,
//! * a build directory is ONE configuration, and changing the target rebuilds,
//! * every refusal names its file and line, or the target it is about,
//! * and the coverage line says what the build did NOT look at.

use std::path::{Path, PathBuf};
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn lauf(argumente: &[&str]) -> (String, String, i32) {
    lauf_in(&wurzel(), argumente)
}

fn lauf_in(verzeichnis: &Path, argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(verzeichnis)
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

/// A build directory of this probe's own, empty: a product left by an earlier run would make
/// "current" and "built" depend on history, not on the input.
fn bauverzeichnis(marke: &str) -> String {
    let d = wurzel().join(format!("target/bausystem-{}-{marke}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    d.display().to_string()
}

fn weg(d: &str) {
    let _ = std::fs::remove_dir_all(d);
}

const BEISPIEL: &str = "programmlogik/beispiel";

/// **The two-file example builds: a library and an object that uses it.**
#[test]
fn das_zweidateienbeispiel_baut() {
    let b = bauverzeichnis("beispiel");
    let (aus, fehler, code) = lauf(&["setup", &b, BEISPIEL]);
    assert_eq!(code, 0, "setup runs:\n{aus}\n{fehler}");
    assert!(aus.contains("2 target(s), 0 test(s)"), "{aus}");
    let (aus, fehler, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "the targets build:\n{aus}\n{fehler}");
    assert!(aus.contains("built    lager") && aus.contains("built    betrieb"), "{aus}");
    assert!(Path::new(&b).join("betrieb.o").exists(), "the object is there");
    weg(&b);
}

/// **The graph is computed, not read.** The project file carries no dependency at all, and
/// the plan still knows that `betrieb` rests on `lager`.
#[test]
fn der_graph_wird_gerechnet_und_nicht_gelesen() {
    let text = std::fs::read_to_string(wurzel().join(BEISPIEL).join("gabbro.build"))
        .expect("project file readable");
    for zeile in text.lines() {
        let ohne = zeile.split('#').next().unwrap_or("");
        assert!(
            !ohne.contains("deps") && !ohne.contains("use "),
            "no dependency is written down; they come out of the sources: {zeile}"
        );
    }
    let b = bauverzeichnis("graph");
    lauf(&["setup", &b, BEISPIEL]);
    let (aus, _, code) = lauf(&["compile", "-C", &b, "--dry-run"]);
    assert_eq!(code, 0, "{aus}");
    assert!(aus.contains("object betrieb (2 file(s), computed: lager)"), "the edge is computed:\n{aus}");
    weg(&b);
}

/// **The coverage line.** *"nothing found" and "nothing looked at" look the same otherwise.*
#[test]
fn der_bau_sagt_was_er_nicht_angesehen_hat() {
    let b = bauverzeichnis("deckung");
    lauf(&["setup", &b, BEISPIEL]);
    let (aus, _, _) = lauf(&["compile", "-C", &b, "--dry-run"]);
    assert!(aus.contains("2 file(s) named by this project"), "what it covered:\n{aus}");
    assert!(aus.contains("NOT looked at:") && aus.contains("stand in no target"), "and what not:\n{aus}");
    weg(&b);
}

/// **Incremental by CONTENT and not by timestamp.** A `touch` (new mtime, same bytes) must NOT
/// rebuild; a deleted artefact with a valid record MUST -- *the presence is checked, not
/// believed.*
#[test]
fn inkrementell_nach_inhalt_und_nicht_nach_zeitstempel() {
    // A copy of the example of its own: rewriting a file of the shared tree would race with
    // the probes that read it in parallel.
    let d = PathBuf::from(bauverzeichnis("inkrement"));
    std::fs::create_dir_all(&d).unwrap();
    for f in ["gabbro.build", "lager.gab", "betrieb.gab"] {
        std::fs::copy(wurzel().join(BEISPIEL).join(f), d.join(f)).unwrap();
    }
    let b = d.join("bau").display().to_string();
    lauf(&["setup", &b, &d.display().to_string()]);
    let (_, _, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "the preparing build runs");

    let quelle = d.join("lager.gab");
    let bytes = std::fs::read(&quelle).expect("source readable");
    std::fs::write(&quelle, &bytes).expect("source writable");
    let (aus, _, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}");
    assert!(aus.contains("current  lager") && aus.contains("current  betrieb"), "same content, no rebuild:\n{aus}");

    let erzeugnis = Path::new(&b).join("betrieb.o");
    std::fs::remove_file(&erzeugnis).expect("artefact removable");
    let (aus, _, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}");
    assert!(aus.contains("built    betrieb"), "a deleted artefact rebuilds:\n{aus}");
    assert!(erzeugnis.exists(), "and the artefact is back");
    weg(&d.display().to_string());
}

/// **A build directory is ONE configuration**, and the target is part of every fingerprint:
/// `configure -Dtarget=aarch64` rebuilds though not a source byte moved.
#[test]
fn ein_anderes_ziel_baut_neu() {
    let b = bauverzeichnis("ziel");
    lauf(&["setup", &b, BEISPIEL, "-Dtarget=x86_64"]);
    let (aus, fehler, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, _, _) = lauf(&["compile", "-C", &b]);
    assert!(aus.contains("current  betrieb"), "twice is current:\n{aus}");
    let (aus, fehler, code) = lauf(&["configure", "-C", &b, "-Dtarget=aarch64"]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("target") && aus.contains("aarch64"), "{aus}");
    let (aus, fehler, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("built    betrieb"), "the changed target rebuilds:\n{aus}");
    weg(&b);
}

/// **A refused option value never reaches the build directory.**
#[test]
fn ein_falscher_optionswert_faellt_mit_namen() {
    let b = bauverzeichnis("option");
    let (_, fehler, code) = lauf(&["setup", &b, BEISPIEL, "-Dtarget=sparc"]);
    assert_eq!(code, 2, "{fehler}");
    assert!(fehler.contains("`sparc` is none of `x86_64`, `aarch64`"), "{fehler}");
    assert!(!Path::new(&b).exists(), "nothing was written");
    let (_, fehler, code) = lauf(&["setup", &b, BEISPIEL, "-Dnirgends=1"]);
    assert_eq!(code, 2);
    assert!(fehler.contains("`nirgends` is no option"), "{fehler}");
    lauf(&["setup", &b, BEISPIEL]);
    let (_, fehler, code) = lauf(&["configure", "-C", &b, "-Dbuildtype=fast"]);
    assert_eq!(code, 2, "{fehler}");
    let zustand = std::fs::read_to_string(Path::new(&b).join("gabbro-setup.txt")).unwrap();
    assert!(!zustand.contains("fast"), "the directory kept its configuration:\n{zustand}");
    let (_, fehler, code) = lauf(&["setup", &b, BEISPIEL]);
    assert_eq!(code, 2, "a second setup over a build directory is refused");
    assert!(fehler.contains("already a build directory"), "{fehler}");
    weg(&b);
}

/// **A library builds a program from two targets** -- the case the manifest build refused
/// (a unit resting on another unit) builds now, and the binary runs.
#[test]
fn ein_programm_ueber_einer_bibliothek_baut() {
    let b = bauverzeichnis("bibliothek");
    let (aus, fehler, code) = lauf(&["setup", &b, "messung/einheit-proben/zwei-einheiten.build"]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf(&["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("built    rechenwerk") && aus.contains("built    haupt"), "{aus}");
    let (aus, _, _) = lauf(&["introspect", "-C", &b]);
    assert!(
        aus.contains("\"name\": \"haupt\", \"type\": \"program\"")
            && aus.contains("\"libraries\": [\"rechenwerk\"]"),
        "introspection names the computed library:\n{aus}"
    );
    assert!(Path::new(&b).join("haupt").exists(), "the program is linked");
    weg(&b);
}

/// **Poisons, each refused by name.**
#[test]
fn gifte_fallen_mit_namen() {
    for (datei, schritt, code_soll, text) in [
        ("messung/einheit-proben/gift-modul-in-zwei-einheiten.build", "setup", 2, "two targets"),
        ("messung/einheit-proben/gift-leere-einheit.build", "setup", 2, "names no source"),
        ("messung/einheit-proben/gift-programm-nutzt-objekt.build", "setup", 2, "make `rechenwerk` a `library`"),
        ("messung/einheit-proben/gift-programm-ohne-main.build", "compile", 1, "names no entry"),
        ("messung/einheit-proben/gift-einheit-faellt.build", "compile", 1, "error(s) -- no IR written"),
        ("messung/einheit-proben/gift-programm-ohne-kante.build", "compile", 1, "error(s) -- no IR written"),
        ("messung/proben/gift-eintritt-in-bibliothek.build", "compile", 1, "carries the entry `main`"),
    ] {
        let b = bauverzeichnis(&format!("gift-{}", datei.len()));
        let (aus, fehler, code) = lauf(&["setup", &b, datei]);
        if schritt == "setup" {
            assert_eq!(code, code_soll, "{datei}:\n{aus}\n{fehler}");
            assert!(fehler.contains(text), "{datei} by name (`{text}`):\n{fehler}");
        } else {
            assert_eq!(code, 0, "{datei} configures:\n{aus}\n{fehler}");
            let (aus, fehler, code) = lauf(&["compile", "-C", &b]);
            assert_eq!(code, code_soll, "{datei}:\n{aus}\n{fehler}");
            assert!(aus.contains(text), "{datei} by name (`{text}`):\n{aus}");
        }
        weg(&b);
    }
}

/// **The build language refuses at file and line**, and what the build does not do (C, a
/// written dependency list) is refused by name.
#[test]
fn die_baudatei_faellt_mit_zeile() {
    let d = PathBuf::from(bauverzeichnis("sprache"));
    std::fs::create_dir_all(&d).unwrap();
    for (text, wort) in [
        ("project('p')\nprogram('a', 'a.c')\n", "gabbro.build:2: `a.c` is no `.gab` file"),
        ("project('p')\nprogram('a', 'a.gab', deps: [])\n", "gabbro.build:2: `program` takes no `deps:`"),
        ("project('p')\ncustom_target('x')\n", "gabbro.build:2: `custom_target` is no function"),
        ("project('p')\nif true\n", "the file ends before `elif`"),
        ("program('a', 'a.gab')\n", "before `project(...)`"),
    ] {
        std::fs::write(d.join("gabbro.build"), text).unwrap();
        let (_, fehler, code) = lauf(&["setup", &d.join("b").display().to_string(), &d.display().to_string()]);
        assert_eq!(code, 2, "{text}\n{fehler}");
        assert!(fehler.contains(wort), "`{wort}`:\n{fehler}");
    }
    weg(&d.display().to_string());
}

/// **Options, subdirectories, tests and install, end to end** on a project written here.
#[test]
fn optionen_unterverzeichnisse_tests_und_installation() {
    let d = PathBuf::from(bauverzeichnis("projekt"));
    std::fs::create_dir_all(d.join("werkzeuge")).unwrap();
    // The source is the `gabbro new` skeleton: libc-free, it prints `Hi`.
    std::fs::create_dir_all(d.join("neu")).unwrap();
    let (_, fehler, code) = lauf_in(&d.join("neu"), &["new", "hallo"]);
    assert_eq!(code, 0, "{fehler}");
    std::fs::rename(d.join("neu/hallo.gab"), d.join("werkzeuge/hallo.gab")).unwrap();
    std::fs::remove_dir_all(d.join("neu")).unwrap();
    std::fs::write(
        d.join("gabbro.options"),
        "option('mit_werkzeugen', type: 'boolean', value: true, description: 'build the tools')\n",
    )
    .unwrap();
    std::fs::write(
        d.join("gabbro.build"),
        "project('p', version: '2.0')\nif get_option('mit_werkzeugen')\n  subdir('werkzeuge')\nendif\n",
    )
    .unwrap();
    std::fs::write(
        d.join("werkzeuge/gabbro.build"),
        "hallo = program('hallo', files('hallo.gab'), install: true)\n\
         test('laeuft', hallo, exit: 0, stdout: 'Hi\\n')\n\
         test('falsche-ausgabe', hallo, stdout: 'nein')\n",
    )
    .unwrap();
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&d, &["setup", &b, "-Dmit_werkzeugen=false"]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("0 target(s), 0 test(s)"), "the option removes the subdirectory:\n{aus}");
    let (aus, fehler, code) = lauf_in(&d, &["configure", "-C", &b, "-Dmit_werkzeugen=true"]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf_in(&d, &["test", "-C", &b, "laeuft"]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("ok       laeuft") && aus.contains("1 ok, 0 failed"), "{aus}");
    let (aus, _, code) = lauf_in(&d, &["test", "-C", &b, "falsche-ausgabe"]);
    assert_eq!(code, 1, "a wrong output fails:\n{aus}");
    assert!(aus.contains("FAIL     falsche-ausgabe (werkzeuge/gabbro.build:3)"), "{aus}");
    let ziel = d.join("ziel");
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(["install", "-C", &b])
        .current_dir(&d)
        .env("DESTDIR", &ziel)
        .output()
        .expect("gabbro runs");
    assert_eq!(aus.status.code(), Some(0), "{}", String::from_utf8_lossy(&aus.stderr));
    assert!(ziel.join("usr/local/bin/hallo").exists(), "installed under DESTDIR/prefix/bindir");
    weg(&d.display().to_string());
}

// ---------------------------------------------------------------- dependencies (BUILD-SYSTEM §7.3)

/// Writes `lager` (a library project: `bestand` exported, `util` private) and `werk` (a program
/// with a `module util` of its own) below `d`; `werk_build` is werk's project file, `zusatz` goes
/// into werk's main module.
fn zwei_projekte(d: &Path, werk_build: &str, zusatz: &str) {
    let lager = d.join("lager");
    let werk = d.join("werk");
    std::fs::create_dir_all(&lager).unwrap();
    std::fs::create_dir_all(werk.join("neu")).unwrap();
    std::fs::write(
        lager.join("gabbro.build"),
        "project('lager', version: '1.3.0')\n\
         library('bestand', 'bestand.gab', export: true)\n\
         library('intern', 'intern.gab')\n",
    )
    .unwrap();
    std::fs::write(lager.join("gabbro.options"), "option('spur', type: 'boolean', value: false)\n").unwrap();
    std::fs::write(
        lager.join("bestand.gab"),
        "module bestand {\nuse util::GRENZE;\npub const MENGE : u32 = 3;\n}\n",
    )
    .unwrap();
    std::fs::write(lager.join("intern.gab"), "module util {\npub const GRENZE : u32 = 7;\n}\n").unwrap();
    let (_, fehler, code) = lauf_in(&werk.join("neu"), &["new", "werk"]);
    assert_eq!(code, 0, "{fehler}");
    let haupt = std::fs::read_to_string(werk.join("neu/werk.gab")).unwrap();
    std::fs::remove_dir_all(werk.join("neu")).unwrap();
    let haupt = haupt.replacen("module werk {", &format!("module werk {{\n{zusatz}\n"), 1);
    std::fs::write(
        werk.join("werk.gab"),
        format!("module util {{\npub const EIGEN : u32 = 1;\n}}\n{haupt}"),
    )
    .unwrap();
    std::fs::write(werk.join("gabbro.build"), werk_build).unwrap();
}

const WERK: &str = "project('werk', version: '0.2.0')\n\
                    lager = dependency('lager', path: '../lager', version: '>=1.2, <2')\n\
                    werk = program('werk', 'werk.gab', dependencies: [lager])\n\
                    test('laeuft', werk, stdout: 'Hi\\n')\n";

/// **A program over a library of another project builds and runs**; both projects have a
/// `module util`, and each keeps its own.
#[test]
fn eine_abhaengigkeit_baut_und_laeuft() {
    let d = PathBuf::from(bauverzeichnis("abh"));
    zwei_projekte(&d, WERK, "use lager::bestand::MENGE;");
    let werk = d.join("werk");
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&werk, &["setup", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("dependency lager 1.3.0"), "{aus}");
    assert!(Path::new(&b).join("gabbro.lock").exists(), "setup writes the lock");
    let (aus, fehler, code) = lauf_in(&werk, &["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("built    lager:bestand") && aus.contains("built    werk"), "{aus}");
    let (aus, fehler, code) = lauf_in(&werk, &["test", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, _, _) = lauf_in(&werk, &["introspect", "-C", &b]);
    assert!(aus.contains("\"lager:intern\"") && aus.contains("\"lager:bestand\""), "{aus}");
    assert!(aus.contains("\"name\": \"lager\", \"version\": \"1.3.0\", \"namespace\": \"lager\""), "{aus}");
    // **A dependency that changes under the build is named, never swapped in silently.**
    std::fs::write(
        d.join("lager/bestand.gab"),
        "module bestand {\nuse util::GRENZE;\npub const MENGE : u32 = 4;\n}\n",
    )
    .unwrap();
    let (aus, fehler, code) = lauf_in(&werk, &["compile", "-C", &b]);
    assert_eq!(code, 2, "{aus}\n{fehler}");
    assert!(fehler.contains("the dependencies changed") && fehler.contains("project=lager"), "{fehler}");
    let (aus, fehler, code) = lauf_in(&werk, &["configure", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf_in(&werk, &["compile", "-C", &b]);
    assert_eq!(code, 0, "accepted by configure:\n{aus}\n{fehler}");
    weg(&d.display().to_string());
}

/// **Every refusal of the dependency rules, by name.**
#[test]
fn abhaengigkeiten_fallen_mit_namen() {
    let faelle: [(&str, &str, &str); 7] = [
        // a private library of the dependency
        (WERK, "use lager::util::GRENZE;", "which it does not export"),
        // used, not declared
        (
            "project('werk')\nlager = dependency('lager', path: '../lager')\nprogram('werk', 'werk.gab')\n",
            "use lager::bestand::MENGE;",
            "does not declare it -- add `dependencies: [lager]`",
        ),
        // declared, not used
        (WERK, "", "delete `lager` there"),
        // the version
        (
            "project('werk')\nlager = dependency('lager', path: '../lager', version: '>=2')\n\
             program('werk', 'werk.gab', dependencies: [lager])\n",
            "use lager::bestand::MENGE;",
            "requires version `>=2`, and",
        ),
        // an option the dependency does not have
        (
            "project('werk')\nlager = dependency('lager', path: '../lager', options: ['nichts=1'])\n\
             program('werk', 'werk.gab', dependencies: [lager])\n",
            "use lager::bestand::MENGE;",
            "`nichts` is no option of project `lager`",
        ),
        // a missing project
        (
            "project('werk')\nlager = dependency('lager', path: '../fehlt')\n\
             program('werk', 'werk.gab', dependencies: [lager])\n",
            "use lager::bestand::MENGE;",
            "holds no `gabbro.build`",
        ),
        // the dependency's own option, set well, still builds the plan
        (
            "project('werk')\nlager = dependency('lager', path: '../lager', options: ['spur=true'])\n\
             program('werk', 'werk.gab', dependencies: [lager])\n",
            "use lager::bestand::MENGE;",
            "",
        ),
    ];
    for (n, (build, zusatz, text)) in faelle.iter().enumerate() {
        let d = PathBuf::from(bauverzeichnis(&format!("abh-gift-{n}")));
        zwei_projekte(&d, build, zusatz);
        let b = d.join("bau").display().to_string();
        let (aus, fehler, code) = lauf_in(&d.join("werk"), &["setup", &b]);
        if text.is_empty() {
            assert_eq!(code, 0, "case {n}:\n{aus}\n{fehler}");
        } else {
            assert_eq!(code, 2, "case {n} is refused:\n{aus}\n{fehler}");
            assert!(fehler.contains(text), "case {n} by name (`{text}`):\n{fehler}");
        }
        weg(&d.display().to_string());
    }
}

/// **Two projects may not export an item of one short name** (`N039`): carriers and symbols are
/// named by their short name in effects and in the product, so the second would be the first.
/// Modules of one name are two modules; items of one name are refused by name.
#[test]
fn gleiche_kurznamen_fallen_mit_n039() {
    let d = PathBuf::from(bauverzeichnis("abh-kurzname"));
    zwei_projekte(&d, WERK, "use lager::bestand::MENGE;");
    let werk = d.join("werk/werk.gab");
    let t = std::fs::read_to_string(&werk).unwrap().replace("pub const EIGEN : u32 = 1;", "pub const GRENZE : u32 = 1;");
    std::fs::write(&werk, t).unwrap();
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&d.join("werk"), &["setup", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf_in(&d.join("werk"), &["compile", "-C", &b]);
    assert_eq!(code, 1, "{aus}\n{fehler}");
    assert!(aus.contains("REFUSED  werk") && aus.contains("N039"), "{aus}\n{fehler}");
    weg(&d.display().to_string());
}

/// **A cycle of projects is refused; a path into a project not declared is refused.**
#[test]
fn zyklus_und_unsichtbares_fallen() {
    let d = PathBuf::from(bauverzeichnis("abh-zyklus"));
    zwei_projekte(&d, WERK, "use lager::bestand::MENGE;");
    std::fs::write(
        d.join("lager/gabbro.build"),
        "project('lager', version: '1.3.0')\nwerk = dependency('werk', path: '../werk')\n\
         library('bestand', 'bestand.gab', export: true, dependencies: [werk])\nlibrary('intern', 'intern.gab')\n",
    )
    .unwrap();
    let b = d.join("bau").display().to_string();
    let (_, fehler, code) = lauf_in(&d.join("werk"), &["setup", &b]);
    assert_eq!(code, 2, "{fehler}");
    assert!(fehler.contains("the projects form a cycle"), "{fehler}");
    weg(&d.display().to_string());

    // `lager` names the program's module without declaring the program.
    let d = PathBuf::from(bauverzeichnis("abh-sicht"));
    zwei_projekte(&d, WERK, "use lager::bestand::MENGE;");
    std::fs::write(
        d.join("lager/bestand.gab"),
        "module bestand {\nuse util::GRENZE;\npub const MENGE : u32 = werk::util::GRENZE;\n}\n",
    )
    .unwrap();
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&d.join("werk"), &["setup", &b]);
    assert_eq!(code, 2, "{aus}\n{fehler}");
    assert!(fehler.contains("reaches project `werk`, which this file's project does not declare"), "{fehler}");
    weg(&d.display().to_string());
}
