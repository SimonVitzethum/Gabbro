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

/// Writes `store` (a library project: `stock` exported, `util` private) and `app` (a program
/// with a `module util` of its own) below `d`; `app_build` is app's project file, `zusatz` goes
/// into app's main module.
fn two_projects(d: &Path, app_build: &str, zusatz: &str) {
    let store = d.join("store");
    let app = d.join("app");
    std::fs::create_dir_all(&store).unwrap();
    std::fs::create_dir_all(app.join("neu")).unwrap();
    std::fs::write(
        store.join("gabbro.build"),
        "project('store', version: '1.3.0')\n\
         library('stock', 'stock.gab', export: true)\n\
         library('internal', 'internal.gab')\n",
    )
    .unwrap();
    std::fs::write(store.join("gabbro.options"), "option('trace', type: 'boolean', value: false)\n").unwrap();
    std::fs::write(
        store.join("stock.gab"),
        "module stock {\nuse util::LIMIT;\npub const AMOUNT : u32 = 3;\n}\n",
    )
    .unwrap();
    std::fs::write(store.join("internal.gab"), "module util {\npub const LIMIT : u32 = 7;\n}\n").unwrap();
    let (_, fehler, code) = lauf_in(&app.join("neu"), &["new", "app"]);
    assert_eq!(code, 0, "{fehler}");
    let haupt = std::fs::read_to_string(app.join("neu/app.gab")).unwrap();
    std::fs::remove_dir_all(app.join("neu")).unwrap();
    let haupt = haupt.replacen("module app {", &format!("module app {{\n{zusatz}\n"), 1);
    std::fs::write(
        app.join("app.gab"),
        format!("module util {{\npub const OWN : u32 = 1;\n}}\n{haupt}"),
    )
    .unwrap();
    std::fs::write(app.join("gabbro.build"), app_build).unwrap();
}

const APP: &str = "project('app', version: '0.2.0')\n\
                    store = dependency('store', path: '../store', version: '>=1.2, <2')\n\
                    app = program('app', 'app.gab', dependencies: [store])\n\
                    test('runs', app, stdout: 'Hi\\n')\n";

/// **A program over a library of another project builds and runs**; both projects have a
/// `module util`, and each keeps its own.
#[test]
fn a_dependency_builds_and_runs() {
    let d = PathBuf::from(bauverzeichnis("abh"));
    two_projects(&d, APP, "use store::stock::AMOUNT;");
    let app = d.join("app");
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&app, &["setup", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("dependency store 1.3.0"), "{aus}");
    assert!(Path::new(&b).join("gabbro.lock").exists(), "setup writes the lock");
    let (aus, fehler, code) = lauf_in(&app, &["compile", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    assert!(aus.contains("built    store:stock") && aus.contains("built    app"), "{aus}");
    let (aus, fehler, code) = lauf_in(&app, &["test", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, _, _) = lauf_in(&app, &["introspect", "-C", &b]);
    assert!(aus.contains("\"store:internal\"") && aus.contains("\"store:stock\""), "{aus}");
    assert!(aus.contains("\"name\": \"store\", \"version\": \"1.3.0\", \"namespace\": \"store\""), "{aus}");
    // **A dependency that changes under the build is named, never swapped in silently.**
    std::fs::write(
        d.join("store/stock.gab"),
        "module stock {\nuse util::LIMIT;\npub const AMOUNT : u32 = 4;\n}\n",
    )
    .unwrap();
    let (aus, fehler, code) = lauf_in(&app, &["compile", "-C", &b]);
    assert_eq!(code, 2, "{aus}\n{fehler}");
    assert!(fehler.contains("the dependencies changed") && fehler.contains("project=store"), "{fehler}");
    let (aus, fehler, code) = lauf_in(&app, &["configure", "-C", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf_in(&app, &["compile", "-C", &b]);
    assert_eq!(code, 0, "accepted by configure:\n{aus}\n{fehler}");
    weg(&d.display().to_string());
}

/// **Every refusal of the dependency rules, by name.**
#[test]
fn dependency_refusals_by_name() {
    let faelle: [(&str, &str, &str); 7] = [
        // a private library of the dependency
        (APP, "use store::util::LIMIT;", "which it does not export"),
        // used, not declared
        (
            "project('app')\nstore = dependency('store', path: '../store')\nprogram('app', 'app.gab')\n",
            "use store::stock::AMOUNT;",
            "does not declare it -- add `dependencies: [store]`",
        ),
        // declared, not used
        (APP, "", "delete `store` there"),
        // the version
        (
            "project('app')\nstore = dependency('store', path: '../store', version: '>=2')\n\
             program('app', 'app.gab', dependencies: [store])\n",
            "use store::stock::AMOUNT;",
            "requires version `>=2`, and",
        ),
        // an option the dependency does not have
        (
            "project('app')\nstore = dependency('store', path: '../store', options: ['nichts=1'])\n\
             program('app', 'app.gab', dependencies: [store])\n",
            "use store::stock::AMOUNT;",
            "`nichts` is no option of project `store`",
        ),
        // a missing project
        (
            "project('app')\nstore = dependency('store', path: '../fehlt')\n\
             program('app', 'app.gab', dependencies: [store])\n",
            "use store::stock::AMOUNT;",
            "holds no `gabbro.build`",
        ),
        // the dependency's own option, set well, still builds the plan
        (
            "project('app')\nstore = dependency('store', path: '../store', options: ['trace=true'])\n\
             program('app', 'app.gab', dependencies: [store])\n",
            "use store::stock::AMOUNT;",
            "",
        ),
    ];
    for (n, (build, zusatz, text)) in faelle.iter().enumerate() {
        let d = PathBuf::from(bauverzeichnis(&format!("abh-gift-{n}")));
        two_projects(&d, build, zusatz);
        let b = d.join("bau").display().to_string();
        let (aus, fehler, code) = lauf_in(&d.join("app"), &["setup", &b]);
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
fn one_short_name_twice_falls_at_n039() {
    let d = PathBuf::from(bauverzeichnis("abh-kurzname"));
    two_projects(&d, APP, "use store::stock::AMOUNT;");
    let app = d.join("app/app.gab");
    let t = std::fs::read_to_string(&app).unwrap().replace("pub const OWN : u32 = 1;", "pub const LIMIT : u32 = 1;");
    std::fs::write(&app, t).unwrap();
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&d.join("app"), &["setup", &b]);
    assert_eq!(code, 0, "{aus}\n{fehler}");
    let (aus, fehler, code) = lauf_in(&d.join("app"), &["compile", "-C", &b]);
    assert_eq!(code, 1, "{aus}\n{fehler}");
    assert!(aus.contains("REFUSED  app") && aus.contains("N039"), "{aus}\n{fehler}");
    weg(&d.display().to_string());
}

/// **A cycle of projects is refused; a path into a project not declared is refused.**
#[test]
fn cycle_and_invisible_paths_refused() {
    let d = PathBuf::from(bauverzeichnis("abh-zyklus"));
    two_projects(&d, APP, "use store::stock::AMOUNT;");
    std::fs::write(
        d.join("store/gabbro.build"),
        "project('store', version: '1.3.0')\napp = dependency('app', path: '../app')\n\
         library('stock', 'stock.gab', export: true, dependencies: [app])\nlibrary('internal', 'internal.gab')\n",
    )
    .unwrap();
    let b = d.join("bau").display().to_string();
    let (_, fehler, code) = lauf_in(&d.join("app"), &["setup", &b]);
    assert_eq!(code, 2, "{fehler}");
    assert!(fehler.contains("the projects form a cycle"), "{fehler}");
    weg(&d.display().to_string());

    // `store` names the program's module without declaring the program.
    let d = PathBuf::from(bauverzeichnis("abh-sicht"));
    two_projects(&d, APP, "use store::stock::AMOUNT;");
    std::fs::write(
        d.join("store/stock.gab"),
        "module stock {\nuse util::LIMIT;\npub const AMOUNT : u32 = app::util::LIMIT;\n}\n",
    )
    .unwrap();
    let b = d.join("bau").display().to_string();
    let (aus, fehler, code) = lauf_in(&d.join("app"), &["setup", &b]);
    assert_eq!(code, 2, "{aus}\n{fehler}");
    assert!(fehler.contains("reaches project `app`, which this file's project does not declare"), "{fehler}");
    weg(&d.display().to_string());
}
