//! **`gabbro build` -- the build out of a manifest.**
//!
//! The reckoning stands in `dokumente/BAUSYSTEM.md` and was written before `bau.rs`. What is
//! held here is the part that can be run:
//!
//! * the graph is COMPUTED out of `module` and `use`, never read out of the manifest,
//! * the incremental decision is by CONTENT and not by timestamp -- **`touch` must not
//!   rebuild, and a deleted artefact must**,
//! * a unit that does not check writes no C and calls no `cc`,
//! * and the coverage line says what the build did NOT look at.

use std::process::Command;

fn lauf(argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

const MANIFEST: &str = "programmlogik/beispiel/gabbro.bau";

/// **The counter-sample: the two-file unit builds, and the C survives
/// `-Wall -Wextra -Werror`.**
#[test]
fn das_zweidateienbeispiel_baut() {
    // A first run may find the artefact current from an earlier run; either is a pass here,
    // and the incremental behaviour has its own test below.
    let (aus, fehler, code) = lauf(&["build", MANIFEST]);
    assert_eq!(code, 0, "the unit builds:\n{aus}\n{fehler}");
    assert!(
        aus.contains("built    lager") || aus.contains("current  lager"),
        "the unit is named either way:\n{aus}"
    );
}

/// **The coverage line, in the shape `abnahme.py` uses.** *"nothing found" and "nothing
/// looked at" look the same otherwise* -- and a build over two files must not read like a
/// build over the tree.
#[test]
fn der_bau_sagt_was_er_nicht_angesehen_hat() {
    let (aus, _, _) = lauf(&["build", "--dry-run", MANIFEST]);
    assert!(
        aus.contains("2 file(s) named by this manifest"),
        "what it covered:\n{aus}"
    );
    assert!(
        aus.contains("NOT looked at:") && aus.contains("stand in no unit of this manifest"),
        "and what it did not:\n{aus}"
    );
    assert!(
        aus.contains("the manifest is the reach"),
        "with the reason beside it, not only the number:\n{aus}"
    );
}

/// **Incremental by CONTENT and not by timestamp -- the whole point, in one test.**
///
/// `CLAUDE.md` carries two traps of this class in opposite directions. So both directions are
/// held: a `touch` (new mtime, same bytes) must NOT rebuild, and a deleted artefact with a
/// valid record MUST -- *the artefact's presence is checked, not believed.*
#[test]
fn inkrementell_nach_inhalt_und_nicht_nach_zeitstempel() {
    let wurzel = std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."));
    // Build once so there is something to be current about.
    let (_, _, code) = lauf(&["build", MANIFEST]);
    assert_eq!(code, 0, "the preparing build runs");

    // 1. Same bytes, new mtime -- read the file and write it straight back.
    let quelle = wurzel.join("programmlogik/beispiel/lager.gab");
    let bytes = std::fs::read(&quelle).expect("source readable");
    std::fs::write(&quelle, &bytes).expect("source writable");
    let (aus, _, code) = lauf(&["build", MANIFEST]);
    assert_eq!(code, 0, "a rewrite of the same bytes is not a change:\n{aus}");
    assert!(
        aus.contains("current  lager"),
        "the same content does NOT rebuild, however new the timestamp:\n{aus}"
    );

    // 2. The artefact is gone, the record is still valid.
    let erzeugnis = wurzel.join("target/bau-beispiel/lager.o");
    std::fs::remove_file(&erzeugnis).expect("artefact removable");
    let (aus, _, code) = lauf(&["build", MANIFEST]);
    assert_eq!(code, 0, "the build repairs the gap:\n{aus}");
    assert!(
        aus.contains("built    lager"),
        "a deleted artefact rebuilds -- the presence is CHECKED, not believed:\n{aus}"
    );
    assert!(erzeugnis.exists(), "and the artefact is back");
}

/// **The graph is computed, not read.** The manifest of the example carries no dependency
/// line at all, and the build still knows it is one unit.
#[test]
fn der_graph_wird_gerechnet_und_nicht_gelesen() {
    let manifest = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../programmlogik/beispiel/gabbro.bau"
    ))
    .expect("manifest readable");
    // Only comment lines may mention `use` -- no directive does.
    for zeile in manifest.lines() {
        let ohne = zeile.split("--").next().unwrap_or("");
        assert!(
            !ohne.contains("use ") && !ohne.contains("depends"),
            "no dependency is written down; they come out of the sources: {zeile}"
        );
    }
    let (aus, _, _) = lauf(&["build", "--dry-run", MANIFEST]);
    assert!(
        aus.contains("computed edge(s) between units"),
        "and the build says the edges are computed:\n{aus}"
    );
}

/// **Poison: the same module name in two units.** Across the tree a module name is not unique
/// (`module gift` belongs to 122 files); inside ONE build it must be, or a `use` edge would
/// have two targets and the graph would be a guess.
#[test]
fn gift_derselbe_modulname_in_zwei_einheiten() {
    let (_, fehler, code) = lauf(&[
        "build",
        "messung/einheit-proben/gift-modul-in-zwei-einheiten.bau",
    ]);
    assert_eq!(code, 1, "refused:\n{fehler}");
    assert!(
        fehler.contains("declared in unit") && fehler.contains("two targets"),
        "and it says WHY, not just that:\n{fehler}"
    );
}

/// **Poison: a unit that names no file.** A build over nothing reports success, and then
/// "nothing found" looks like "nothing looked at".
#[test]
fn gift_eine_einheit_ohne_datei() {
    let (_, fehler, code) = lauf(&["build", "messung/einheit-proben/gift-leere-einheit.bau"]);
    assert_eq!(code, 2, "refused at the manifest:\n{fehler}");
    assert!(
        fehler.contains("names no file"),
        "by name:\n{fehler}"
    );
}

/// **Poison: a unit whose files do not check.** No C is written and no `cc` is called -- a
/// generator that translates out of a refused tree undoes every pass in front of it.
///
/// **And the sites are in the FILE, not in the concatenation** -- the build renders through
/// the same offset map as `pruefe --unit`, out of the same function.
#[test]
fn gift_eine_einheit_die_nicht_durchgeht() {
    let (aus, fehler, code) = lauf(&["build", "messung/einheit-proben/gift-einheit-faellt.bau"]);
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(aus.contains("REFUSED  halb"), "the unit is named:\n{aus}");
    assert!(
        aus.contains("no C written"),
        "and nothing was written:\n{aus}"
    );
    // **The refusals go to STDOUT, like `gabbro pruefe`'s** -- they come out of the shared
    // renderer, and a refusal that changed stream between two subcommands would be a refusal
    // a harness has to look for in two places.
    assert!(
        aus.contains("programmlogik/beispiel/betrieb.gab:36:56"),
        "the site is in its own file at its own line, not in the concatenation:\n{aus}"
    );
    assert!(
        !aus.contains("<unit>:") && !fehler.contains("<unit>:"),
        "no refusal carries a line number of the joined text:\n{aus}\n{fehler}"
    );
}

/// **A different compiler flag is a different artefact -- and the build must notice.**
///
/// *This test exists because a hand mutation survived without it* (`453`): dropping the
/// compiler line out of the fingerprint left all eight probes green, and a build that switched
/// from `-O0` to `-O2` would have reported "current" over an artefact nobody asked for any
/// more. **Content alone is not the whole input.**
///
/// Two manifests, identical but for one flag, pointing at ONE output directory.
#[test]
fn eine_andere_uebersetzerfahne_baut_neu() {
    let o0 = "messung/einheit-proben/fahne-o0.bau";
    let o2 = "messung/einheit-proben/fahne-o2.bau";
    let (aus, fehler, code) = lauf(&["build", o0]);
    assert_eq!(code, 0, "the first flag builds:\n{aus}\n{fehler}");
    // Once more with the SAME manifest -- it must be current, or the test below proves
    // nothing (a build that always rebuilds would pass it for the wrong reason).
    let (aus, _, _) = lauf(&["build", o0]);
    assert!(
        aus.contains("current  fahne"),
        "the same manifest twice is current -- otherwise the next assertion is empty:\n{aus}"
    );
    let (aus, fehler, code) = lauf(&["build", o2]);
    assert_eq!(code, 0, "the second flag builds:\n{aus}\n{fehler}");
    assert!(
        aus.contains("built    fahne"),
        "ONE changed flag rebuilds, though not a source byte moved:\n{aus}"
    );
}

/// The fingerprint takes the LENGTHS of its parts too. Without that, two different file
/// lists whose bytes concatenate the same way would be one build.
#[test]
fn der_abdruck_trennt_verschiedene_zerlegungen() {
    // (This is held through the command line's own behaviour elsewhere; here the property is
    // stated on the function directly, which is why `bau` is a module of the binary crate and
    // its helper is `pub`.)
    let a: &[&[u8]] = &[b"ab", b"c"];
    let b: &[&[u8]] = &[b"a", b"bc"];
    assert_ne!(
        gabbro_bau_abdruck(a),
        gabbro_bau_abdruck(b),
        "two different decompositions are two different fingerprints"
    );
}

/// A copy of `bau::abdruck64` -- an integration test cannot reach a binary crate's modules,
/// so the property is stated against the same computation. **If the two ever disagree, this
/// test is the wrong one to trust** -- it is here for the property, not as a second
/// implementation anyone should call.
fn gabbro_bau_abdruck(teile: &[&[u8]]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for t in teile {
        for b in (t.len() as u64).to_le_bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        for b in *t {
            h ^= u64::from(*b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    h
}

// --- `kmod` and `unit … module <init> <exit>` (server lane, TODO 0e K4) -----------------
//
// The manifest's third art: a unit that becomes a LOADABLE LINUX KERNEL MODULE. What is
// held here is the part that needs no kernel -- the parsing and the four refusals. The
// artefact itself is measured where it can only be measured, in QEMU
// (`instrumente/pruefe-kernelmodul.sh`), because a `.ko` that is not loaded is a file.

fn kratz(marke: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("gabbro-kmod-{}-{marke}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("scratch directory");
    d
}

/// Writes a manifest and a tiny unit into a scratch directory and runs `--dry-run` over it.
/// `--dry-run` is the point: it walks the graph and applies every rule, and it calls neither
/// `cc` nor `make`, so a machine without kernel headers measures the same thing.
fn kmod_lauf(marke: &str, unitzeile: &str, quelle: &str, kmodzeile: &str) -> (String, String, i32) {
    let d = kratz(marke);
    std::fs::write(d.join("u.gab"), quelle).expect("unit");
    std::fs::write(d.join("melde.c"), "void gabbro_kmod_melde(void) { }\n").expect("body");
    let manifest = format!(
        "compiler cc -std=c11\nout {aus}\n{kmodzeile}{unitzeile}\n  {q}\n  {c}\n",
        aus = d.join("bau").display(),
        q = d.join("u.gab").display(),
        c = d.join("melde.c").display(),
    );
    let mpfad = d.join("manifest");
    std::fs::write(&mpfad, manifest).expect("manifest");
    lauf(&["build", "--dry-run", mpfad.to_str().expect("utf8")])
}

const KMOD_EINHEIT: &str = "module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";

/// **The good case: the manifest parses, the graph walks, the rules hold.**
#[test]
fn ein_modul_im_manifest_wird_gelesen() {
    let (aus, fehler, code) = kmod_lauf(
        "gut",
        "unit gabbro_probe module laden entladen",
        KMOD_EINHEIT,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_eq!(code, 0, "the manifest is read:\n{aus}\n{fehler}");
    assert!(aus.contains("gabbro_probe"), "the unit is named:\n{aus}");
}

/// **A `module` unit without a `kmod` line, and the other way round.** Both are a claim
/// nobody keeps: the first asks for an artefact the build cannot make, the second names two
/// paths nothing reads.
#[test]
fn modul_ohne_kmod_und_kmod_ohne_modul() {
    let (_, fehler, code) = kmod_lauf(
        "ohnekmod",
        "unit gabbro_probe module laden entladen",
        KMOD_EINHEIT,
        "",
    );
    assert_ne!(code, 0, "a module without a `kmod` line is refused");
    assert!(fehler.contains("no `kmod"), "with its reason:\n{fehler}");
    let (_, fehler, code) = kmod_lauf(
        "ohnemodul",
        "unit gabbro_probe object",
        KMOD_EINHEIT,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_ne!(code, 0, "a `kmod` line without a module unit is refused");
    assert!(fehler.contains("nothing reads"), "with its reason:\n{fehler}");
}

/// **The three ways the two calls can be uncallable**, each with its own reason: a name the
/// unit does not declare, one that takes an argument, and one that answers nothing -- the
/// last is the load verdict, and a `void` init would make every load succeed.
#[test]
fn die_beiden_rufe_des_moduls_muessen_rufbar_sein() {
    let kmod = "kmod laufzeit/kmodul /lib/modules/x/build\n";
    let (aus, _, code) = kmod_lauf(
        "kein_init",
        "unit gabbro_probe module gibtsnicht entladen",
        KMOD_EINHEIT,
        kmod,
    );
    assert_ne!(code, 0, "an init the unit does not declare is refused");
    assert!(aus.contains("declares no `gibtsnicht`"), "by name:\n{aus}");

    let mit_parameter = "module treiber::probe {
impl fn laden(n : u32) -> u32 effects { pure } costs <= 8 ops { return n; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf(
        "mit_parameter",
        "unit gabbro_probe module laden entladen",
        mit_parameter,
        kmod,
    );
    assert_ne!(code, 0, "an init with a parameter is refused");
    assert!(aus.contains("parameter(s)"), "with the arity named:\n{aus}");

    let ohne_wert = "module treiber::probe {
impl fn laden() effects { pure } costs <= 8 ops { }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) =
        kmod_lauf("ohne_wert", "unit gabbro_probe module laden entladen", ohne_wert, kmod);
    assert_ne!(code, 0, "an init that answers nothing is refused");
    assert!(aus.contains("load verdict"), "and the reason is the verdict:\n{aus}");

    let (aus, _, code) =
        kmod_lauf("gleich", "unit gabbro_probe module laden laden", KMOD_EINHEIT, kmod);
    assert_ne!(code, 0, "one function as both init and exit is refused");
    assert!(aus.contains("BOTH"), "loading and unloading are not one call:\n{aus}");
}

/// **A foreign C body belongs to a module today and nowhere else**, and the refusal says so
/// instead of compiling it into nothing. (A hosted `program` with a foreign body is a
/// build-system gap of its own -- the emission harness writes those drivers by hand.)
#[test]
fn ein_c_rumpf_ausserhalb_eines_moduls_faellt() {
    let (_, fehler, code) = kmod_lauf("crumpf", "unit gabbro_probe object", KMOD_EINHEIT, "");
    assert_ne!(code, 0, "a `.c` file in an `object` unit is refused");
    assert!(
        fehler.contains("foreign C body") && fehler.contains("kernel module"),
        "with its reason:\n{fehler}"
    );
}

/// **A `module` unit may not declare the hosted entry.** `module_init` calls the function the
/// manifest names; a `pub fn haupt()` in a kernel module is a name the loader never calls and
/// the kernel never links.
#[test]
fn ein_modul_mit_hosted_eintritt_faellt() {
    let mit_haupt = "module treiber::probe {
pub impl fn main() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf(
        "mit_haupt",
        "unit gabbro_probe module laden entladen",
        mit_haupt,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_ne!(code, 0, "a module with the hosted entry is refused");
    assert!(aus.contains("entered by the calls the manifest names"), "with its reason:\n{aus}");
}
