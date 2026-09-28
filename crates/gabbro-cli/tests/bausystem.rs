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

/// **The twelve primitives the module runtime calls, as a program declares them** (server
/// lane, 2026-09-28, TODO section 0e K7).
///
/// Held against `laufzeit/kmodul/bindung.h` by `bau.rs::bindungsregel`, which every test
/// below goes through: a `module` unit that binds none of these is refused, so this snippet
/// is what makes the OTHER refusals measurable. The real thing a program would name is
/// `bibliothek/linux-kmod/linux-kmod.gab` -- this is the same declarations, inline, because
/// these tests write their unit into a scratch directory.
const KMOD_BINDUNG: &str = "
module bindung::kern {
extern fn gabbro_kern_melden(code : u32, a : u64, b : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_reserve(bytes : u64) -> u64 effects { pure } costs <= 8 ops;
extern fn gabbro_kern_freigeben(basis : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_vorrat() -> u64 effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_init(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_nimm(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_gib(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_nimm_maskiert(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_gib_maskiert(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_kernnummer() -> u32 effects { pure } costs <= 8 ops;
extern fn gabbro_kern_faden_start(f : u64, koerper : u64) -> u32 effects { pure } costs <= 8 ops;
extern fn gabbro_kern_faden_warte(f : u64) effects { pure } costs <= 8 ops;
}
";

/// Writes a manifest and a tiny unit into a scratch directory and runs `--dry-run` over it.
/// `--dry-run` is the point: it walks the graph and applies every rule, and it calls neither
/// `cc` nor `make`, so a machine without kernel headers measures the same thing.
///
/// **The binding travels with the unit** (K7): every `module` must bind the primitives its
/// runtime calls, so a helper that left them out would measure that rule and nothing else.
/// [`kmod_lauf_roh`] is the door for the two tests that want exactly that.
fn kmod_lauf(marke: &str, unitzeile: &str, quelle: &str, kmodzeile: &str) -> (String, String, i32) {
    kmod_lauf_roh(marke, unitzeile, quelle, kmodzeile, true, false)
}

/// `bindung`: append the twelve declarations. `kopf`: name a `stdatomic.h` among the unit's
/// files -- the memory model of an `atomic`, which a program supplies the same way
/// (`bibliothek/linux-kmod/stdatomic.h`).
fn kmod_lauf_roh(
    marke: &str,
    unitzeile: &str,
    quelle: &str,
    kmodzeile: &str,
    bindung: bool,
    kopf: bool,
) -> (String, String, i32) {
    let d = kratz(marke);
    let mut text = quelle.to_string();
    if bindung {
        text.push_str(KMOD_BINDUNG);
    }
    std::fs::write(d.join("u.gab"), text).expect("unit");
    std::fs::write(d.join("melde.c"), "void gabbro_kmod_melde(void) { }\n").expect("body");
    let mut dateien = format!("  {}\n", d.join("u.gab").display());
    // The header stands BEFORE the `.c` body, so that the test which asks about a header in
    // a non-module unit measures the header rule and not the one beside it (both refuse,
    // and the first one reached is the one that speaks).
    if kopf {
        std::fs::write(d.join("stdatomic.h"), "/* the program's memory model */\n")
            .expect("header");
        dateien.push_str(&format!("  {}\n", d.join("stdatomic.h").display()));
    }
    dateien.push_str(&format!("  {}\n", d.join("melde.c").display()));
    let manifest = format!(
        "compiler cc -std=c11\nout {aus}\n{kmodzeile}{unitzeile}\n{dateien}",
        aus = d.join("bau").display(),
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

/// **A foreign C body belonged to a module and nowhere else, and since K8 it does not**
/// (server lane, 2026-09-28, TODO section 0e K8; the test held the other way until then).
///
/// The refusal it replaces was honest about itself: *"a hosted `program` with a foreign body
/// is a build-system gap of its own -- naming it here would be a promise this build does not
/// keep."* K8 is where the promise had to be kept. The hosted runtime's operating-system
/// calls are declarations the PROGRAM defines (`laufzeit/bindung.h`), the bodies that define
/// them are an ordinary `.c` file of the unit (`bibliothek/linux/linux.c`), and a binding the
/// build refused to compile would have been a library nobody could use.
///
/// What is checked is the whole of what changed: the unit BUILDS, and its body became an
/// object beside the unit's own. *A build that accepted the file and compiled nothing would
/// pass the first half and link nothing* -- which is the shape the old refusal named.
#[test]
fn ein_c_rumpf_ausserhalb_eines_moduls_wird_uebersetzt() {
    let d = kratz("crumpf");
    std::fs::write(d.join("u.gab"), KMOD_EINHEIT).expect("unit");
    std::fs::write(d.join("melde.c"), "void gabbro_kmod_melde(void) { }\n").expect("body");
    let manifest = format!(
        "compiler cc -std=c11\nout {aus}\nunit gabbro_probe object\n  {q}\n  {c}\n",
        aus = d.join("bau").display(),
        q = d.join("u.gab").display(),
        c = d.join("melde.c").display(),
    );
    let mpfad = d.join("manifest");
    std::fs::write(&mpfad, manifest).expect("manifest");
    let (aus, fehler, code) = lauf(&["build", mpfad.to_str().expect("utf8")]);
    assert_eq!(code, 0, "an `object` unit may carry its own C body:\n{aus}\n{fehler}");
    assert!(
        d.join("bau").join("gabbro_probe.fremd0.o").is_file(),
        "and the build compiled it, beside the unit's own object:\n{aus}"
    );
}

/// **A `module` unit may declare an integer `atomic` and may NOT declare a floating-point
/// one** -- and both answers arrive before a byte of C is written (server lane, TODO section
/// 0e K6; the test held the other way until 2026-09-28).
///
/// Session 3 refused EVERY `atomic` in a module: the lowering did not exist, and one nobody
/// had related to the goal theorem's atomic rely would have made the wall green and the claim
/// false. Session 5 built it (`laufzeit/kmodul/include/stdatomic.h`: the emitter's nine call
/// forms onto `READ_ONCE`/`WRITE_ONCE`, `smp_load_acquire`/`smp_store_release` and the
/// `try_cmpxchg` family, each row at least as strong as the C11 operation it replaces, under
/// the named assumption (M11) of `Zielsatz/Spec.lean`). What is left is the float, which no
/// barrier repairs -- the FPU is not usable in kernel context without `kernel_fpu_begin`.
///
/// **The `u32` half is the one that would rot silently.** A rule that kept refusing every
/// atomic would leave this file green while the lowering beside it went unused, so the
/// positive direction is asserted first.
#[test]
fn ein_modul_mit_atomic_wird_gesenkt_und_ein_gleitkomma_atomic_faellt() {
    let mit_atomic = "atomic STAND : u32 relaxed;
module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    // **And it names a `stdatomic.h`**, because the memory model of an `atomic` is the
    // program's too since K7 -- see `ein_modul_mit_atomic_ohne_speichermodell_faellt` for
    // the other direction of that.
    let (aus, fehler, code) = kmod_lauf_roh(
        "mit_atomic",
        "unit gabbro_probe module laden entladen",
        mit_atomic,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
        true,
        true,
    );
    assert_eq!(code, 0, "a module with an integer `atomic` builds its plan:\n{aus}\n{fehler}");

    let mit_gleitkomma = "atomic PEGEL : f64 relaxed;
module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "mit_gleitkomma",
        "unit gabbro_probe module laden entladen",
        mit_gleitkomma,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
        true,
        true,
    );
    assert_ne!(code, 0, "a module with a floating-point `atomic` is refused");
    assert!(aus.contains("floating-point atomic `PEGEL`"), "by name:\n{aus}");
    assert!(aus.contains("kernel_fpu_begin"), "with its reason:\n{aus}");
    assert!(
        aus.contains("ARE lowered"),
        "and saying that this is the remainder and not the rule:\n{aus}"
    );

    // **The array twin:** `_Atomic` qualifies the ELEMENT type, so an array of floats is a
    // float atomic and the walk has to look through the array (`bau.rs::sammle`).
    let feld = "atomic PEGEL : [f32; 4] relaxed;
module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "mit_gleitkommafeld",
        "unit gabbro_probe module laden entladen",
        feld,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
        true,
        true,
    );
    assert_ne!(code, 0, "an array of floats is a float atomic too");
    assert!(aus.contains("floating-point atomic `PEGEL`"), "by name:\n{aus}");

    // **And the same unit with no atomic at all still builds its plan**, so none of the above
    // is measuring a rule that refuses every module.
    let (aus, fehler, code) = kmod_lauf(
        "ohne_atomic",
        "unit gabbro_probe module laden entladen",
        KMOD_EINHEIT,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_eq!(code, 0, "the same unit without the atomic is fine:\n{aus}\n{fehler}");
}

/// **A `module` that binds no kernel primitive is refused, per thing it uses** (server lane,
/// 2026-09-28, TODO section 0e K7).
///
/// SIMON'S RULE is *"API calls are always user-made"*, and until this rule the module RUNTIME
/// was the exception: `laufzeit/kmodul/` called twelve kernel functions no program had
/// declared (`dokumente/OFFEN.md` O35). They are declarations now
/// (`laufzeit/kmodul/bindung.h`) and the program defines them.
///
/// **Why a test and not only the QEMU harness.** The harness measures a `.ko`; a unit whose
/// binding is missing has no `.ko`. What it would get instead is `modpost`'s *"gabbro_kern_…
/// undefined"* -- a linker error, in a `make` log, about a name the user never wrote.
///
/// Each direction is asserted with its POSITIVE twin in the same test, so none of it can pass
/// by refusing everything.
#[test]
fn ein_modul_ohne_bindung_faellt_je_nach_dem_was_es_benutzt() {
    let kmod = "kmod laufzeit/kmodul /lib/modules/x/build\n";

    // 1. The report channel: every module needs it, because every load refusal is words the
    //    program owns (printing is a kernel call).
    let (aus, _, code) = kmod_lauf_roh(
        "ohne_bindung",
        "unit gabbro_probe module laden entladen",
        KMOD_EINHEIT,
        kmod,
        false,
        false,
    );
    assert_ne!(code, 0, "a module that binds nothing is refused");
    assert!(aus.contains("binds no `gabbro_kern_melden`"), "by name:\n{aus}");
    assert!(aus.contains("bibliothek/linux-kmod"), "with the file that supplies it:\n{aus}");

    // 2. An `arena` needs the reservation primitives -- and the same unit without the arena
    //    does not, which is what makes this a rule about what the unit USES.
    let mit_arena = "type Wert = u64 in 0 .. 1000;
arena Knoten capacity 2 .. 4 max 64 of Wert;
module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let nur_melden = "
module bindung::kern {
extern fn gabbro_kern_melden(code : u32, a : u64, b : u64) effects { pure } costs <= 8 ops;
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "arena_ohne_reserve",
        "unit gabbro_probe module laden entladen",
        &format!("{mit_arena}{nur_melden}"),
        kmod,
        false,
        false,
    );
    assert_ne!(code, 0, "an arena without the reservation primitives is refused");
    assert!(aus.contains("binds no `gabbro_kern_reserve`"), "by name:\n{aus}");
    assert!(aus.contains("declares an `arena`"), "and by the reason it needs it:\n{aus}");

    let (aus, fehler, code) = kmod_lauf_roh(
        "arena_mit_reserve",
        "unit gabbro_probe module laden entladen",
        mit_arena,
        kmod,
        true,
        false,
    );
    assert_eq!(code, 0, "the same arena WITH the binding builds its plan:\n{aus}\n{fehler}");

    let (aus, fehler, code) = kmod_lauf_roh(
        "ohne_arena_nur_melden",
        "unit gabbro_probe module laden entladen",
        &format!("{KMOD_EINHEIT}{nur_melden}"),
        kmod,
        false,
        false,
    );
    assert_eq!(
        code, 0,
        "a module with no arena needs no reservation primitive:\n{aus}\n{fehler}"
    );

    // 3. A `masks irqs` lock needs the MASKED pair, and it is a separate pair of names on
    //    purpose: the masking is the binding's promise (`kern_bindung_maskiert`), and the
    //    goal theorem's `KernHaltE` rests on it.
    let mit_sperre = "module treiber::probe {
static mut Takte : u64 = 0;
pub lock TAKT protects { Takte } rank 0 held <= 64 ops masks irqs;
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let ohne_maske = "
module bindung::kern {
extern fn gabbro_kern_melden(code : u32, a : u64, b : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_init(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_kernnummer() -> u32 effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_nimm(s : u64) effects { pure } costs <= 8 ops;
extern fn gabbro_kern_sperre_gib(s : u64) effects { pure } costs <= 8 ops;
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "maske_ohne_paar",
        "unit gabbro_probe module laden entladen",
        &format!("{mit_sperre}{ohne_maske}"),
        kmod,
        false,
        false,
    );
    assert_ne!(code, 0, "a masked lock bound with the PLAIN pair alone is refused");
    assert!(
        aus.contains("binds no `gabbro_kern_sperre_nimm_maskiert`"),
        "by name -- the plain pair is not the masked one:\n{aus}"
    );

    // 4. The SHAPE, not only the name: C has no mangling, so a wrong arity links and then
    //    reads a register nobody set.
    let falsche_stelligkeit = "module treiber::probe {
extern fn gabbro_kern_melden(code : u32) effects { pure } costs <= 8 ops;
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "falsche_stelligkeit",
        "unit gabbro_probe module laden entladen",
        falsche_stelligkeit,
        kmod,
        false,
        false,
    );
    assert_ne!(code, 0, "a binding of the right name and the wrong arity is refused");
    assert!(aus.contains("1 parameter(s) and the runtime calls it with 3"), "with both:\n{aus}");
}

/// **A `module` that declares an `atomic` and binds no memory model is refused** (server
/// lane, 2026-09-28, TODO section 0e K7).
///
/// The memory model is macros -- `READ_ONCE`, `smp_load_acquire`, `try_cmpxchg` -- and leaves
/// no symbol, so the `nm -u` stage of `instrumente/pruefe-kernelmodul.sh` cannot see it at
/// all. It is bound the other way: the runtime's `<stdatomic.h>` refuses `_Atomic` outright
/// and the program names the table (`bibliothek/linux-kmod/stdatomic.h`), which the build
/// copies over the runtime's stub. **This rule is the door before that one** -- without it
/// the refusal is the kernel build's, over an undefined `_Atomic` in a `make` log.
///
/// The positive twin stands in `ein_modul_mit_atomic_wird_gesenkt_und_ein_gleitkomma_atomic_faellt`,
/// which names the header and builds its plan.
#[test]
fn ein_modul_mit_atomic_ohne_speichermodell_faellt() {
    let mit_atomic = "atomic STAND : u32 relaxed;
module treiber::probe {
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, _, code) = kmod_lauf_roh(
        "atomic_ohne_kopf",
        "unit gabbro_probe module laden entladen",
        mit_atomic,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
        true,
        false,
    );
    assert_ne!(code, 0, "an atomic with no memory model named is refused");
    assert!(aus.contains("names no `stdatomic.h`"), "by the file that is missing:\n{aus}");
    assert!(aus.contains("atomic `STAND`"), "and by the declaration:\n{aus}");
}

/// **A program-supplied header belongs to a module and nowhere else**, the same reading the
/// `.c` branch beside it has (server lane, TODO section 0e K7).
#[test]
fn ein_kopf_ausserhalb_eines_moduls_faellt() {
    let (_, fehler, code) = kmod_lauf_roh(
        "kopf_im_objekt",
        "unit gabbro_probe object",
        KMOD_EINHEIT,
        "",
        false,
        true,
    );
    assert_ne!(code, 0, "a `.h` file in an `object` unit is refused");
    assert!(
        fehler.contains("program-supplied header") && fehler.contains("kernel module"),
        "with its reason:\n{fehler}"
    );
}

/// **A `module` unit's `concurrent` roots become KTHREADS, not pthreads** (server lane,
/// 2026-09-28, TODO section 0e K6).
///
/// A root is a root in all three worlds and only the starter differs: a pthread in
/// `laufzeit/start.c`, a core on bare metal, a `kthread` in `laufzeit/kmodul/kmodul.c`. Before
/// this, `TreiberPlan` did not know the unit's art, so a `module` with a `concurrent` set had
/// a hosted pthread driver written beside its `.ko` -- **a file for a world the module is not
/// in**, and one that would have compiled against `pthread.h` in a kernel build if anything
/// had ever picked it up.
///
/// The list travels as `wurzeln.h`, out of the same walk the other two flavours read (`W7`),
/// which is why the dry run names that file and not a driver.
#[test]
fn die_wurzeln_eines_moduls_werden_kthreads_und_kein_hosted_treiber() {
    let mit_wurzeln = "module treiber::probe {
fn eins() effects { pure } costs <= 8 ops { return; }
fn zwei() effects { pure } costs <= 8 ops { return; }
concurrent { eins, zwei };
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
}
";
    let (aus, fehler, code) = kmod_lauf(
        "modul_wurzeln",
        "unit gabbro_probe module laden entladen",
        mit_wurzeln,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_eq!(code, 0, "a module with concurrent roots builds its plan:\n{aus}\n{fehler}");
    assert!(aus.contains("roots [eins, zwei]"), "the roots are seen:\n{aus}");
    assert!(aus.contains("wurzeln.h (one kthread per root)"), "as kthreads:\n{aus}");
    assert!(!aus.contains(".treiber.c"), "and no hosted driver is promised:\n{aus}");
    assert!(!aus.contains(".metall.c"), "and no bare-metal one either:\n{aus}");

    // The twin -- the same two roots in a `program` unit still get the hosted driver -- is
    // `bau.rs::treiberregel_tests::die_art_entscheidet_welcher_treiber`, where the art can be
    // varied without a second manifest.
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

/// **A `module` unit MAY declare a hardware entry without a vector, and before 2026-09-28 it
/// could not** (server lane, TODO section 0e K3).
///
/// A Gabbro unit built as a Linux kernel module is entered from the host kernel's interrupt
/// path -- a timer, a device line -- and that path owns no vector the program could name. The
/// entry therefore says `via irq` and no `vector`, which the bare-metal half of the driver
/// rule refused: *"has no literal vector -- the bare-metal driver cannot name its IDT slot"*.
/// **A refusal whose reason names an artefact nobody asked for is a refusal in the wrong
/// place** -- a module's artefact is a `.ko`, with no IDT and no metal driver. What still
/// holds the declaration is the checker (`H102` over the dispatch's call graph); what binds
/// the stub to the kernel is the program's own C, and no build rule can see that (OFFEN O19).
///
/// The positive twin is below it: the SAME unit as a `program` is still refused, so the metal
/// rule was gated and not deleted.
#[test]
fn ein_modul_mit_eintritt_ohne_vektor_baut() {
    let mit_eintritt = "module treiber::probe {
static mut g : u64 = 0;
lock L protects { g } rank 0 held <= 40 ops masks irqs;
impl fn schlag() effects { writes g, locks L } costs <= 8 ops { locks L { g = 1; } }
impl fn laden() -> u32 effects { pure } costs <= 8 ops { return 0; }
impl fn entladen() -> u32 effects { pure } costs <= 8 ops { return 0; }
entry uhr via irq arch x86_64 {
    regs in  { }
    regs out { }
    preserves { rbx, rbp, r12, r13, r14, r15 }
    clobbers  { rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11 }
    stack uhr_stapel per cpu nested never
    dispatch treiber::probe::schlag;
}
}
";
    let (aus, fehler, code) = kmod_lauf(
        "eintritt_ohne_vektor",
        "unit gabbro_probe module laden entladen",
        mit_eintritt,
        "kmod laufzeit/kmodul /lib/modules/x/build\n",
    );
    assert_eq!(code, 0, "a module's vectorless entry is no longer refused:\n{aus}\n{fehler}");
    assert!(
        !aus.contains("literal vector"),
        "and not for the bare-metal driver's reason either:\n{aus}"
    );

    // **The twin that keeps the metal rule alive.** The same unit as an `object` still meets
    // `metallregel`, because an object unit CAN own a bare-metal driver. Its manifest is
    // written here rather than through `kmod_lauf`, which always names a `.c` body -- and a
    // foreign C body outside a module is refused one rule earlier, which would have made this
    // twin pass for the wrong reason (measured: it did).
    let d = kratz("eintritt_objekt");
    std::fs::write(d.join("u.gab"), mit_eintritt).expect("unit");
    let manifest = format!(
        "compiler cc -std=c11\nout {aus}\nunit gabbro_probe object\n  {q}\n",
        aus = d.join("bau").display(),
        q = d.join("u.gab").display(),
    );
    let mpfad = d.join("manifest");
    std::fs::write(&mpfad, manifest).expect("manifest");
    let (aus, _, code) = lauf(&["build", "--dry-run", mpfad.to_str().expect("utf8")]);
    assert_ne!(code, 0, "an object unit's vectorless entry is still refused:\n{aus}");
    assert!(aus.contains("literal vector"), "for the bare-metal driver's reason:\n{aus}");
}

/// **A HOSTED unit with an `arena` that binds no memory primitive is refused** (server lane,
/// 2026-09-28, TODO section 0e K8) -- the module rule's twin, and deliberately the same shape.
///
/// SIMON DREW THE LINE FOR THE RUNTIMES on 2026-09-28: *"an die Hardware ist OK, OS nicht, das
/// muss selbst gemacht werden."* `laufzeit/arena_dyn.c` was the first hosted file to move: it
/// asked `mmap` for the reservation, `mprotect` for every commit and `sysconf` for the page
/// size, and printed its fail-stops itself. Those six names are declarations now
/// (`laufzeit/bindung.h`) and the PROGRAM defines them --
/// `bibliothek/linux/linux.gab` plus its `.c` is the binding it may take off the shelf.
///
/// **Why a test and not only the instrument.** `instrumente/pruefe-os-bindung.sh` measures
/// what a BUILT binary still pulls out of the OS; a unit whose binding is missing has no
/// binary. What it would get instead is *"undefined reference to `gabbro_os_melden`"* -- a
/// linker error about a name the user never wrote.
///
/// Both directions stand in one test, so neither can pass by refusing everything: the unit
/// WITH the declarations builds, and the one without is refused by name.
#[test]
fn eine_gehostete_einheit_mit_arena_ohne_bindung_faellt() {
    let mit_arena = "module probe::halde {
type Wert = u64 in 0 .. 1000;
arena Puffer capacity 2 .. 4 max 4096 of Wert;
impl fn fuellen() -> u32 effects { writes Puffer } costs <= 1024 ops {
    grow Puffer by 8 else { return 1; };
    let a = alloc Puffer (1) else { return 2; };
    return 0;
}
}
";
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..");
    let bindung_gab = wurzel.join("bibliothek").join("linux").join("linux.gab");
    let bindung_c = wurzel.join("bibliothek").join("linux").join("linux.c");
    let laufzeit = wurzel.join("laufzeit");
    assert!(bindung_gab.is_file(), "the binding this rule points at exists");

    let baue = |marke: &str, mit_bindung: bool| {
        let d = kratz(marke);
        std::fs::write(d.join("u.gab"), mit_arena).expect("unit");
        let mut dateien = format!("  {}\n", d.join("u.gab").display());
        if mit_bindung {
            dateien.push_str(&format!("  {}\n", bindung_gab.display()));
            dateien.push_str(&format!("  {}\n", bindung_c.display()));
        }
        let manifest = format!(
            "compiler cc -std=c11 -I {inc}\nout {aus}\nunit gabbro_probe object\n{dateien}",
            inc = laufzeit.display(),
            aus = d.join("bau").display(),
        );
        let mpfad = d.join("manifest");
        std::fs::write(&mpfad, manifest).expect("manifest");
        let (aus, fehler, code) = lauf(&["build", mpfad.to_str().expect("utf8")]);
        (d, aus, fehler, code)
    };

    let (_, aus, _, code) = baue("arena_ohne_bindung", false);
    assert_ne!(code, 0, "an `arena` without a binding is refused:\n{aus}");
    assert!(aus.contains("binds no `gabbro_os_melden`"), "by name:\n{aus}");
    assert!(aus.contains("bibliothek/linux"), "with the file that supplies it:\n{aus}");
    assert!(aus.contains("`arena`"), "and with what makes the unit need it:\n{aus}");

    // **The positive twin, and it compiles the bodies too.** A rule that only ever refused
    // would be met by a library nobody can build: the `.c` of the binding is an ordinary file
    // of the unit since K8, and the build turns it into an object beside the unit's own.
    let (d, aus, fehler, code) = baue("arena_mit_bindung", true);
    assert_eq!(code, 0, "the same unit with the binding builds:\n{aus}\n{fehler}");
    assert!(
        d.join("bau").join("gabbro_probe.fremd0.o").is_file(),
        "and the binding's bodies are an object of this build:\n{aus}"
    );
}

/// **A binding of the right name and the WRONG SHAPE is refused too** (server lane,
/// 2026-09-28, TODO section 0e K8).
///
/// C has no mangling, so a declaration with the right name and the wrong arity links and then
/// reads a register nobody set. The module rule asks the same three questions
/// (`bau.rs::bindung_pruefe`, which both rules share -- a second copy of this check would be
/// the drift it exists against).
#[test]
fn eine_bindung_mit_falscher_stelligkeit_faellt() {
    let d = kratz("arena_falsche_stelligkeit");
    // `gabbro_os_reserve` takes ONE parameter and answers one. Here it takes two.
    let quelle = "module probe::halde {
type Wert = u64 in 0 .. 1000;
arena Puffer capacity 2 .. 4 max 4096 of Wert;
extern fn gabbro_os_melden(code : u32, a : u64, b : u64) effects { pure } costs <= 512 ops;
extern fn gabbro_os_ende(code : u32) effects { pure } costs <= 512 ops;
extern fn gabbro_os_reserve(bytes : u64, mehr : u64) -> u64 effects { pure } costs <= 512 ops;
extern fn gabbro_os_commit(basis : u64, versatz : u64, bytes : u64) -> u32 effects { pure } costs <= 512 ops;
extern fn gabbro_os_seitengroesse() -> u64 effects { pure } costs <= 512 ops;
impl fn fuellen() -> u32 effects { writes Puffer } costs <= 1024 ops {
    grow Puffer by 8 else { return 1; };
    let a = alloc Puffer (1) else { return 2; };
    return 0;
}
}
";
    std::fs::write(d.join("u.gab"), quelle).expect("unit");
    let manifest = format!(
        "compiler cc -std=c11\nout {aus}\nunit gabbro_probe object\n  {q}\n",
        aus = d.join("bau").display(),
        q = d.join("u.gab").display(),
    );
    let mpfad = d.join("manifest");
    std::fs::write(&mpfad, manifest).expect("manifest");
    let (aus, _, code) = lauf(&["build", mpfad.to_str().expect("utf8")]);
    assert_ne!(code, 0, "a binding of the wrong arity is refused:\n{aus}");
    assert!(
        aus.contains("gabbro_os_reserve") && aus.contains("parameter"),
        "by name and by shape:\n{aus}"
    );
    assert!(aus.contains("laufzeit/bindung.h"), "against the header it is held to:\n{aus}");
}
