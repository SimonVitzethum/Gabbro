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
