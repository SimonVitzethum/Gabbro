//! **The two-unit program -- `OB5`, and the criterion is a CHANGE and not a number.**
//!
//! Until 2026-09-01 `gabbro build` printed `0 computed edge(s)` over its only example, and
//! that was an honest zero: the graph was computed, topologically sorted, and a cycle refused
//! by name -- *there was simply never an edge.* Every statement about modularity in this tree
//! -- effect derivation across the call graph, assumption import, profiles -- was therefore
//! measured on a case nobody had built.
//!
//! What is held here is the case:
//!
//! ```text
//! rechenwerk (object)   prog-vorrat.gab + prog-werk.gab  ->  rechenwerk.o
//!      ^                                                     rechenwerk.gabi
//!      | use werk::ablegen, use werk::holen, use vorrat::Regal
//! haupt (program)       prog-haupt.gab                   ->  haupt.o, then the LINKER
//! ```
//!
//! **The result the program computes is `137`, and it is `100 + 37`.** The `100` is a `5000`
//! that a PRIVATE helper of the other unit capped; the `37` went through untouched. *A number
//! that both halves of the boundary had to be right to produce.*
//!
//! > **Why the result travels as an exit status and not as printed text.** A Gabbro program
//! > cannot print: `printf`, `puts` and `putchar` all stand in the table of `cnamen.rs`, and
//! > `N041` refuses an `extern fn` on any of them -- *the guard is right, and it has no
//! > exemption for a deliberate foreign binding.* So what prints stands beside the program:
//! > `der_treiber_druckt_und_wird_verglichen` links a C driver against the very
//! > `rechenwerk.o` this build wrote, the same shape `pruefe-emission.sh` Stufe 10 uses.
//! > **The driver is the instrument, not part of the program.**

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

/// **The tests of this file share one output directory and one source tree.**
///
/// `eine_aenderung_im_privaten_rumpf_baut_das_programm_neu` writes into `prog-werk.gab` and
/// puts it back. Whoever ran beside it would measure a mixture -- *the same class as the
/// `rsync` into a directory a mutation run was working in.*
static SPERRE: Mutex<()> = Mutex::new(());

const MANIFEST: &str = "messung/einheit-proben/zwei-einheiten.bau";
const WERK: &str = "messung/einheit-proben/prog-werk.gab";
const AUS: &str = "target/bau-zwei";

fn wurzel() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn lauf(argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(wurzel())
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

/// Builds the two units and hands back what the build said.
fn baue() -> (String, String, i32) {
    lauf(&["build", MANIFEST])
}

/// **THE test: two units, one linker, and the program runs.**
///
/// Three statements in one run, and none of them can be made over a single unit:
/// the build computes an edge, it carries it, and the linked artefact answers `137`.
#[test]
fn das_zweieinheitenprogramm_uebersetzt_und_laeuft() {
    let _sperre = SPERRE.lock().expect("lock");
    let (aus, fehler, code) = lauf(&["build", "--dry-run", MANIFEST]);
    assert_eq!(code, 0, "the manifest reads:\n{aus}\n{fehler}");
    assert!(
        aus.contains("1 computed edge(s) between units") && aus.contains("haupt -> rechenwerk"),
        "the edge is COMPUTED out of the `use` lines and named:\n{aus}"
    );

    let (aus, fehler, code) = baue();
    assert_eq!(code, 0, "both units build:\n{aus}\n{fehler}");
    for e in ["rechenwerk", "haupt"] {
        assert!(
            aus.contains(&format!("built    {e}")) || aus.contains(&format!("current  {e}")),
            "unit `{e}` is named either way:\n{aus}"
        );
    }

    let programm = wurzel().join(AUS).join("haupt");
    assert!(programm.exists(), "the LINKED program is there, not just an object");
    let ergebnis = Command::new(&programm).output().expect("the program runs");
    assert_eq!(
        ergebnis.status.code(),
        Some(137),
        "the handwriting is 137 = 100 + 37: the 5000 was capped by the OTHER unit's private \
         helper, the 37 went through. stdout: {:?}",
        String::from_utf8_lossy(&ergebnis.stdout)
    );
}

/// **Counter-direction: without the edge the program does not build.**
///
/// The same file, a manifest that does not name the unit it rests on. *Without this the
/// sentence "the program translates" would only say that two files happen to fit.*
#[test]
fn ohne_die_kante_faellt_das_programm() {
    let (aus, fehler, code) = lauf(&["build", "messung/einheit-proben/gift-programm-ohne-kante.bau"]);
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(aus.contains("REFUSED  haupt"), "the unit is named:\n{aus}");
    assert!(
        aus.contains("[K003]") && aus.contains("`ablegen` is not declared here"),
        "and it falls at the call across the boundary, by name:\n{aus}"
    );
    assert!(
        aus.contains("messung/einheit-proben/prog-haupt.gab:"),
        "with the site in the file:\n{aus}"
    );
}

/// **Counter-direction: a `program` over two files that carry no `main`.**
///
/// > **This test measured the LINKER until 2026-09-01, and `B001` took the case away from
/// > it.** The refusal used to read *"the linker refused 1 object(s)"* -- `ld`'s words, in
/// > the system's language, three tools after the mistake. It now falls at `B001`, in
/// > Gabbro's words and *before the C is written*.
///
/// The statement the old form carried -- **the binder runs at all, and it can say no** -- did
/// not move with it, and a rule that moves a refusal upstream also takes away the probe that
/// lived on it. It is rebuilt in `eintritt.rs::der_binder_laeuft_und_kann_absagen`, on an
/// `extern fn` nothing defines. *Without that second file this change would have traded a
/// measurement for a rule and called it progress.*
#[test]
fn ein_programm_ohne_main_faellt_an_b001() {
    let (aus, fehler, code) = lauf(&["build", "messung/einheit-proben/gift-programm-ohne-main.bau"]);
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(
        aus.contains("REFUSED  ohnemain") && aus.contains("[B001]"),
        "and it is GABBRO that refuses, by name:\n{aus}"
    );
    assert!(
        !aus.contains("the linker refused"),
        "one tool earlier than it used to -- the linker is never reached:\n{aus}"
    );
}

/// **`pub` decides what binds outside, and `nm` asks the LINKER.**
///
/// This is the statement no single translation unit can make: a missing `static` does not
/// show up inside one unit at all. Measured over the object this build wrote.
#[test]
fn was_pub_nicht_traegt_bindet_nicht() {
    let _sperre = SPERRE.lock().expect("lock");
    let (aus, fehler, code) = baue();
    assert_eq!(code, 0, "the build runs first:\n{aus}\n{fehler}");

    let objekt = wurzel().join(AUS).join("rechenwerk.o");
    let nm = Command::new("nm")
        .args(["-g", "--defined-only"])
        .arg(&objekt)
        .output()
        .expect("nm runs");
    let text = String::from_utf8_lossy(&nm.stdout).into_owned();
    let mut aussen: Vec<&str> = text
        .lines()
        .filter_map(|z| {
            let felder: Vec<&str> = z.split_whitespace().collect();
            (felder.len() == 3 && felder[1] == "T").then_some(felder[2])
        })
        .collect();
    aussen.sort_unstable();
    assert_eq!(
        aussen,
        ["ablegen", "holen"],
        "exactly the two `pub` bodies bind outside -- `deckeln` does not, and the table's \
         storage does not either:\n{text}"
    );
    // **And the interface says the same thing**, so the two registers agree.
    let gabi = std::fs::read_to_string(wurzel().join(AUS).join("rechenwerk.gabi"))
        .expect("the build wrote an interface");
    assert!(!gabi.contains("deckeln"), "the private helper is in no interface:\n{gabi}");
}

/// **A change in a dependency's PRIVATE body rebuilds the program.**
///
/// *This is what the edge cost, and it is the trap the whole incremental section stands
/// against.* The `.gabi` does not move when a private body changes -- the object does. Without
/// the upstream fingerprints inside the dependent's own, `haupt` would have been reported
/// current over a library it no longer contains.
#[test]
fn eine_aenderung_im_privaten_rumpf_baut_das_programm_neu() {
    let _sperre = SPERRE.lock().expect("lock");
    let werk = wurzel().join(WERK);
    let vorher = std::fs::read(&werk).expect("source readable");

    // Build once, then once more: the second run must be current, or the assertion below
    // proves nothing (a build that always rebuilds would pass it for the wrong reason).
    let (_, _, code) = baue();
    assert_eq!(code, 0, "the preparing build runs");
    let (aus, _, _) = baue();
    assert!(
        aus.contains("current  haupt"),
        "unchanged, the program is current -- otherwise the next assertion is empty:\n{aus}"
    );
    let gabi_vorher = std::fs::read_to_string(wurzel().join(AUS).join("rechenwerk.gabi")).unwrap();

    let geaendert = String::from_utf8(vorher.clone())
        .expect("utf-8")
        .replace("        return 100;", "        return 99;");
    assert_ne!(geaendert.as_bytes(), &vorher[..], "the change bites");
    std::fs::write(&werk, &geaendert).expect("source writable");
    let (aus, fehler, code) = baue();
    let gabi_nachher = std::fs::read_to_string(wurzel().join(AUS).join("rechenwerk.gabi")).unwrap();
    let ergebnis = Command::new(wurzel().join(AUS).join("haupt")).output();
    // Put the source back BEFORE asserting -- a failing assertion must not leave the tree
    // changed. *A test that poisons the corpus when it falls poisons the next run too.*
    std::fs::write(&werk, &vorher).expect("source restorable");

    assert_eq!(code, 0, "it builds again:\n{aus}\n{fehler}");
    assert_eq!(
        gabi_vorher, gabi_nachher,
        "the INTERFACE did not move -- a private body is not part of it"
    );
    assert!(
        aus.contains("built    rechenwerk") && aus.contains("built    haupt"),
        "and the program was rebuilt anyway, though nothing it can see changed:\n{aus}"
    );
    assert_eq!(
        ergebnis.expect("the program runs").status.code(),
        Some(136),
        "and it computes the new number, not the old one"
    );

    // And back to green, so the directory is left the way it was found.
    let (aus, _, code) = baue();
    assert_eq!(code, 0, "the tree is back:\n{aus}");
}

/// **The result, PRINTED and compared against a handwriting.**
///
/// A C driver over the very `rechenwerk.o` this build wrote -- the shape of
/// `pruefe-emission.sh` Stufe 10, and the only way to get printed output out of a Gabbro
/// library: `N041` refuses every libc printing name (see the module comment). *The driver is
/// the instrument; the object under it is the build's.*
///
/// **With a speaking probe**, because "6. Ergebnis" says nothing about the private helper
/// otherwise: it could be dead and the number still right.
#[test]
fn der_treiber_druckt_und_wird_verglichen() {
    let _sperre = SPERRE.lock().expect("lock");
    let (aus, fehler, code) = baue();
    assert_eq!(code, 0, "the build runs first:\n{aus}\n{fehler}");
    let arb = wurzel().join("target/bau-zwei-treiber");
    std::fs::create_dir_all(&arb).expect("work directory");
    let treiber = arb.join("treiber.c");
    std::fs::write(&treiber, TREIBER).expect("driver writable");

    let objekt = wurzel().join(AUS).join("rechenwerk.o");
    let programm = arb.join("probe");
    uebersetze(&[treiber.as_path(), objekt.as_path()], &programm);
    let ist = String::from_utf8_lossy(&Command::new(&programm).output().expect("runs").stdout)
        .trim()
        .to_string();
    assert_eq!(
        ist, "100 37 100",
        "the handwriting: 5000 capped to 100, 37 through, 100 exactly at the bound"
    );

    // **Speaking probe: the private helper really computes.** The generated C is poisoned,
    // not the source -- the source is the corpus, and a probe that edits it is a probe that
    // can leave it edited.
    let c = std::fs::read_to_string(wurzel().join(AUS).join("rechenwerk.c")).expect("C readable");
    let gift = c.replace("        return 100;", "        return w;");
    assert_ne!(gift, c, "the poison bites");
    let gift_c = arb.join("rechenwerk-gift.c");
    std::fs::write(&gift_c, &gift).expect("writable");
    let gift_programm = arb.join("probe-gift");
    uebersetze(&[treiber.as_path(), gift_c.as_path()], &gift_programm);
    let ist_gift =
        String::from_utf8_lossy(&Command::new(&gift_programm).output().expect("runs").stdout)
            .trim()
            .to_string();
    assert_ne!(
        ist_gift, "100 37 100",
        "a spoiled private helper must change the printed result -- otherwise the comparison \
         above measures nothing about it"
    );
    assert_eq!(ist_gift, "5000 37 100", "and it changes it in exactly the one place");
}

// =========================================================================================
// **The two measurements that were unaskable until the boundary existed.**
//
// `OB5` blocks them by name: effect derivation across a module boundary, and assumption
// import. Both were "measured" before at a case nobody had built -- which is not a
// measurement, it is a guess with a number beside it.

/// **The derivation DOES see the callee in the other unit** -- and the finding `OB6` could
/// not find comes with it.
///
/// Two directions in one test, because only the pair says anything:
///
/// * a caller whose `effects` list is right comes out `identical` at `abi --vergleich`
///   -- and the read and the write it names can ONLY come from the two callees, since its
///   own body touches no place at all;
/// * a caller that drops the `writes` falls at **`E008`** -- *because it is checked, not
///   because it is silent.* Without the bridge the same file falls at `K003`, at the missing
///   resolution, and about the omission nobody says a word.
#[test]
fn die_effektableitung_sieht_ueber_die_grenze() {
    let _sperre = SPERRE.lock().expect("lock");
    let (aus, fehler, code) = baue();
    assert_eq!(code, 0, "the build writes the interface first:\n{aus}\n{fehler}");
    let gabi = format!("{AUS}/rechenwerk.gabi");

    let (aus, fehler, code) = lauf(&[
        "abi",
        "--vergleich",
        "--with",
        &gabi,
        "messung/einheit-proben/prog-haupt.gab",
    ]);
    assert_eq!(code, 0, "the comparison runs across the boundary:\n{aus}\n{fehler}");
    assert!(
        aus.contains("identical      haupt::main"),
        "the computed hull equals the written list -- and the two effects in it were derived \
         THROUGH the `.gabi`, because `main` touches no place itself:\n{aus}"
    );
    assert!(
        aus.contains("units read  1") && !aus.contains("NO FUNCTION LOOKED AT"),
        "and the population is not empty -- a zero here would be no measurement (W1):\n{aus}"
    );

    // **Without the bridge the same command measures nothing, and says so.**
    let (aus, _, _) = lauf(&["abi", "--vergleich", "messung/einheit-proben/prog-haupt.gab"]);
    assert!(
        aus.contains("units REJECTED") && aus.contains("NO FUNCTION LOOKED AT"),
        "alone the file is rejected, and the command refuses to call that a result:\n{aus}"
    );

    // **Counter-direction: an effect performed across the boundary and not declared falls.**
    let gift = "messung/einheit-proben/gift-wirkung-fehlt-ueber-die-grenze.gab";
    let (aus, _, code) = lauf(&["pruefe", "--with", &gabi, gift]);
    assert_eq!(code, 1, "refused:\n{aus}");
    assert!(
        aus.contains("[E008]") && aus.contains("calls something with `writes Regal.slots`"),
        "at the effect, by name:\n{aus}"
    );
    // **And the site is in the FILE.** Until 2026-09-01 this path rendered against the joined
    // text and printed a line number of the concatenation beside the file's name.
    assert!(
        aus.contains(&format!("{gift}:17:13")),
        "line 17 of a file of 28 lines, not a line of the preamble plus the file:\n{aus}"
    );

    let (aus, _, code) = lauf(&["pruefe", gift]);
    assert_eq!(code, 1, "alone it also falls -- but at something else:\n{aus}");
    assert!(
        aus.contains("[K003]") && !aus.contains("[E008]"),
        "at the missing resolution, and NOT at the missing effect: the omission is invisible \
         without the bridge:\n{aus}"
    );
}

/// **An `assume` does NOT travel across the unit boundary -- measured, and it is a decision.**
///
/// `abi.rs` says so in its own head: a library that ships its `assume` lines forces its
/// machine on every importer, and an override at the import is not a replacement but a proof
/// obligation («ABI4»). *Until that obligation is counted, it is more honest not to carry the
/// assumption over at all.*
///
/// What this test holds is the CONSEQUENCE, so that it is written down rather than deduced:
/// the library is proved under one assumption, the program is proved under none, and **at the
/// boundary nothing says that an assumption was dropped.** That is `OB8`'s "platform
/// assumptions per program NULL" seen from the other side -- there is now a place where an
/// assumption COULD stand once, and it does not carry.
#[test]
fn eine_annahme_traegt_nicht_ueber_die_grenze() {
    let _sperre = SPERRE.lock().expect("lock");
    let (aus, fehler, code) = baue();
    assert_eq!(code, 0, "the build runs:\n{aus}\n{fehler}");

    let (aus, _, code) = lauf(&["annahmen", "messung/einheit-proben/prog-vorrat.gab"]);
    assert_eq!(code, 0, "the library's manifest:\n{aus}");
    assert!(aus.contains("-- 1 Annahmen"), "the library has exactly one:\n{aus}");
    assert!(aus.contains("fach_zahl_passt_in_den_index"), "by name:\n{aus}");

    let gabi = std::fs::read_to_string(wurzel().join(AUS).join("rechenwerk.gabi"))
        .expect("the build wrote an interface");
    assert!(
        !gabi.contains("assume") && !gabi.contains("fach_zahl_passt_in_den_index"),
        "and the interface carries neither the word nor the name:\n{gabi}"
    );

    let (aus, _, code) = lauf(&["annahmen", "messung/einheit-proben/prog-haupt.gab"]);
    assert_eq!(code, 0, "the program's manifest:\n{aus}");
    assert!(
        aus.contains("-- 0 Annahmen"),
        "the program that USES the library is proved under none of its assumptions -- and \
         nothing at the boundary says one was dropped:\n{aus}"
    );

    // **The counter-direction: the program does not fall for it either.** *Silence in both
    // directions is the whole finding* -- there is no refusal, no hint and no line in a
    // certificate that names the loss.
    let (aus, _, code) = lauf(&[
        "pruefe",
        "--with",
        &format!("{AUS}/rechenwerk.gabi"),
        "messung/einheit-proben/prog-haupt.gab",
    ]);
    assert_eq!(code, 0, "it checks clean across the boundary:\n{aus}");
    assert!(
        !aus.to_lowercase().contains("assum"),
        "and not one word about the assumption it was NOT proved under:\n{aus}"
    );
}

/// `cc` with the manifest's own flags. **A driver built more leniently than the unit under it
/// would hide the very warnings the manifest asked for.**
fn uebersetze(eingaben: &[&Path], ziel: &Path) {
    let aus = Command::new("cc")
        .args(["-std=c11", "-O0", "-Wall", "-Wextra", "-Werror", "-o"])
        .arg(ziel)
        .args(eingaben)
        .output()
        .expect("cc runs");
    assert!(
        aus.status.success(),
        "cc took it:\n{}",
        String::from_utf8_lossy(&aus.stderr)
    );
}

/// **The driver declares the two `pub` names by hand and includes nothing.**
///
/// That is deliberate: a `#include` of a generated header would test the header. What is
/// tested here is the ABI -- the plain C one, prototype and outer binding name and nothing
/// else. *A library one can only use with its own compiler is no library.*
const TREIBER: &str = r#"#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
bool ablegen(uint32_t i, int32_t w);
int32_t holen(uint32_t i);
int main(void) {
    ablegen(2, 5000);
    ablegen(5, 37);
    ablegen(7, 100);
    printf("%d %d %d\n", holen(2), holen(5), holen(7));
    return 0;
}
"#;
