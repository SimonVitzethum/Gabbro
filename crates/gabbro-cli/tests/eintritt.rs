//! **`B001` -- a `program` names exactly one entry, and an `object` names none.**
//!
//! *The finding that shaped this file is that the entry itself was never missing.* On
//! 2026-09-01 the plan said *"`int main` in the emitted C over 102 units: 0"* and *"`pub fn
//! haupt() -> i32` needs a hand-written C driver to run"*. Measured the same day, both halves
//! are stale: `messung/einheit-proben/prog-haupt.gab` declares `pub impl fn main()`, the
//! build links it, and `./target/bau-zwei/haupt` answers `137`. **A hosted Gabbro program has
//! run out of a manifest alone since `56f2d7d`.**
//!
//! What it ran on was an accident, and that is the whole of `B001`: `emit.rs` does not
//! mangle, so a function a writer happens to call `main` becomes C's `main`. Nothing held
//! that a `unit ... program` has one, and nothing held that a `unit ... object` has none.
//!
//! **Who refused what BEFORE this rule, measured case by case:**
//!
//! | case | refused by | in whose words |
//! |---|---|---|
//! | one `pub fn main()` in a `program` | nobody -- it builds and runs | -- |
//! | two `pub fn main` in one unit | **`N039`** | Gabbro, by name |
//! | zero `main` in a `program` | `ld` | *"undefined reference to `main`"*, system locale |
//! | a private `fn main` | `cc -Werror=main` | *"normally a non-static function"* |
//! | a wrong return type or arity | `cc -Werror=main` | C's |
//! | a `pub` `main` beside a private one | **nobody** | -- |
//! | an `object` that declares `main` | `ld`, at the link of a *later* program | -- |
//!
//! The last two rows are findings and not bookkeeping: `N039` asks *"do two EXPORTED items
//! carry one C name"*, which is not the question *"how many entries does this program have"*.
//!
//! **It cost no word.** `main` is an identifier, not a keyword; `entry` is untouched and
//! stays what it was -- a hardware-entered interrupt stub with a register footprint, a vector
//! and a dispatch, emitting a prototype and never a body.

use std::path::PathBuf;
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn baue(manifest: &str) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(["build", manifest])
        .current_dir(wurzel())
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

/// **THE test: a `.gab` file plus a manifest, and the binary runs -- no hand-written C.**
///
/// *The acceptance criterion of `B1` is a change and not a number.* `41` and not `0`, so a
/// run that did nothing is distinguishable from a run that worked.
#[test]
fn ein_programm_laeuft_ohne_handgeschriebenes_c() {
    let (aus, fehler, code) = baue("messung/proben/eintritt.bau");
    assert_eq!(code, 0, "the build runs:\n{aus}\n{fehler}");
    // **`built` OR `current`** -- the build is incremental by content, and a second run over
    // an unchanged source reports the artefact it already has. *Asserting `built` alone would
    // make this test pass only on the first run of the day.*
    assert!(
        aus.contains("built    eintritt") || aus.contains("current  eintritt"),
        "the unit came through:\n{aus}"
    );
    assert!(aus.contains("0 refused"), "and nothing was refused:\n{aus}");

    let binaer = wurzel().join("target/bau-eintritt/eintritt");
    assert!(binaer.exists(), "the linker wrote a binary: {}", binaer.display());
    let lauf = Command::new(&binaer).output().expect("the program runs");
    assert_eq!(lauf.status.code(), Some(41), "and it answers 41");

    // **And the C it ran on carries the entry as a DEFINITION.** Without this the test above
    // would pass over a binary whose `main` came from anywhere.
    let c = std::fs::read_to_string(wurzel().join("target/bau-eintritt/eintritt.c"))
        .expect("the generated C is on disk");
    assert!(c.contains("main(void) {"), "a definition and not just a prototype:\n{c}");
    assert!(!c.contains("static int32_t main"), "and it is exported:\n{c}");
}

/// **Counter-direction: a `program` with NO entry, and the refusal is Gabbro's.**
///
/// This case fell before -- at `ld`, in the system's language, three tools downstream. What
/// changed is who says it and when: *before the C is written.*
#[test]
fn ein_programm_ohne_eintritt_faellt_an_b001() {
    // **The output directory is cleared first, or the last assertion measures history.** A
    // `.c` this build did not write looks exactly like one it did.
    let _ = std::fs::remove_dir_all(wurzel().join("target/bau-ohne-main"));
    let (aus, fehler, code) = baue("messung/einheit-proben/gift-programm-ohne-main.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(aus.contains("REFUSED  ohnemain"), "the unit is named:\n{aus}");
    assert!(aus.contains("[B001]"), "and the rule is named:\n{aus}");
    assert!(aus.contains("declares no `main`"), "and it says WHAT is missing:\n{aus}");
    // **The refusal stands BEFORE the C exists.** A rule that ran afterwards would say the
    // same thing the linker says, only in Gabbro's words -- a translation and not a pass.
    assert!(
        !aus.contains("the linker refused"),
        "and it is no longer the linker that answers:\n{aus}"
    );
    assert!(
        !wurzel().join("target/bau-ohne-main/ohnemain.c").exists(),
        "and no C was written -- the rule runs in front of the emitter"
    );
}

/// **Counter-direction: the entry is there and PRIVATE.**
///
/// It lowers to `static int32_t main(void)` -- the linker never sees it. `cc -Werror=main`
/// catches it one tool later, in C's words; the file itself checks clean, because a private
/// function is nothing Gabbro objects to.
#[test]
fn ein_privater_eintritt_faellt() {
    let (aus, fehler, code) = baue("messung/proben/gift-eintritt-privat.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(aus.contains("[B001]") && aus.contains("is not `pub`"), "by name:\n{aus}");
    assert!(
        aus.contains("probe::eintritt::privat::main"),
        "and the site is named, module and all:\n{aus}"
    );
}

/// **Counter-direction: TWO entries -- and `N039` does not see this pair.**
///
/// One is `pub`, one is not, so there is no second exported symbol and `N039` stays silent.
/// *That is the gap the count closes*: "exactly one entry" is a different question from "no
/// two exported names".
#[test]
fn zwei_eintritte_fallen_wo_n039_schweigt() {
    let (aus, fehler, code) = baue("messung/proben/gift-eintritt-zwei.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(aus.contains("[B001]") && aus.contains("2 times"), "counted:\n{aus}");
    assert!(
        aus.contains("probe::zwei::a::main") && aus.contains("probe::zwei::b::main"),
        "and BOTH sites are named -- a count without the sites is not a refusal:\n{aus}"
    );
    assert!(!aus.contains("[N039]"), "and `N039` really is silent here:\n{aus}");
}

/// **Counter-direction: the entry takes an argument.**
///
/// C allows `int main(void)` and `int main(int, char **)`. Gabbro has no `char`, so the
/// second is not writable -- the same seam `beispiele/63` names for `puts`.
#[test]
fn ein_eintritt_mit_parameter_faellt() {
    let (aus, fehler, code) = baue("messung/proben/gift-eintritt-parameter.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(
        aus.contains("[B001]") && aus.contains("takes 1 parameter(s)"),
        "by name and with the count:\n{aus}"
    );
}

/// **Counter-direction over the OTHER half of the rule: an `object` that declares `main`.**
///
/// The same source as `eintritt.bau`, one word different in the manifest. *This is the one
/// question a single file cannot answer* -- and it is the only place in the build where
/// `object` and `program` differ before the linker.
#[test]
fn eine_bibliothek_mit_eintritt_faellt() {
    let (aus, fehler, code) = baue("messung/proben/gift-eintritt-in-bibliothek.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(
        aus.contains("[B001]") && aus.contains("this `object` declares"),
        "by name:\n{aus}"
    );
    assert!(
        aus.contains("collides with the `program` that links it"),
        "and it says why, not just that:\n{aus}"
    );
}

/// **The speaking probe for the LINK step, rebuilt.**
///
/// `ein_programm_ohne_main_faellt_am_binder` used to be the only proof that the binder runs
/// at all -- *a `program` that in truth wrote nothing but an object would look the same from
/// outside.* `B001` refuses that case one tool earlier, and **a rule that moves a refusal
/// upstream also takes away the probe that lived on it.**
///
/// So the probe stands on a case `B001` does not cover: an `extern fn` nothing defines. It
/// checks clean, `cc -c` accepts it, and `ld` says no.
#[test]
fn der_binder_laeuft_und_kann_absagen() {
    let (aus, fehler, code) = baue("messung/proben/gift-eintritt-ungebunden.bau");
    assert_eq!(code, 1, "refused:\n{aus}\n{fehler}");
    assert!(
        aus.contains("REFUSED  ungebunden") && aus.contains("the linker refused"),
        "and it is the LINKER, not `B001` and not `cc -c`:\n{aus}"
    );
    assert!(!aus.contains("[B001]"), "`B001` passed this one:\n{aus}");
    assert!(
        fehler.contains("nirgendwo_definiert"),
        "and the undefined name reaches the writer:\n{fehler}"
    );
}

/// **`--dry-run` carries `B001` too, and that is what a dry run is for.**
///
/// The entry is read out of the sources -- no C, no compiler, no linker -- so a plan that
/// could not link says so before anything is written. *Without this the cheapest command in
/// the build would be the one that hides the most.*
#[test]
fn der_trockenlauf_traegt_die_regel() {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(["build", "--dry-run", "messung/einheit-proben/gift-programm-ohne-main.bau"])
        .current_dir(wurzel())
        .output()
        .expect("gabbro runs");
    let text = String::from_utf8_lossy(&aus.stdout).into_owned();
    assert_eq!(aus.status.code(), Some(1), "the dry run refuses too:\n{text}");
    assert!(text.contains("[B001]"), "by name:\n{text}");
    assert!(
        text.contains("1 refused"),
        "and the coverage line counts it -- a finding that misses the tally is half a \
         finding:\n{text}"
    );
}
