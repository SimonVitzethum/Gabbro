//! **The "not checked in this run" register: short by default, full on demand.**
//!
//! Measured 2026-08-25 on `beispiele/16-by-ops-am-feld.gab`, a CLEAN file of 39 lines: the
//! run printed **1 142 words, 1 122 of them (98.2 %) this register** -- and twenty the
//! result. *A disclosure that drowns the finding by a factor of 56 is not read the twentieth
//! time.*
//!
//! **And it cannot differ between two runs:** `ungeprueft()` reads `passliste()`, a static
//! list inside the binary. So the wording stands behind `--paesse`, and an ordinary run
//! carries the count, every pass by NAME, and a fingerprint.
//!
//! > **This is the first test in this folder that runs the COMMAND LINE.** Until today not
//! > one checked what `gabbro` prints -- the output was covered only indirectly, through
//! > `pruefe-emission.sh`, and that holds exit codes against C, not text against a promise.

use std::process::Command;

fn lauf(argumente: &[&str]) -> String {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .output()
        .expect("gabbro runs");
    String::from_utf8_lossy(&aus.stdout).into_owned()
}

const DATEI: &str = "beispiele/16-by-ops-am-feld.gab";

/// The long line a FULL register is recognised by -- it stands in the entry for pass 2 and
/// in no summary.
const LANGE_ZEILE: &str = "CARRIED -- the rest is NAMED: the K condition is built";

#[test]
fn der_regellauf_fasst_das_register_zusammen() {
    let aus = lauf(&["pruefe", DATEI]);
    assert!(
        aus.contains("Not checked in this run:"),
        "the disclosure itself stays -- it moves, it does not fall away:\n{aus}"
    );
    assert!(
        aus.contains("9 passes"),
        "the NUMBER of unchecked passes is there:\n{aus}"
    );
    assert!(
        aus.contains("register "),
        "the fingerprint makes a change of wording visible:\n{aus}"
    );
    assert!(
        !aus.contains(LANGE_ZEILE),
        "the full wording is NOT in an ordinary run:\n{aus}"
    );
}

#[test]
fn jeder_ungeprueft_pass_wird_im_regellauf_beim_namen_genannt() {
    // **Counting is not enough.** A summary that gives only a number turns nine NAMED gaps
    // into one anonymous one -- *and then the shortening is a loss and not a move.*
    let aus = lauf(&["pruefe", DATEI]);
    for pass in gabbro_check::ungeprueft() {
        assert!(
            aus.contains(pass.name),
            "pass `{}` is missing from the summary:\n{aus}",
            pass.name
        );
    }
}

#[test]
fn paesse_druckt_das_volle_register() {
    let aus = lauf(&["pruefe", "--paesse", DATEI]);
    assert!(
        aus.contains(LANGE_ZEILE),
        "`--paesse` gives the wording, unchanged:\n{aus}"
    );
}

#[test]
fn die_kuerzung_ruehrt_das_ergebnis_nicht_an() {
    // What stands at the top is the reason for the call. It reads the same in both forms.
    let kurz = lauf(&["pruefe", DATEI]);
    let voll = lauf(&["pruefe", "--paesse", DATEI]);
    let kopf = "beispiele/16-by-ops-am-feld.gab: 6 items, 0 errors, 0 hints";
    assert!(kurz.contains(kopf), "short:\n{kurz}");
    assert!(voll.contains(kopf), "full:\n{voll}");
}
