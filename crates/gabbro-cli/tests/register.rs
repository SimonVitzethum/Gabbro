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

/// **A reader that stops reading must not look like a crash.**
///
/// `gabbro pruefe f.gab | head` ended with **`rc=101` and a panic message** until
/// 2026-08-31: Rust ignores `SIGPIPE`, so the write into the closed pipe fails with `EPIPE`
/// and `println!` turns that into a panic. *Measured before the repair: 101 through a pipe,
/// 0 without one.*
///
/// The WHOLE poison corpus is passed on purpose. `gabbro paesse` prints 13 891 bytes and
/// fits inside a 64 KiB pipe buffer -- the child could finish writing before `head` ever
/// closes the read end, and the probe would pass without having tested anything. *A probe
/// whose subject fits in the buffer measures the buffer, not the rule.*
fn durch_bash(skript: &str) -> (String, String) {
    let aus = std::process::Command::new("bash")
        .arg("-c")
        .arg(skript)
        .arg("bash")
        .arg(env!("CARGO_BIN_EXE_gabbro"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .output()
        .expect("bash runs");
    (
        String::from_utf8_lossy(&aus.stdout).trim().to_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
    )
}

#[test]
fn geschlossene_pipe_ist_kein_absturz() {
    let (rc, err) = durch_bash(
        r#""$1" pruefe beispiele/gift/*.gab | head -1 >/dev/null; echo "${PIPESTATUS[0]}""#,
    );
    assert_eq!(rc, "0", "a closed pipe must not end in rc=101\nstderr:\n{err}");
    assert!(
        !err.contains("panicked"),
        "a closed pipe must not print a panic:\n{err}"
    );
}

/// **And the repair must not swallow the VERDICT.** A hook that turned every panic into a
/// quiet 0 would hide exactly what this checker exists to say.
///
/// This one pipes into a reader that reads EVERYTHING (`cat > /dev/null`), so no `EPIPE`
/// ever arises -- *if it ended in `head` as well, `cat` would take the broken pipe and hand
/// it straight on, and the probe would measure the repair instead of the verdict.*
#[test]
fn die_pipe_verschluckt_das_urteil_nicht() {
    let (rc, err) = durch_bash(
        r#""$1" pruefe beispiele/gift/104-ensures-index-tippfehler.gab | cat >/dev/null; echo "${PIPESTATUS[0]}""#,
    );
    assert_eq!(rc, "1", "a finding stays a finding through a pipe\nstderr:\n{err}");
}
