//! **`gabbro prove` may say GREEN only when Lean checked something.**
//!
//! Found by the server lane on 2026-09-29 (`~/gabbro-netz`, `firewall/regeln.gab`): the
//! measurement ran `~/.elan/bin/lean` -- elan's proxy -- from the caller's directory, where no
//! `lean-toolchain` file stands. The proxy printed `error: no default toolchain configured` and
//! exited 1. That line carries no `file:line:col:`, so the error parser saw nothing, the `sorry`
//! parser saw nothing, and the unit was reported
//!
//! > `GREEN  DutyRegeln -- 15 statement(s), all closed by the generator; nothing owed`
//!
//! in three seconds -- where the real run takes six minutes and leaves nine duties owed. **And
//! `emit --proved` goes through the same measurement**, so it would have written C for a unit
//! that owed nine proofs.
//!
//! The three cases below replace `lean` and `lake` by small scripts (`$LEANBIN`, `$LAKE`), so
//! they need no Lean installation and run in milliseconds:
//!
//! | `lean` does | the verdict must be |
//! |---|---|
//! | prints an error WITHOUT a position and exits 1 (the case that happened) | SETUP, exit 3 -- never GREEN |
//! | exits 0 and writes no `.olean` (it checked nothing) | SETUP, exit 3 |
//! | exits 0 and writes the `.olean` it was asked for | GREEN, exit 0 -- the positive control, so the two above are not red for an unrelated reason |

use std::path::{Path, PathBuf};
use std::process::Command;

const WURZEL: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
const DATEI: &str = "beispiele/16-by-ops-am-feld.gab";

fn gabbro() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_gabbro"))
}

/// A model folder with the one file `modell_finden` looks for, and a script directory.
fn aufbau(name: &str) -> (PathBuf, PathBuf) {
    let basis = Path::new(env!("CARGO_TARGET_TMPDIR")).join("beweismessung").join(name);
    let _ = std::fs::remove_dir_all(&basis);
    let modell = basis.join("modell");
    std::fs::create_dir_all(modell.join("Gabbro")).unwrap();
    std::fs::write(modell.join("Gabbro/Body.lean"), "-- stand-in\n").unwrap();
    let skripte = basis.join("skripte");
    std::fs::create_dir_all(&skripte).unwrap();
    (modell, skripte)
}

fn skript(ort: &Path, name: &str, text: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let p = ort.join(name);
    std::fs::write(&p, format!("#!/bin/sh\n{text}\n")).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
    p
}

fn lauf(modell: &Path, lean: &Path, lake: &Path) -> (i32, String) {
    let out = Command::new(gabbro())
        .current_dir(WURZEL)
        .env("LEANBIN", lean)
        .env("LAKE", lake)
        .args(["prove", "--model"])
        .arg(modell)
        .arg(DATEI)
        .output()
        .expect("gabbro runs");
    let text = String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    (out.status.code().unwrap_or(-1), text)
}

#[test]
fn a_lean_that_fails_without_a_position_is_setup_not_green() {
    let (modell, skripte) = aufbau("ohne-ort");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = skript(&skripte, "lean", "echo 'error: no default toolchain configured. run `elan default stable`' >&2\nexit 1");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert!(!text.contains("GREEN"), "a Lean run that failed was reported GREEN:\n{text}");
    assert_eq!(code, 3, "the setup failed, so the exit must be 3:\n{text}");
    assert!(text.contains("SETUP") && text.contains("nothing was measured"), "{text}");
}

#[test]
fn a_lean_that_writes_no_receipt_is_setup_not_green() {
    let (modell, skripte) = aufbau("ohne-quittung");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = skript(&skripte, "lean", "exit 0");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert!(!text.contains("GREEN"), "a Lean run that compiled nothing was reported GREEN:\n{text}");
    assert_eq!(code, 3, "{text}");
    assert!(text.contains("wrote no"), "{text}");
}

/// A stand-in `lean`: writes the receipt it was asked for and, for the gate file (the last
/// argument), answers every `#print axioms gate_N` with `report` (`%s` = the theorem's name).
fn lean_mit_bericht(skripte: &Path, bericht: &str) -> PathBuf {
    skript(
        skripte,
        "lean",
        &format!(
            "while [ $# -gt 1 ]; do if [ \"$1\" = -o ]; then shift; : > \"$1\"; fi; shift; done\n\
             grep '^#print axioms gate_' \"$1\" | sed \"s/#print axioms \\(gate_[0-9]*\\)/'\\1' {bericht}/\"\nexit 0"
        ),
    )
}

#[test]
fn a_lean_that_writes_its_receipt_and_reports_no_axioms_is_setup_not_green() {
    // the fail-closed half of the gate: a run that does not say what the theorems depend on
    // has measured nothing
    let (modell, skripte) = aufbau("ohne-bericht");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = skript(
        &skripte,
        "lean",
        "while [ $# -gt 0 ]; do if [ \"$1\" = -o ]; then shift; : > \"$1\"; fi; shift; done\nexit 0",
    );
    let (code, text) = lauf(&modell, &lean, &lake);
    assert!(!text.contains("GREEN"), "{text}");
    assert_eq!(code, 3, "{text}");
    assert!(text.contains("reported no axioms"), "{text}");
}

#[test]
fn a_lean_that_reports_sorryax_under_a_generated_theorem_is_red() {
    let (modell, skripte) = aufbau("sorryax");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = lean_mit_bericht(&skripte, "depends on axioms: [propext, sorryAx]");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert!(!text.contains("GREEN"), "{text}");
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("sorryAx"), "{text}");
}

#[test]
fn a_lean_that_reports_a_foreign_axiom_is_red_and_the_standard_three_are_green() {
    let (modell, skripte) = aufbau("fremdes-axiom");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = lean_mit_bericht(&skripte, "depends on axioms: [propext, Lean.ofReduceBool]");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("Lean.ofReduceBool"), "{text}");
    let lean = lean_mit_bericht(&skripte, "depends on axioms: [propext, Classical.choice, Quot.sound]");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert_eq!(code, 0, "the standard three are the positive control:\n{text}");
}

#[test]
fn a_lean_that_writes_its_receipt_is_green() {
    let (modell, skripte) = aufbau("mit-quittung");
    let lake = skript(&skripte, "lake", "exit 0");
    let lean = lean_mit_bericht(&skripte, "does not depend on any axioms");
    let (code, text) = lauf(&modell, &lean, &lake);
    assert_eq!(code, 0, "the positive control must be GREEN:\n{text}");
    assert!(text.contains("GREEN"), "{text}");
}

/// **The template spells out both passes of `gabbro_auto2`, at the block's own column, and
/// carries the heartbeat budget** (GabbroV lane, 2026-09-29). Found by running the template of
/// `beispiele/55-kindkette` through Lean: its pipeline is the continuation `    <;> gabbro_pipeline`
/// of a split, and the lines after it were written at that continuation's column (4) -- Lean
/// answered `unexpected identifier; expected command` at the first of them. `124` has no split
/// and is the plain case.
#[test]
fn the_template_carries_both_passes_at_the_blocks_column_and_the_budget() {
    for datei in ["beispiele/55-kindkette.gab", "beispiele/124-two-threads-private.gab"] {
        let out = Command::new(gabbro())
            .current_dir(WURZEL)
            .args(["prove", "--template", datei])
            .output()
            .expect("gabbro runs");
        let text = String::from_utf8_lossy(&out.stdout).to_string();
        assert!(text.contains("set_option maxHeartbeats 11300000"), "{datei}: no heartbeat budget:\n{text}");
        assert!(!text.contains("gabbro_auto2"), "{datei}: the macro must be spelled out:\n{text}");
        let zeilen: Vec<&str> = text.lines().collect();
        let mut gesehen = 0;
        for (i, z) in zeilen.iter().enumerate() {
            if z.trim_start().starts_with("all_goals (try (gabbro_pipeline") {
                gesehen += 1;
                assert!(z.starts_with("  all_goals") && !z.starts_with("   "), "{datei}: the second pass is not at column 2: {z:?}");
                assert!(zeilen[i - 1].contains("gabbro_pipeline"), "{datei}: the second pass does not follow the first");
                let nach = zeilen[i + 2];
                assert_eq!(nach, "  all_goals sorry", "{datei}: the owed goal is not at column 2");
            }
        }
        assert!(gesehen >= 1, "{datei}: no second pass in the template:\n{text}");
    }
}
