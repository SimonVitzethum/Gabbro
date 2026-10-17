//! **`gabbro annahmen` over a corpus: independent programs are not one assumption set.**
//!
//! `SYNTAX.md` §12 makes the manifest a SET: the files named on one command line are the
//! units of ONE program, and the same name declared differently in two of them is a
//! contradiction. A corpus run (`gabbro annahmen beispiele/*.gab`) names files that are NOT
//! one program -- examples 74, 90, 96, 149, 163 and 182 (74 and 182 differ in wording) each declare their own
//! `linux_write_contract` -- and aborted over a conflict that does not exist. `--per-file`
//! keeps the sets apart; a conflict INSIDE one file still falls.

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

const A: &str = "beispiele/74-syscall-schreiben.gab";
const B: &str = "beispiele/182-fallible-gate.gab";

#[test]
fn zwei_programme_mit_verschiedener_annahme_fallen_ohne_das_flag_als_eines() {
    let (_, fehler, code) = lauf(&["annahmen", A, B]);
    assert_eq!(code, 1, "as ONE program the two declarations contradict:\n{fehler}");
    assert!(fehler.contains("linux_write_contract"), "by name:\n{fehler}");
}

#[test]
fn je_datei_haelt_die_programme_auseinander() {
    let (aus, fehler, code) = lauf(&["annahmen", "--per-file", A, B]);
    assert_eq!(code, 0, "each file is its own program:\n{fehler}");
    assert!(aus.contains(&format!("== {A}")) && aus.contains(&format!("== {B}")), "{aus}");
    assert_eq!(aus.matches("linux_write_contract").count(), 2, "one per file:\n{aus}");
}

#[test]
fn ein_widerspruch_in_einer_datei_faellt_auch_je_datei() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../.claude/muse-arbeit/kratz");
    std::fs::create_dir_all(dir).expect("scratch dir");
    let pfad = format!("{dir}/annahme-widerspruch-{}.gab", std::process::id());
    std::fs::write(
        &pfad,
        "module widerspruch {\n\n\
         assume ein_vertrag\n    \"The first wording.\"\n    falsifier sonde_a;\n\n\
         assume ein_vertrag\n    \"A different wording.\"\n    falsifier sonde_a;\n\n}\n",
    )
    .expect("write probe");
    let (_, fehler, code) = lauf(&["annahmen", "--per-file", &pfad]);
    let _ = std::fs::remove_file(&pfad);
    assert_eq!(code, 1, "a contradiction inside ONE program still aborts:\n{fehler}");
    assert!(fehler.contains("ein_vertrag"), "by name:\n{fehler}");
}
