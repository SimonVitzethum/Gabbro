//! **Every subcommand has an ENGLISH first name, and the German second name keeps working.**
//!
//! The path is additive and costs nothing: the tree already carried the shape at
//! `"--hilfe" | "-h" | "hilfe"`. What it does NOT carry on its own is the guarantee that the
//! two spellings do the same thing -- so that is what is held here, pair by pair, over the
//! whole list rather than over an example.
//!
//! **The word for the second spelling is `Zweitname`, not `alias`.** `gabbro alias` is a
//! subcommand about POINTER aliasing, and one word for two things is how a register starts
//! to drift.
//!
//! > **W16, and it was a real hole:** `split_with("pruefe", …)` handed a LITERAL name to its
//! > own refusal. Under the second spelling the message named a command nobody had typed. The
//! > typed spelling is threaded through now, and `die_absage_nennt_den_getippten_namen` holds
//! > it.

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

/// The twelve pairs. **`abi`, `emit`, `lean` and `build` are not here** -- they were English
/// from the start, and a pair of one word is not a pair.
const PAARE: &[(&str, &str)] = &[
    ("check", "pruefe"),
    ("fragments", "fragmente"),
    ("assumptions", "annahmen"),
    ("k-condition", "k-bedingung"),
    ("costs", "kosten"),
    ("contexts", "kontexte"),
    ("obligations", "pflichten"),
    ("blindspots", "blindstellen"),
    ("certificate", "zeugnis"),
    ("ceremony", "zeremonie"),
    ("templates", "schablonen"),
    ("passes", "paesse"),
];

const DATEI: &str = "beispiele/16-by-ops-am-feld.gab";

/// **Both spellings, byte for byte the same run.** Over every pair, not over one.
#[test]
fn jeder_erstname_tut_dasselbe_wie_sein_zweitname() {
    for (englisch, deutsch) in PAARE {
        // `templates` and `passes` take no file; the others do. Handing a file to one that
        // ignores it changes nothing, so one call shape covers both.
        let a = lauf(&[englisch, DATEI]);
        let b = lauf(&[deutsch, DATEI]);
        assert_eq!(
            a, b,
            "`gabbro {englisch}` and `gabbro {deutsch}` are one command, \
             in stdout, stderr and exit code"
        );
        assert_ne!(
            a.2, 2,
            "`gabbro {englisch}` is a KNOWN command -- exit 2 would mean it fell through to \
             the unknown-command arm and the pair proves nothing"
        );
    }
}

/// **The English name comes FIRST in the help, and the German one is printed too.**
#[test]
fn die_hilfe_zeigt_beide_namen_englisch_zuerst() {
    let (_, hilfe, _) = lauf(&["help"]);
    for (englisch, deutsch) in PAARE {
        let paar = format!("{englisch}|{deutsch}");
        assert!(
            hilfe.contains(&paar),
            "`{paar}` stands in the help, English first:\n{hilfe}"
        );
    }
    assert!(
        hilfe.contains("ENGLISH first name"),
        "and the rule itself is written down, not only practised:\n{hilfe}"
    );
}

/// `help` and `--help` reach the same place as `hilfe`, `--hilfe` and `-h`.
#[test]
fn hilfe_hat_auch_einen_englischen_erstnamen() {
    let englisch = lauf(&["help"]);
    for zweitname in ["--help", "hilfe", "--hilfe", "-h"] {
        assert_eq!(
            englisch,
            lauf(&[zweitname]),
            "`{zweitname}` reaches the same help"
        );
    }
}

/// **W16: a refusal names the spelling that was TYPED.**
///
/// `split_with` and `read_preamble` used to carry a literal `"pruefe"` / `"emit"`. Under the
/// other spelling the message named a command nobody had called -- a measuring device
/// reporting its own name instead of the subject's.
#[test]
fn die_absage_nennt_den_getippten_namen() {
    // `--with` demands a `.gabi`; a `.gab` is refused, and the refusal carries the name.
    for (getippt, erwartet) in [
        ("check", "gabbro check:"),
        ("pruefe", "gabbro pruefe:"),
        ("emit", "gabbro emit:"),
    ] {
        let (_, fehler, code) = lauf(&[getippt, "--with", DATEI, DATEI]);
        assert_eq!(code, 2, "a `.gab` is no `.gabi`:\n{fehler}");
        assert!(
            fehler.contains(erwartet),
            "the refusal names `{getippt}`, the spelling that was typed:\n{fehler}"
        );
    }
}

/// A name that is neither spelling is still refused, and the help still comes.
#[test]
fn ein_unbekannter_befehl_faellt_weiter() {
    let (_, fehler, code) = lauf(&["pruefen"]);
    assert_eq!(code, 2, "not a command:\n{fehler}");
    assert!(
        fehler.contains("pruefen"),
        "and the refusal quotes what was typed:\n{fehler}"
    );
}
