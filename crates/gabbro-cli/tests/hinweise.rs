//! **Permanent probes for the subcommand hint (Lane B, held by Lane B2).**
//!
//! Lane B built the unknown-subcommand hint in `src/main.rs::suggest` (at most 2
//! edits, same initial, table members only) with its cases as in-file unit tests.
//! Those cases move here in integration form -- binary in, stderr out -- so the
//! hint stays measured at the surface the user sees, not at the function.
//!
//! Both directions, or neither is a measurement: firing cases assert the hint
//! names the meant spelling, silent cases assert no hint is printed at all.

use std::process::Command;

fn run(args: &[&str]) -> (String, String, i32) {
    let out = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(args)
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        out.status.code().unwrap_or(-1),
    )
}

/// **The hint fires where due** -- one slipped letter, one missing letter, one
/// transposed pair, each answered on stderr with the spelling that was meant.
/// An unknown subcommand exits 2; the hint rides along, it never dispatches.
#[test]
fn hint_fires_where_due() {
    for (typed, near) in [
        ("chek", "check"),
        ("pruefen", "pruefe"),
        ("biuld", "build"),
        ("hep", "help"),
        ("kostne", "kosten"),
    ] {
        let (_, err, code) = run(&[typed]);
        assert_eq!(
            code, 2,
            "`gabbro {typed}` is unknown -- exit 2 carries the refusal"
        );
        assert!(
            err.contains(&format!("did you mean `gabbro {near}`?")),
            "`gabbro {typed}` must suggest `gabbro {near}` on stderr:\n{err}"
        );
    }
}

/// **And it stays silent where not** -- no near reading, no guess. `xyz` shares
/// no initial with any command; `qqq`, `c` and `h` are too far from every word
/// they start. The refusal (exit 2) stands alone in all four.
#[test]
fn hint_silent_where_not_due() {
    for typed in ["xyz", "qqq", "c", "h"] {
        let (_, err, code) = run(&[typed]);
        assert_eq!(
            code, 2,
            "`gabbro {typed}` is unknown -- exit 2 carries the refusal"
        );
        assert!(
            !err.contains("did you mean"),
            "`gabbro {typed}` must print no hint:\n{err}"
        );
    }
}

/// **An exact spelling needs no hint.** A known command runs -- here `help`,
/// which exits 0 -- and stderr carries no suggestion.
#[test]
fn exact_spelling_carries_no_hint() {
    let (_, err, code) = run(&["help"]);
    assert_eq!(code, 0, "`gabbro help` is known:\n{err}");
    assert!(
        !err.contains("did you mean"),
        "`gabbro help` must print no hint:\n{err}"
    );
}
