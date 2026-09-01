//! **The five hints of «B3», measured in BOTH directions.**
//!
//! *Eight attempts for "add two numbers", by someone with the whole grammar and 63 examples
//! open.* Five of the seven refusals were syntax paper cuts. **Every one of them was correct
//! and well explained, and none of them taught the shape** -- so five lines were added, each
//! at the exact site of one measured attempt.
//!
//! | # | the attempt | what refused it | what the refusal did NOT say |
//! |---|---|---|---|
//! | 1 | no `effects` at all | `E001` | what the clause LOOKS like |
//! | 2 | `effects {}` | `P014` | that `pure` is the word for "none" |
//! | 3 | `effects pure` | `P001` | that `effects` takes a BRACE LIST |
//! | 4 | `u32 + u32 -> u64` | `M104` | that the width is the OPERANDS' |
//! | 5 | `else { return 0 }` | `P001` | that the LAST statement needs its `;` too |
//!
//! **Paper cut 6 (`… else { return 0; };`) got no new line, and that is a finding and not an
//! omission:** `P033` already names the block forms and `narrow … else` among them. *A hint
//! added there would have been a hint nobody measured a need for.*
//!
//! # The direction that is easy to forget
//!
//! **A hint that fires on correct code is worse than none.** Firing is held here file by
//! file against `beispiele/gift/580`…`584`; SILENCE is held over the whole clean corpus --
//! every `.gab` under `beispiele/`, not a sample -- and no hint text may appear in any of
//! them. *Silence is not free just because a note hangs off an error: a note is text, and
//! text over 176 clean files is a claim that has to be measured.*
//!
//! > **And the reverse of the reverse:** the counter-direction run over all 539 `.gab` files
//! > of the tree with both binaries (`instrumente/vergleiche-binaerprogramme.py`) moved
//! > **9 files, all of them poison, and none of them by exit code** -- pure added note lines
//! > under refusals that already stood.

use std::path::{Path, PathBuf};

/// The exact text of each hint. **Stated once, here** -- a probe that spelled a
/// near-miss of the message would go green over a message nobody ships.
const HINWEISE: &[(&str, &str)] = &[
    ("E001", "the clause is a BRACE LIST and it is never empty"),
    ("P014", "an EMPTY list is not `no effects`"),
    ("P001-brace", "`effects` takes a BRACE LIST and not a bare word"),
    ("M104", "the width that is left is the OPERANDS'"),
    ("P001-semi", "the LAST statement of a block ends with `;` too"),
];

/// The poison file each hint was measured on, in the order of the eight attempts.
const STELLEN: &[(&str, &str)] = &[
    ("E001", "580-wirkungsklausel-fehlt.gab"),
    ("P014", "581-wirkungsliste-leer.gab"),
    ("P001-brace", "582-wirkung-ohne-klammern.gab"),
    ("M104", "583-summe-verlaesst-die-breite.gab"),
    ("P001-semi", "584-strichpunkt-fehlt-im-block.gab"),
];

fn beispiele() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

/// The rendered report of one file -- refusals, notes and all, exactly as a reader sees it.
fn bericht(pfad: &Path) -> String {
    let quelle = std::fs::read_to_string(pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let name = pfad.file_name().and_then(|s| s.to_str()).unwrap_or("?");
    let (baum, mut absagen) = gabbro_syntax::lies(name, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen.zeige(&quelle)
}

/// **Direction one: each hint fires on the shape that was measured.**
#[test]
fn jeder_hinweis_feuert_auf_seiner_form() {
    for (marke, datei) in STELLEN {
        let pfad = beispiele().join("gift").join(datei);
        assert!(pfad.exists(), "the poison probe stands: {}", pfad.display());
        let text = bericht(&pfad);
        let (_, erwartet) = HINWEISE
            .iter()
            .find(|(m, _)| m == marke)
            .expect("every site has its hint");
        assert!(
            text.contains(erwartet),
            "`{datei}` must carry the «B3» hint `{marke}`:\n  expected: {erwartet}\n{text}"
        );
    }
}

/// **Direction two: none of the five says anything over the CLEAN corpus.**
///
/// Over every `.gab` under `beispiele/` -- not a sample. *A hint that fires on correct code
/// is worse than none, and the only way to know is to read all of them.*
#[test]
fn kein_hinweis_spricht_ueber_sauberem_quelltext() {
    let mut gesehen = 0;
    for e in std::fs::read_dir(beispiele()).expect("beispiele lesbar") {
        let pfad = e.expect("Eintrag").path();
        if pfad.extension().is_none_or(|x| x != "gab") {
            continue;
        }
        gesehen += 1;
        let text = bericht(&pfad);
        for (marke, hinweis) in HINWEISE {
            assert!(
                !text.contains(hinweis),
                "the «B3» hint `{marke}` speaks over the CLEAN file {}: \n{text}",
                pfad.display()
            );
        }
    }
    assert!(
        gesehen >= 60,
        "the probe found the clean corpus: {gesehen} files -- a sweep over three would \
         prove nothing"
    );
}

/// **Paper cut 6 needed no new line, and this holds the reason.**
///
/// `P033` already names `narrow … else` among the forms that carry no trailing semicolon.
/// *If that note is ever shortened, this probe goes red and asks for a sixth hint* -- which
/// is the honest order: measure the gap, then write the line.
#[test]
fn der_sechste_papierschnitt_war_schon_gedeckt() {
    let quelle = "module s {\n\
                  pub fn f(a : u32 in 0 .. 50) -> u32 in 0 .. 100\n\
                      effects { pure }\n\
                      costs <= 8 ops\n\
                  {\n\
                      narrow a to 0 .. 50 else { return 0; };\n\
                      return a;\n\
                  }\n\
                  }\n";
    let (baum, mut absagen) = gabbro_syntax::lies("s.gab", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let text = absagen.zeige(quelle);
    assert!(text.contains("P033"), "the trailing semicolon is refused:\n{text}");
    assert!(
        text.contains("carry NO trailing semicolon") && text.contains("`narrow … else`"),
        "and `P033` names the form the reader typed -- no sixth hint is owed:\n{text}"
    );
}

/// **The `M104` hint adapts to the operand type, and it never offers a way out that does not
/// exist.** At 64 bits there is no wider type to bind into.
#[test]
fn der_breitenhinweis_verspricht_keine_breite_die_es_nicht_gibt() {
    let vier = "module w { pub fn f(a : u32, b : u32) -> u64 effects { pure } \
                costs <= 4 ops { return a + b; } }";
    let acht = "module w { pub fn f(a : u64, b : u64) -> u64 effects { pure } \
                costs <= 4 ops { return a + b; } }";
    let vorzeichen = "module w { pub fn f(a : i32, b : i32) -> i64 effects { pure } \
                      costs <= 4 ops { return a + b; } }";

    for (quelle, muss, darf_nicht) in [
        (vier, "let w : u64 = x;", "no wider type"),
        (acht, "at 64 bits there is no wider type", "bind each operand"),
        (vorzeichen, "let w : i64 = x;", "u64 = x"),
    ] {
        let (baum, mut absagen) = gabbro_syntax::lies("w.gab", quelle);
        let _ = gabbro_check::pruefe(&baum, &mut absagen);
        let text = absagen.zeige(quelle);
        assert!(text.contains("M104"), "the width is left:\n{text}");
        assert!(text.contains(muss), "the note says `{muss}`:\n{text}");
        assert!(
            !text.contains(darf_nicht),
            "and it does NOT say `{darf_nicht}`:\n{text}"
        );
    }
}
