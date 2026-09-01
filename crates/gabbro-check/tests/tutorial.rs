//! **`TUTORIAL.md` is measured against the compiler, not proofread.**
//!
//! *A teaching document whose examples do not compile is the most expensive kind of prose: it
//! looks like a proof.* The same rule already holds `dokumente/SYNTAX.md`
//! (`die_beispiele_der_grammatik_gehen_selbst_durch`), and it holds harder here -- the reader
//! of a grammar document has the grammar; the reader of the tutorial has nothing else.
//!
//! **It found something on the first run.** Section 4 called its example function `double`,
//! and `double` is a keyword of C11: `N041`. That refusal became section 9's second half --
//! *Gabbro does not mangle, so C's vocabulary is closed to you at the boundary too* -- and it
//! is in the tutorial because the tutorial was measured, not because anybody remembered it.
//!
//! What is held here:
//!
//! * **every complete unit in the file checks with 0 errors** -- gate P2 demands 100 %;
//! * **the file really carries units**, so that emptying it cannot pass;
//! * **the commands it tells a newcomer to type exist**, spelled as it spells them.
//!
//! > **And what is NOT held:** whether the file teaches. The examples compile; that a reader
//! > gets from them to a program of their own is measured by writing one, and that
//! > measurement lives in a commit message, not in an assertion.

use gabbro_check::korpus;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("Wurzel")
        .to_path_buf()
}

fn tutorial() -> String {
    std::fs::read_to_string(wurzel().join("TUTORIAL.md")).expect("TUTORIAL.md liegt da")
}

/// **Every complete unit in the tutorial checks.** Gate P2, over the file a newcomer reads
/// first.
#[test]
fn jeder_block_des_tutorials_geht_durch() {
    let md = tutorial();
    let mut einheiten = 0;
    for b in korpus::messe("TUTORIAL.md", &md) {
        if !b.vollstaendig {
            continue;
        }
        einheiten += 1;
        assert!(
            b.sauber(),
            "TUTORIAL.md, block from line {}: the on-ramp breaks the language it teaches:\n{}",
            b.erste_zeile,
            b.text
        );
    }
    assert!(
        einheiten >= 6,
        "the tutorial carries its examples as complete units: {einheiten} found -- \
         a file whose blocks all became excerpts would pass the assertion above and \
         measure nothing"
    );
}

/// **The commands the tutorial tells a newcomer to type exist**, in the spelling it uses.
///
/// *A tutorial is a list of instructions, and an instruction that names a command nobody
/// answers is the seventh paper cut with better manners.* The spellings are checked against
/// the help text, which is where a reader would look next.
#[test]
fn jeder_befehl_den_das_tutorial_nennt_gibt_es() {
    let md = tutorial();
    let hilfe = std::fs::read_to_string(
        wurzel().join("crates/gabbro-cli/src/main.rs"),
    )
    .expect("main.rs");

    let mut geprueft = 0;
    for befehl in [
        "gabbro new",
        "gabbro build",
        "gabbro check",
        "gabbro costs",
        "gabbro effects",
        "gabbro passes",
        "gabbro certificate",
        "gabbro obligations",
        "gabbro abi",
        "gabbro fragments",
    ] {
        let wort = befehl.trim_start_matches("gabbro ");
        if !md.contains(befehl) {
            continue;
        }
        geprueft += 1;
        assert!(
            hilfe.contains(&format!("\"{wort}\"")),
            "TUTORIAL.md tells the reader to run `{befehl}`, and no subcommand answers to \
             `{wort}`"
        );
    }
    // **A probe that skips every row of its own table is green and empty.** The tutorial
    // names nine of the ten today; the floor is well under that and still bites if the file
    // stops naming commands at all.
    assert!(
        geprueft >= 6,
        "the probe found the commands the tutorial names: {geprueft} of 10 -- a sweep that \
         matched nothing would assert nothing"
    );
}

/// **The tutorial names the tool that prints the cost, at its first `costs` line.**
///
/// *That was the finding the whole file is built around*: `gabbro costs` computes the number
/// a `costs` clause has to carry, and a cost bound was guessed five times in one session
/// while it sat in the same binary. A tutorial that introduces `costs` without it teaches
/// the guessing.
#[test]
fn das_tutorial_nennt_gabbro_costs_bei_der_ersten_kostenzeile() {
    let md = tutorial();
    let erste_kostenzeile = md
        .find("costs   <=")
        .or_else(|| md.find("costs <="))
        .expect("the tutorial shows a `costs` clause");
    let nennt_werkzeug = md
        .find("gabbro costs")
        .expect("the tutorial names `gabbro costs`");
    // The section that introduces `costs` may show the clause first; what may not happen is
    // that the tool is never named, or named only in a closing table.
    assert!(
        nennt_werkzeug < erste_kostenzeile + 4000,
        "`gabbro costs` is named {} characters after the first `costs` clause -- \
         a reader who stops before that has been taught to guess",
        nennt_werkzeug.saturating_sub(erste_kostenzeile)
    );
}

/// **The showcase in section 8 carries the number the tool prints, and this holds it.**
///
/// *Found by a reader who had only `TUTORIAL.md` and the binary*, 2026-09-01. Section 5 says
/// *"copy the number down -- a `costs` line is a measurement, not an estimate"*; section 8
/// then showed `costs <= 4 ops` over a body `gabbro costs` computes as **3**, annotated *"read
/// off `gabbro costs`, not guessed"*. **Both could not be true**, and the reader followed
/// section 5 and wrote 3.
///
/// A tutorial whose worked example breaks its own sharpest rule teaches the rule it shows,
/// not the rule it states. The showcase now runs at `slack 0`, and this probe keeps it there.
///
/// > *The other blocks in the file are allowed slack on purpose* -- section 5 says a bound
/// > above the computed number is often the right call. **The final example is the one that
/// > has to demonstrate the practice**, so it is the only one held.
#[test]
fn das_letzte_beispiel_traegt_die_gerechnete_zahl() {
    let md = tutorial();
    let block = korpus::schneide(&md)
        .into_iter()
        .find(|b| b.text.contains("module tutorial::add_two"))
        .expect("section 8 carries the worked example");
    let (baum, _) = gabbro_syntax::lies("TUTORIAL.md", &block.text);
    let bericht = gabbro_check::kosten::bericht(&baum);
    let zeile = bericht
        .lines()
        .find(|z| z.starts_with("sum\t"))
        .unwrap_or_else(|| panic!("the example declares `sum`:\n{bericht}"));
    let spalten: Vec<&str> = zeile.split('\t').collect();
    assert_eq!(
        spalten.get(1),
        spalten.get(2),
        "section 8 promises `{}` ops over a body that costs `{}` -- the tutorial's own rule \
         is to copy the computed number down, and its worked example is where a reader \
         looks for the practice:\n{bericht}",
        spalten.get(2).unwrap_or(&"?"),
        spalten.get(1).unwrap_or(&"?")
    );
}

/// **The footer is on page one.** *No other compiler tells you what it did not look at*, and
/// a reader should meet that where they meet the tool, not discover it.
#[test]
fn das_tutorial_zeigt_die_fusszeile_frueh() {
    let md = tutorial();
    let stelle = md
        .find("Not checked in this run")
        .expect("the tutorial shows the register footer");
    assert!(
        stelle < md.len() / 3,
        "the `Not checked in this run` footer stands at {stelle} of {} -- it belongs on \
         page one",
        md.len()
    );
}
