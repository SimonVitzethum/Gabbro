//! **`gabbro pruefe --unit` -- the named files as ONE translation unit.**
//!
//! The measurement behind it stands in `messung/EINHEITENSICHT.md`. The short form: the
//! resolver (`umgebung.rs::kandidaten`) walked the module chain and followed `use` lines all
//! along; what it never got was the OTHER FILE. `gabbro lean` joins the sources and therefore
//! resolves; `gabbro pruefe` loops and therefore does not.
//!
//! **Why these tests live here and not in `beispiele/gift/`:** that harness runs ONE FILE PER
//! PROCESS, and every case below needs two or three. A poison sample that cannot be handed to
//! its own harness is not a poison sample -- so the cases stand where the command line is
//! driven.
//!
//! > **The counter-direction carries more weight here than the finding.** An over-wide
//! > resolution turns correct refusals into silence, and silence reads exactly like a clean
//! > run. Four of the six tests below are counter-direction.

use std::process::Command;

/// stdout, stderr and the exit code -- all three, because a refusal that moved from one
/// stream to the other is a changed refusal.
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

const LAGER: &str = "programmlogik/beispiel/lager.gab";
const BETRIEB: &str = "programmlogik/beispiel/betrieb.gab";

/// **The counter-sample: two files that belong together check clean as one unit.**
///
/// `betrieb.gab` says in its own first line that it writes into a table standing in
/// `lager.gab`. Checked file by file that is five refusals; checked as a unit it is none.
#[test]
fn zwei_dateien_als_einheit_loesen_auf() {
    let (aus, _, code) = lauf(&["pruefe", "--unit", LAGER, BETRIEB]);
    assert_eq!(code, 0, "the unit checks clean:\n{aus}");
    assert!(
        aus.contains("unit of 2 file(s): 15 items, 0 errors, 0 hints"),
        "the unit line names files, items and both counts:\n{aus}"
    );
}

/// The German second name reaches the same code. *A flag with two spellings that do two things is
/// worse than a flag with one.*
#[test]
fn der_deutsche_zweitname_der_fahne_tut_dasselbe() {
    let englisch = lauf(&["pruefe", "--unit", LAGER, BETRIEB]);
    let deutsch = lauf(&["pruefe", "--einheit", LAGER, BETRIEB]);
    assert_eq!(englisch, deutsch, "`--unit` and `--einheit` are one flag");
}

/// **Counter-direction 1: a name out of a file that was NOT handed over must still fall.**
///
/// Without this the flag would not resolve names, it would merely stop looking for them.
#[test]
fn ohne_die_andere_datei_faellt_es_weiter() {
    let (aus, _, code) = lauf(&["pruefe", "--unit", BETRIEB]);
    assert_eq!(code, 1, "one file alone is still one file:\n{aus}");
    for erwartet in ["N040", "M109", "M119", "H016"] {
        assert!(
            aus.contains(erwartet),
            "`{erwartet}` still falls when `lager.gab` is not handed over:\n{aus}"
        );
    }
}

/// **Counter-direction 2: a name that no `use` names must fall, even though the file
/// carrying it lies right beside it in the same run.**
#[test]
fn ein_name_ohne_use_faellt_auch_neben_seiner_datei() {
    let (aus, _, code) = lauf(&[
        "pruefe",
        "--unit",
        "messung/einheit-proben/pub-a.gab",
        "messung/einheit-proben/ohne-use-b.gab",
    ]);
    assert_eq!(code, 1, "no `use`, no name:\n{aus}");
    assert!(aus.contains("[N040]"), "the type name does not resolve:\n{aus}");
    // **And the site is the site in ITS OWN FILE.** Without the offset map the line number
    // would be the one in the concatenation -- a line number in no file at all, which is what
    // `gabbro lean` names as its own price.
    assert!(
        aus.contains("messung/einheit-proben/ohne-use-b.gab:7:29"),
        "the refusal points into the file it came from, at its own line:\n{aus}"
    );
}

/// **Counter-direction 3: `pub` decides what leaves a module -- and it decides twice.**
///
/// `N025` at the `use` line, `N038` at the exported signature that would carry the name
/// abroad.
#[test]
fn pub_entscheidet_was_hinausgeht() {
    let (aus, _, code) = lauf(&[
        "pruefe",
        "--unit",
        "messung/einheit-proben/pub-a.gab",
        "messung/einheit-proben/pub-b.gab",
    ]);
    assert_eq!(code, 1, "a private name does not travel:\n{aus}");
    assert!(aus.contains("[N025]"), "the `use` line itself is refused:\n{aus}");
    assert!(aus.contains("[N038]"), "and the export that would carry it:\n{aus}");
}

/// **Counter-direction 4: two modules carrying the same name do not hide one another.**
///
/// The answer today is blunter than "the nearer one wins": `N039` refuses the whole build,
/// because both names would carry the same C name. **And it is order-independent** -- the
/// refusal names whichever module came first, but it comes either way.
#[test]
fn zwei_module_mit_demselben_namen_verdecken_einander_nicht() {
    let x = "messung/einheit-proben/kollision-x.gab";
    let y = "messung/einheit-proben/kollision-y.gab";
    let z = "messung/einheit-proben/kollision-z.gab";
    for reihenfolge in [[x, y, z], [y, x, z]] {
        let (aus, _, code) = lauf(&[
            "pruefe",
            "--unit",
            reihenfolge[0],
            reihenfolge[1],
            reihenfolge[2],
        ]);
        assert_eq!(code, 1, "the collision is refused in either order:\n{aus}");
        assert!(aus.contains("[N039]"), "and it is `N039` that refuses it:\n{aus}");
    }
}

/// **A HINT is printed, not swallowed -- and the summary counts it.**
///
/// *This test exists because a hand mutation survived without it* (`451`, and the whole run
/// stayed green): a single `continue` on `Stufe::Hinweis` in the bucketing loop made every
/// hint of a unit vanish, and the six tests above did not notice, because every one of them
/// looks at errors. **Silence reads exactly like a clean run** -- which is the failure this
/// whole flag is under suspicion of, so the flag has to be held against it by name.
///
/// `lager.gab` alone carries `H008`: a lock that nothing takes. Handed over WITH `betrieb.gab`
/// the hint is gone, and rightly so -- the taking stands in the other file. Alone it must
/// stay.
#[test]
fn ein_hinweis_wird_gedruckt_und_gezaehlt() {
    let (aus, _, code) = lauf(&["pruefe", "--unit", LAGER]);
    assert_eq!(code, 0, "a hint is not an error:\n{aus}");
    assert!(
        aus.contains("hint: [H008] programmlogik/beispiel/lager.gab:12:10"),
        "the hint is printed, with its own file and its own line:\n{aus}"
    );
    assert!(
        aus.contains("unit of 1 file(s): 6 items, 0 errors, 1 hints"),
        "and the summary counts it -- a count that says 0 where one was printed is worse \
         than either:\n{aus}"
    );
    // **And the counter-direction of the counter-direction:** with the other file the hint
    // is GONE, because the lock is taken there. Otherwise the test above would pass on a
    // checker that simply never resolves anything.
    let (mit, _, _) = lauf(&["pruefe", "--unit", LAGER, BETRIEB]);
    assert!(
        !mit.contains("[H008]"),
        "as a unit the lock IS taken, so the hint falls away:\n{mit}"
    );
}

/// **What joining BUYS, beside silence: a finding no per-file run can reach.**
///
/// `messung/abi-proben/mischt.gab` carries a lock ring across two libraries and says so in
/// its own first line -- *"der Zyklus, den weder `speicher` noch `geraet` allein sehen
/// kann"*. File by file the checker reports name noise and not the ring. As a unit it reports
/// the ring, twice, with the site in the file that carries it.
#[test]
fn der_sperrring_ueber_bibliotheken_wird_erst_als_einheit_sichtbar() {
    let dateien = [
        "messung/abi-proben/lib-speicher.gab",
        "messung/abi-proben/lib-geraet.gab",
        "messung/abi-proben/mischt.gab",
    ];
    // File by file: no `H012` anywhere.
    for d in dateien {
        let (aus, _, _) = lauf(&["pruefe", d]);
        assert!(
            !aus.contains("[H012]"),
            "checked alone, {d} cannot see the ring:\n{aus}"
        );
    }
    let (aus, _, code) = lauf(&["pruefe", "--unit", dateien[0], dateien[1], dateien[2]]);
    assert_eq!(code, 1, "as a unit the ring is refused:\n{aus}");
    assert_eq!(
        aus.matches("[H012]").count(),
        2,
        "both directions of the ring, not one:\n{aus}"
    );
    assert!(
        aus.contains("messung/abi-proben/mischt.gab:17:9"),
        "and the site is in the file that closes the ring:\n{aus}"
    );
}

// =========================================================================================
// **`emit --unit` and `abi --unit` -- the other half of the pair** (2026-09-01, `OB5`).
//
// Until this day a unit that CHECKED as a unit was not TRANSLATED as one: `pruefe --unit`
// joined the files, `emit` looped over them, and `gabbro abi` refused the second file because
// it cannot be checked alone. *The capability existed inside `gabbro build` and had no name
// on the command line* -- which is the shape a missing feature and a hidden one share.

/// **The counter-sample, and the price named as a number.**
///
/// The same two files, one flag apart: seven refusals without it, none with it.
#[test]
fn emit_als_einheit_uebersetzt_was_einzeln_faellt() {
    let (_, fehler, code) = lauf(&["emit", LAGER, BETRIEB]);
    assert_eq!(code, 1, "file by file the second one falls:\n{fehler}");
    assert_eq!(
        fehler.matches("error: [").count(),
        7,
        "and it falls seven times, at names the other file declares:\n{fehler}"
    );

    let (aus, fehler, code) = lauf(&["emit", "--unit", LAGER, BETRIEB]);
    assert_eq!(code, 0, "as one unit it translates:\n{fehler}");
    assert!(aus.contains("int32_t"), "and the C is C:\n{aus}");
    assert!(
        aus.contains("void raeumen(") && aus.contains("void kennzeichnen("),
        "with the bodies of the SECOND file in it:\n{aus}"
    );
}

/// **The refusals of `emit --unit` go to STDERR, and that is not a slip.**
///
/// This command writes the C to stdout. A diagnostic on the same stream would land inside the
/// translation unit of whoever piped the output into a `.c` file -- so the two streams carry
/// two different things, and the test says which.
#[test]
fn die_absagen_von_emit_stehen_nicht_im_c() {
    let (aus, fehler, code) = lauf(&["emit", "--unit", BETRIEB]);
    assert_eq!(code, 1, "alone the file does not translate:\n{aus}\n{fehler}");
    assert!(fehler.contains("error: ["), "the refusals are on stderr:\n{fehler}");
    assert!(
        !aus.contains("error: ["),
        "and NOT on stdout, where the C goes:\n{aus}"
    );
    // **And the site is in the file, not in the concatenation.**
    assert!(
        fehler.contains("programmlogik/beispiel/betrieb.gab:"),
        "the site is the site in the file:\n{fehler}"
    );
    assert!(!fehler.contains("<unit>:"), "never the joined text:\n{fehler}");
}

/// The German second name reaches the same code, at `emit` as at `pruefe`.
#[test]
fn der_zweitname_der_fahne_gilt_auch_bei_emit() {
    let englisch = lauf(&["emit", "--unit", LAGER, BETRIEB]);
    let deutsch = lauf(&["emit", "--einheit", LAGER, BETRIEB]);
    assert_eq!(englisch, deutsch, "`--unit` and `--einheit` are one flag here too");
}

/// **`abi --unit` writes ONE interface for a unit of two files** -- and it carries what the
/// second file exports, which no per-file run can produce at all.
#[test]
fn abi_als_einheit_schreibt_eine_schnittstelle() {
    let (_, _, code) = lauf(&["abi", BETRIEB]);
    assert_eq!(code, 1, "alone the second file has no interface");

    let (aus, fehler, code) = lauf(&["abi", "--unit", LAGER, BETRIEB]);
    assert_eq!(code, 0, "as a unit it has one:\n{fehler}");
    assert!(aus.starts_with("-- @gabi 1"), "with the marker:\n{aus}");
    assert!(
        aus.contains("pub table Faecher") && aus.contains("pub extern fn raeumen("),
        "and both files' exports in it:\n{aus}"
    );
    // **A body never travels.** An interface with a body would be a second copy of the code.
    assert!(
        !aus.contains("Faecher.slots[f].belegt  = false;"),
        "no body crosses the boundary:\n{aus}"
    );
}
