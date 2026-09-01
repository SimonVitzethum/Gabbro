//! **Every FLAG has an ENGLISH first name too -- and a guardian holds it for the flag
//! nobody has written yet.**
//!
//! `erstnamen.rs` next door holds the twelve sub-command pairs that EXIST. It cannot hold the
//! thirteenth, and `messung/ERSTNAMEN.md` §5 said so about itself on the day it was written:
//!
//! > *"Kein Waechter prueft, dass ein NEUER Unterbefehl einen englischen Erstnamen bekommt --
//! > `erstnamen.rs` haelt die zwoelf, die es gibt, und nicht den dreizehnten, den jemand
//! > morgen hinzufuegt."*
//!
//! **The difference is that this file reads the SOURCE, not a list.** A flag or a sub-command
//! that appears in `crates/gabbro-cli/src/` and not in the register below turns this red --
//! whatever language it is in. *A rule in the tool is worth more than a rule in the head.*
//!
//! ## What it holds, in four layers
//!
//! | | |
//! |---|---|
//! | **completeness** | every flag spelling in the source stands in the register. **This is the ratchet** -- a NEW flag is red until someone registers it and gives it an English first name |
//! | **first name** | no registered first name carries a German word |
//! | **equivalence** | both spellings of a pair are ONE flag: stdout, stderr and exit code byte for byte |
//! | **liveness** | and each pair is measured at a call where the flag DEMONSTRABLY changes the run |
//!
//! **The fourth layer is the one that is easy to leave out, and without it the third is
//! empty.** An unknown flag is not refused by this CLI -- it is ignored, or handed on as a
//! file name. So two spellings that are BOTH unread produce identical output, and a typo in
//! an English first name would pass the equivalence test with full marks. *A test that
//! measures equality has to measure first that anything is there* -- the same sentence
//! `ERSTNAMEN.md` §3 wrote about the sub-commands, one level down.
//!
//! ## What it does NOT do (W10)
//!
//! **The German word list is a closed list, and it obliges rather than acquits.** It cannot
//! decide "is this word English?" -- nothing in this tree can. What it names is German; what
//! it does not name may still be German. **The completeness layer is what actually holds the
//! line**, because it fires on every new spelling regardless of language; the word list is
//! what makes the refusal say the right thing when the new flag is German.

use std::collections::BTreeSet;
use std::process::Command;

const WURZEL: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
const QUELLEN: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src");

// =======================================================================================
// The register
// =======================================================================================

/// One flag. `zweitname` is `""` where there never was a German spelling; `lebendig` is a
/// full argv at which the flag changes the run, and `&[]` where the entry is a single
/// spelling and therefore makes no equality claim that could go vacuous.
struct Fahne {
    erstname: &'static str,
    zweitname: &'static str,
    lebendig: &'static [&'static str],
}

const DATEI: &str = "beispiele/16-by-ops-am-feld.gab";

/// **Every flag spelling `crates/gabbro-cli/src/` accepts.**
///
/// The English first names came in on 2026-09-01, additively and on the path the
/// sub-commands took in `ERSTNAMEN.md`: **twelve German-only flags got an English first
/// name, and no German spelling was taken away.**
const FAHNEN: &[Fahne] = &[
    // --- the twelve that were German-only until 2026-09-01 -----------------------------
    Fahne {
        erstname: "--computed",
        zweitname: "--berechnet",
        // Only two of the 63 clean examples have a computed hull that differs from the
        // written one at all; on the other 61 this flag is invisible, and a liveness call
        // taken from them would have proved nothing.
        lebendig: &["abi", "--computed", "beispiele/29-undurchsichtig.gab"],
    },
    Fahne {
        erstname: "--compare",
        zweitname: "--vergleich",
        lebendig: &["abi", "--compare", DATEI],
    },
    Fahne {
        erstname: "--wide",
        zweitname: "--weit",
        // **`--wide` alone changes nothing on any of the 63 examples** -- it widens the
        // COMPARISON, so its liveness only exists next to `--compare`. Measured, not
        // assumed: 0 of 63 alone, 63 of 63 together.
        lebendig: &["abi", "--compare", "--wide", "beispiele/01-tabelle.gab"],
    },
    Fahne {
        erstname: "--total",
        zweitname: "--summe",
        lebendig: &["alias", "--total", DATEI],
    },
    Fahne {
        erstname: "--table",
        zweitname: "--tafel",
        lebendig: &["ceremony", "--table", DATEI],
    },
    Fahne {
        erstname: "--per-site",
        zweitname: "--je-stelle",
        lebendig: &["ceremony", "--per-site", DATEI],
    },
    Fahne {
        erstname: "--gate",
        zweitname: "--tor",
        lebendig: &["templates", "--gate"],
    },
    Fahne {
        erstname: "--per-statement",
        zweitname: "--je-satz",
        lebendig: &["passes", "--per-statement"],
    },
    Fahne {
        erstname: "--passes",
        zweitname: "--paesse",
        lebendig: &["check", "--passes", DATEI],
    },
    Fahne {
        erstname: "--origin",
        zweitname: "--ursprung",
        lebendig: &["effects", "--origin", DATEI],
    },
    Fahne {
        erstname: "--lock-rank",
        zweitname: "--sperrrang",
        lebendig: &["effects", "--lock-rank", DATEI],
    },
    Fahne {
        erstname: "--narrow",
        zweitname: "--eng",
        lebendig: &["effects", "--narrow", DATEI],
    },
    // --- the pairs that already had an English first name ------------------------------
    Fahne {
        erstname: "--unit",
        zweitname: "--einheit",
        // A single file IS its own unit, so `--unit` is invisible on one -- the flag is
        // about what happens when there are two.
        lebendig: &[
            "abi",
            "--unit",
            "beispiele/01-tabelle.gab",
            "beispiele/02-geraet.gab",
        ],
    },
    Fahne {
        erstname: "--dry-run",
        zweitname: "--trocken",
        // Without a manifest both spellings fail identically BEFORE the flag is read --
        // exactly the vacuous equality this file exists to refuse.
        lebendig: &["build", "--dry-run", "programmlogik/beispiel/gabbro.bau"],
    },
    Fahne {
        erstname: "--help",
        zweitname: "--hilfe",
        // Held next door by `hilfe_hat_auch_einen_englischen_erstnamen`, over all five
        // spellings at once; a second liveness call here would be the same claim twice.
        lebendig: &[],
    },
    // --- English from the start, no pair ------------------------------------------------
    Fahne {
        erstname: "--with",
        zweitname: "",
        lebendig: &[],
    },
    Fahne {
        erstname: "--testbuild",
        zweitname: "",
        lebendig: &[],
    },
    Fahne {
        erstname: "--isabelle",
        zweitname: "",
        lebendig: &[],
    },
    Fahne {
        erstname: "--lean",
        zweitname: "",
        lebendig: &[],
    },
    Fahne {
        // `fn` is the keyword in Gabbro AND in Rust; it is not a word of either natural
        // language, and there is nothing to translate.
        erstname: "--fn",
        zweitname: "",
        lebendig: &[],
    },
];

/// **Every sub-command arm of the dispatch, English name first.**
///
/// `erstnamen.rs` carries twelve pairs and drives them; this carries ALL arms, because the
/// question here is completeness against the source rather than behaviour.
///
/// > **Two pairs were missing from the hand-written list next door, and reading the source
/// > is what found them:** `effects|wirkungen` stands in no table in `ERSTNAMEN.md`, and
/// > `build|bau` was filed there under *"English from the start"* although `bau` is a German
/// > second name like any other. *A register maintained by hand drifts from the thing it
/// > registers; that is the whole reason this file reads `main.rs`.*
const UNTERBEFEHLE: &[&[&str]] = &[
    &["abi"],
    &["new"],
    &["check", "pruefe"],
    &["build", "bau"],
    &["emit"],
    &["fragments", "fragmente"],
    &["assumptions", "annahmen"],
    &["k-condition", "k-bedingung"],
    &["effects", "wirkungen"],
    &["costs", "kosten"],
    &["alias"],
    &["contexts", "kontexte"],
    &["obligations", "pflichten"],
    &["lean"],
    &["blindspots", "blindstellen"],
    &["certificate", "zeugnis"],
    &["ceremony", "zeremonie"],
    &["templates", "schablonen"],
    &["passes", "paesse"],
    &["--help", "help", "--hilfe", "-h", "hilfe"],
];

// =======================================================================================
// The German word list -- it obliges, it does not acquit (W10)
// =======================================================================================

/// **A closed list of German words, checked against the parts of a first name.**
///
/// A word that is ALSO English stays out, for the reason `pruefe-englisch.py` gives about
/// its own list: a detector that runs on English text must not contain English words.
/// Kept out for exactly that: `alt`, `gross`, `lang`, `mit`, `name`, `art`, `rang` -- each
/// of them is a word in both languages.
const DEUTSCH: &[&str] = &[
    // the twelve second names this tree carries, part by part
    "berechnet", "vergleich", "weit", "eng", "summe", "tafel", "tor", "je", "satz", "stelle",
    "paesse", "ursprung", "sperrrang", "einheit", "trocken", "hilfe",
    // the sub-command second names
    "pruefe", "pruefen", "bau", "bedingung", "wirkungen", "kosten", "kontexte", "pflichten",
    "blindstellen", "zeugnis", "zeremonie", "schablonen", "annahmen", "fragmente",
    // what a next flag would plausibly reach for
    "alle", "jede", "jeder", "jedes", "ohne", "nur", "auch", "und", "oder", "nicht", "kein",
    "voll", "kurz", "neu", "leise", "laut", "ganz", "mehr", "teil", "schritt", "stufe", "weg",
    "ziel", "quelle", "menge", "tiefe", "breite", "hoehe", "anzahl", "zahl", "zahlen",
    "datei", "dateien", "zeile", "zeilen", "wort", "woerter", "wortschatz", "ausgabe",
    "eingabe", "fehler", "warnung", "absage", "absagen", "grund", "gruende", "regel",
    "regeln", "probe", "proben", "lauf", "messung", "messungen", "waechter", "abnahme",
    "zaehle", "zaehler", "erst", "zweit", "deutsch", "englisch", "schranke", "bereich",
    "traeger", "sicht", "farbe", "breit", "schmal",
];

/// The German word in a flag or command spelling, if the closed list knows one.
fn deutsches_wort(name: &str) -> Option<&'static str> {
    let rumpf = name.trim_start_matches('-');
    for teil in rumpf.split('-') {
        for d in DEUTSCH {
            if teil == *d {
                return Some(d);
            }
        }
    }
    None
}

// =======================================================================================
// Reading the SOURCE -- not a list
// =======================================================================================

/// Every quoted literal in a line, in order.
fn zitate(zeile: &str) -> Vec<String> {
    let mut aus = Vec::new();
    let b = zeile.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'"' {
            let mut j = i + 1;
            while j < b.len() && b[j] != b'"' {
                // a `\"` inside a literal does not end it
                if b[j] == b'\\' {
                    j += 1;
                }
                j += 1;
            }
            if j >= b.len() {
                break;
            }
            aus.push(zeile[i + 1..j].to_string());
            i = j + 1;
        } else {
            i += 1;
        }
    }
    aus
}

/// **Every `--flag` spelling a source text COMPARES against.**
///
/// Comment lines are skipped: they quote flags as examples, and an example is not an
/// acceptance site. A literal that is not all lower-case ASCII and `-` is not a flag.
fn fahnen_in(text: &str) -> BTreeSet<String> {
    let mut aus = BTreeSet::new();
    for zeile in text.lines() {
        let t = zeile.trim_start();
        if t.starts_with("//") {
            continue;
        }
        for z in zitate(zeile) {
            if z.len() > 2
                && z.starts_with("--")
                && z[2..]
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c == '-' || c.is_ascii_digit())
            {
                aus.insert(z);
            }
        }
    }
    aus
}

/// The whole flag surface of the CLI. **The source list is a PATTERN, not an enumeration** --
/// a new file under `src/` is in on the day it is created, for the reason
/// `pruefe-englisch.py` gives after its own list was eight files short.
fn fahnen_der_quelle() -> BTreeSet<String> {
    let mut aus = BTreeSet::new();
    let mut gesehen = 0usize;
    for eintrag in std::fs::read_dir(QUELLEN).expect("crates/gabbro-cli/src is readable") {
        let pfad = eintrag.expect("directory entry").path();
        if pfad.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        gesehen += 1;
        let text = std::fs::read_to_string(&pfad).expect("source is readable");
        aus.extend(fahnen_in(&text));
    }
    assert!(
        gesehen >= 3,
        "the CLI has at least three sources; {gesehen} means the pattern read the wrong place \
         and every check below would be vacuously green"
    );
    aus
}

/// **The dispatch arms of `main`, read out of `main.rs`.**
///
/// Each entry is one arm's spellings in source order, so the FIRST one is the first name.
fn unterbefehle_in(text: &str) -> Vec<Vec<String>> {
    let mut aus = Vec::new();
    let mut drin = false;
    for zeile in text.lines() {
        if zeile.contains("match befehl.as_str() {") {
            drin = true;
            continue;
        }
        if !drin {
            continue;
        }
        if zeile.starts_with("        anderes =>") {
            break;
        }
        if !zeile.starts_with("        \"") {
            continue;
        }
        let Some(pfeil) = zeile.find("=>") else {
            continue;
        };
        let namen = zitate(&zeile[..pfeil]);
        if !namen.is_empty() {
            aus.push(namen);
        }
    }
    aus
}

fn unterbefehle_der_quelle() -> Vec<Vec<String>> {
    let text = std::fs::read_to_string(format!("{QUELLEN}/main.rs")).expect("main.rs is readable");
    let aus = unterbefehle_in(&text);
    assert!(
        aus.len() >= 15,
        "the dispatch has at least fifteen arms; {} means the scan lost the match and every \
         check below would be vacuously green",
        aus.len()
    );
    aus
}

fn lauf(argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(WURZEL)
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

// =======================================================================================
// 1 -- completeness: the ratchet
// =======================================================================================

/// **A flag in the source and not in the register turns this red -- in any language.**
///
/// This is the layer that actually closes the hole `ERSTNAMEN.md` §5 named. It does not ask
/// whether the new flag is German; it asks whether anybody decided. *A new flag costs one
/// line in `FAHNEN`, and that line is where the English first name gets written down.*
#[test]
fn jede_fahne_der_quelle_steht_im_register() {
    let register: BTreeSet<String> = FAHNEN
        .iter()
        .flat_map(|f| {
            [f.erstname, f.zweitname]
                .into_iter()
                .filter(|s| !s.is_empty())
                .map(String::from)
        })
        .collect();
    let quelle = fahnen_der_quelle();

    let unbekannt: Vec<&String> = quelle.difference(&register).collect();
    assert!(
        unbekannt.is_empty(),
        "these flags are accepted by the CLI and stand in no register: {unbekannt:?}\n\
         Add them to `FAHNEN` in this file, ENGLISH FIRST NAME first. The German spelling \
         goes in `zweitname` and keeps working; it does not replace the English one."
    );

    let tot: Vec<&String> = register.difference(&quelle).collect();
    assert!(
        tot.is_empty(),
        "these flags stand in the register and in no source: {tot:?}\n\
         A register that outlives its subject is the failure this file exists to prevent."
    );
}

/// The same completeness rule for the sub-commands -- **the thirteenth one, which
/// `erstnamen.rs` cannot hold.**
#[test]
fn jeder_unterbefehl_der_quelle_steht_im_register() {
    let register: BTreeSet<Vec<String>> = UNTERBEFEHLE
        .iter()
        .map(|a| a.iter().map(|s| s.to_string()).collect())
        .collect();
    let quelle: BTreeSet<Vec<String>> = unterbefehle_der_quelle().into_iter().collect();

    let unbekannt: Vec<&Vec<String>> = quelle.difference(&register).collect();
    assert!(
        unbekannt.is_empty(),
        "these dispatch arms stand in no register: {unbekannt:?}\n\
         Add them to `UNTERBEFEHLE`, ENGLISH FIRST NAME first -- and if the pair is a real \
         pair, add it to `PAARE` in `erstnamen.rs` too, so both spellings get DRIVEN."
    );
    let tot: Vec<&Vec<String>> = register.difference(&quelle).collect();
    assert!(
        tot.is_empty(),
        "these arms stand in the register and no longer in `main.rs`: {tot:?}"
    );
}

// =======================================================================================
// 2 -- the first name is English
// =======================================================================================

#[test]
fn kein_erstname_traegt_ein_deutsches_wort() {
    let mut schlecht = Vec::new();
    for f in FAHNEN {
        if let Some(d) = deutsches_wort(f.erstname) {
            schlecht.push(format!("{} (German word `{d}`)", f.erstname));
        }
    }
    for arm in UNTERBEFEHLE {
        if let Some(d) = deutsches_wort(arm[0]) {
            schlecht.push(format!("{} (German word `{d}`)", arm[0]));
        }
    }
    assert!(
        schlecht.is_empty(),
        "a FIRST name is English; these are not: {schlecht:?}\n\
         Give it an English first name and move this spelling to the second-name column."
    );
}

/// **And the counter-direction, held mechanically rather than remembered.**
///
/// A guardian that has never been seen to fire is a guardian nobody has measured. Both
/// layers are fed a source text that does not exist in the tree, and both have to refuse it.
#[test]
fn der_waechter_feuert_auf_eine_neue_deutsche_fahne() {
    // Layer 1: completeness. A new German-only flag in a source is not in the register.
    let erfunden = r#"
        let zaehler = rest.iter().any(|a| a == "--zaehler");
        let ohne = rest.iter().any(|a| a == "--je-datei");
    "#;
    let gefunden = fahnen_in(erfunden);
    let register: BTreeSet<String> = FAHNEN
        .iter()
        .flat_map(|f| {
            [f.erstname, f.zweitname]
                .into_iter()
                .filter(|s| !s.is_empty())
                .map(String::from)
        })
        .collect();
    let neu: Vec<&String> = gefunden.difference(&register).collect();
    assert_eq!(
        neu.len(),
        2,
        "a new flag has to reach the completeness layer as UNKNOWN: {neu:?}"
    );

    // Layer 2: the word list names the reason.
    assert_eq!(deutsches_wort("--zaehler"), Some("zaehler"));
    assert_eq!(deutsches_wort("--je-datei"), Some("je"));

    // And the same two layers stay SILENT on the names this tree actually carries.
    for f in FAHNEN {
        assert_eq!(
            deutsches_wort(f.erstname),
            None,
            "`{}` is a first name of this tree and must not be flagged",
            f.erstname
        );
    }

    // Layer 1 fires on a new ENGLISH flag too, and that is deliberate: the register is the
    // place where somebody decides. It costs one line and it is never silent drift.
    assert_eq!(
        fahnen_in(r#"a == "--verbose""#)
            .difference(&register)
            .count(),
        1
    );
}

/// The dispatch scan has to see a new arm as well -- the thirteenth sub-command.
#[test]
fn der_waechter_feuert_auf_einen_neuen_deutschen_unterbefehl() {
    // A raw string, and the eight-space indent is load-bearing: the scan reads the arms of
    // ONE match by their indentation, so a fixture that loses it would test nothing.
    let erfunden = r#"
    match befehl.as_str() {
        "zaehle" => befehl_zaehle(rest),
        "summary" | "uebersicht" => befehl_uebersicht(rest),
        anderes => {
"#;
    let arme = unterbefehle_in(erfunden);
    assert_eq!(arme, vec![vec!["zaehle"], vec!["summary", "uebersicht"]]);
    assert_eq!(deutsches_wort(&arme[0][0]), Some("zaehle"));
    // and a German-only arm whose FIRST name is English passes layer 2, as it should
    assert_eq!(deutsches_wort(&arme[1][0]), None);
}

// =======================================================================================
// 3 + 4 -- equivalence, and the liveness floor underneath it
// =======================================================================================

/// **Both spellings are ONE flag -- and the flag is READ.**
///
/// The second half is the whole point. `gabbro` does not refuse an unknown flag: `abi`
/// filters the ones it knows and treats the rest as file names, `ceremony` drops everything
/// starting with `--`. So a misspelled English first name is silently ignored, its German
/// partner is silently ignored, and the two produce identical output. **Equality without
/// liveness would call that a pass.**
#[test]
fn jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname() {
    for f in FAHNEN {
        if f.zweitname.is_empty() || f.lebendig.is_empty() {
            continue;
        }
        assert!(
            f.lebendig.contains(&f.erstname),
            "the liveness call for `{}` has to CONTAIN it",
            f.erstname
        );

        let mit_englisch: Vec<&str> = f.lebendig.to_vec();
        let mit_deutsch: Vec<&str> = f
            .lebendig
            .iter()
            .map(|a| if *a == f.erstname { f.zweitname } else { *a })
            .collect();
        let ohne: Vec<&str> = f
            .lebendig
            .iter()
            .copied()
            .filter(|a| *a != f.erstname)
            .collect();

        let a = lauf(&mit_englisch);
        let b = lauf(&mit_deutsch);
        let bare = lauf(&ohne);

        assert_eq!(
            a, b,
            "`{}` and `{}` are one flag, in stdout, stderr and exit code",
            f.erstname, f.zweitname
        );
        assert_ne!(
            a, bare,
            "`{}` has to CHANGE the run at {:?} -- otherwise the equality above is two \
             ignored spellings agreeing with each other, and proves nothing",
            f.erstname, f.lebendig
        );
    }
}

/// **The two pairs `PAARE` never drove.**
///
/// `jeder_unterbefehl_der_quelle_steht_im_register` proves they EXIST; it does not prove the
/// two spellings do the same thing. `erstnamen.rs` drives twelve pairs and these are not
/// among them -- `effects|wirkungen` stands in no table at all, and `build|bau` was filed
/// under "English from the start". **So until today nothing measured that `gabbro wirkungen`
/// and `gabbro effects` are one command.**
///
/// They are not simply added to `PAARE` next door because that list drives every pair with
/// ONE call shape, and `build` needs a manifest: `gabbro build <file.gab>` exits 2 for both
/// spellings, which is the vacuous agreement `PAARE`'s own `assert_ne!(a.2, 2)` exists to
/// refuse. *A pair that only agrees on how it fails has not been measured.*
#[test]
fn die_zwei_paare_die_erstnamen_rs_nicht_faehrt_tun_dasselbe() {
    const OFFEN: &[(&[&str], &[&str])] = &[
        (&["effects", DATEI], &["wirkungen", DATEI]),
        (
            &["build", "--dry-run", "programmlogik/beispiel/gabbro.bau"],
            &["bau", "--dry-run", "programmlogik/beispiel/gabbro.bau"],
        ),
    ];
    for (englisch, deutsch) in OFFEN {
        let a = lauf(englisch);
        let b = lauf(deutsch);
        assert_eq!(
            a, b,
            "`{englisch:?}` and `{deutsch:?}` are one command, in stdout, stderr and exit code"
        );
        assert_ne!(
            a.2, 2,
            "`{englisch:?}` is a KNOWN call -- exit 2 would mean both spellings fell into the \
             unknown arm, and two identical refusals prove nothing"
        );
    }
}

/// **The rule stands in the help, not only in this file.**
///
/// A user does not read the test suite. `ERSTNAMEN.md` §5 booked *"the help is the only
/// place the rule stands"* as a weakness of the sub-command half; for the flags the help
/// carries it too, and now a guardian carries it as well.
#[test]
fn die_hilfe_nennt_die_fahnenregel() {
    let (_, hilfe, _) = lauf(&["help"]);
    assert!(
        hilfe.contains("Every subcommand AND every flag has an ENGLISH first name"),
        "the rule itself is written where a user reads it:\n{hilfe}"
    );
    for f in FAHNEN {
        if f.zweitname.is_empty() || f.lebendig.is_empty() {
            continue;
        }
        assert!(
            hilfe.contains(f.zweitname),
            "`{}` keeps working and the help says so -- a second name nobody can find is a \
             second name that has quietly been dropped",
            f.zweitname
        );
    }
}
