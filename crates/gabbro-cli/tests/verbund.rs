//! **`gabbro link` over the probe files -- each unit clean ALONE, the pair refused by name.**
//!
//! Opus agent E, 2026-09-26. The probes live in `messung/proben/verbund/`: the positive pair
//! `tabelle-bib.gab` (a library with a lock-guarded table writer and its contract) and
//! `tabelle-app.gab` (two threads calling it), and five refusals, numbered from the gift range
//! reserved for this work (1241-1245). A link probe is TWO units, and each is accepted alone
//! -- that is the whole point of it -- so it cannot be a `beispiele/gift/` file: the gift
//! harness checks a file alone and expects it to fall. The first four refusals are STALE
//! INTERFACES (`.gabi`, the importer's view of the library as it was compiled); the fifth is an
//! app that states the library's hardware assumption differently.
//!
//! What every refusal probe holds, both halves:
//! * the importer checks CLEAN against its view (`gabbro check … --with …`, exit 0) -- the
//!   refusal is the link's and nobody else's;
//! * `gabbro link` falls with exactly the probe's code (`-- link-erwartet: N50x`), exit 1.

use std::path::PathBuf;
use std::process::Command;

fn wurzel() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn lauf(argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(wurzel())
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

const D: &str = "messung/proben/verbund";

/// The interface `gabbro abi` writes for the library NOW, in a per-test file under `target/`.
fn schnittstelle(name: &str) -> String {
    let (aus, fehler, code) = lauf(&["abi", &format!("{D}/tabelle-bib.gab")]);
    assert_eq!(code, 0, "the library has an interface:\n{fehler}");
    let dir = wurzel().join("target").join("verbund-proben");
    std::fs::create_dir_all(&dir).expect("target dir");
    let p = dir.join(format!("{name}.gabi"));
    std::fs::write(&p, aus).expect("write the interface");
    p.to_string_lossy().into_owned()
}

fn codes(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|z| z.strip_prefix("error: ["))
        .filter_map(|z| z.split(']').next())
        .map(str::to_string)
        .collect()
}

#[test]
fn die_tabelle_verbindet_sauber() {
    let gabi = schnittstelle("positiv");
    let (_, f1, c1) = lauf(&["check", &format!("{D}/tabelle-bib.gab")]);
    assert_eq!(c1, 0, "the library checks alone:\n{f1}");
    let (_, f2, c2) = lauf(&["check", "--with", &gabi, &format!("{D}/tabelle-app.gab")]);
    assert_eq!(c2, 0, "the app checks alone against the interface:\n{f2}");
    let (aus, fehler, code) = lauf(&[
        "link",
        "--with",
        &gabi,
        &format!("{D}/tabelle-bib.gab"),
        &format!("{D}/tabelle-app.gab"),
    ]);
    assert_eq!(code, 0, "the pair links:\n{aus}\n{fehler}");
    assert!(
        aus.contains("1 import(s) held against their bodies") && aus.contains("0 refusal(s)"),
        "the link really held the import:\n{aus}"
    );
    // The German second name is the same command.
    let (aus2, _, code2) = lauf(&[
        "verbinde",
        "--with",
        &gabi,
        &format!("{D}/tabelle-bib.gab"),
        &format!("{D}/tabelle-app.gab"),
    ]);
    assert_eq!((aus2, code2), (aus, code));
}

/// Every refusal probe: `(file, the importer, the interface it was checked with)`.
fn proben() -> Vec<(String, String, Option<String>)> {
    let mut aus = Vec::new();
    for e in std::fs::read_dir(wurzel().join(D)).expect("probe dir").flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        if !name.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            continue;
        }
        if name.ends_with(".gabi") {
            aus.push((name.clone(), format!("{D}/tabelle-app.gab"), Some(format!("{D}/{name}"))));
        } else if name.ends_with(".gab") {
            aus.push((name.clone(), format!("{D}/{name}"), None));
        }
    }
    aus.sort();
    aus
}

#[test]
fn jede_linkprobe_faellt_mit_ihrem_code_und_nur_am_link() {
    let proben = proben();
    let nummern: Vec<&str> = proben.iter().map(|(n, _, _)| &n[..4]).collect();
    assert_eq!(
        nummern,
        vec!["1241", "1242", "1243", "1244", "1245"],
        "the reserved probe numbers, each once"
    );
    let aktuell = schnittstelle("gift");
    for (name, app, gabi) in proben {
        let text_von = gabi.clone().unwrap_or_else(|| app.clone());
        let text = std::fs::read_to_string(wurzel().join(&text_von)).expect("probe readable");
        let erwartet = text
            .lines()
            .find_map(|z| z.strip_prefix("-- link-erwartet: "))
            .unwrap_or_else(|| panic!("{name}: no `-- link-erwartet:` line"))
            .trim()
            .to_string();
        let gabi = gabi.unwrap_or_else(|| aktuell.clone());
        let (_, f1, c1) = lauf(&["check", "--with", &gabi, &app]);
        assert_eq!(c1, 0, "{name}: the importer checks CLEAN alone:\n{f1}");
        let (aus, fehler, code) =
            lauf(&["link", "--with", &gabi, &format!("{D}/tabelle-bib.gab"), &app]);
        assert_eq!(code, 1, "{name}: the link refuses:\n{aus}\n{fehler}");
        assert_eq!(
            codes(&fehler),
            vec![erwartet.clone()],
            "{name}: exactly `{erwartet}`, nothing else:\n{fehler}"
        );
    }
}

#[test]
fn ein_link_ist_ein_paar() {
    let (_, fehler, code) = lauf(&["link", &format!("{D}/tabelle-bib.gab")]);
    assert_eq!(code, 1, "one unit is no link:\n{fehler}");
    assert!(fehler.contains("a link is a PAIR"), "{fehler}");
}
