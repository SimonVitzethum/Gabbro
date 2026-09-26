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
//! Opus agent F added 1246-1248, each a PAIR `NNNN-…-bib.gab` + `NNNN-…-app.gab`: the review-E
//! F1 reproduction (a read behind an imported head races), threads in both units that race
//! over the linked program, and a module split over two units (`N516`); plus two positive
//! twins (`rennen-bewacht-*`, `faeden-beide-*`).
//!
//! What every refusal probe holds, both halves:
//! * the library checks clean alone; the importer checks CLEAN against its view (`gabbro check
//!   … --with …`, exit 0) -- the refusal is the link's and nobody else's -- UNLESS the probe
//!   says `-- allein-erwartet: …`: 1246 is the F1 false accept, which now falls per unit
//!   already, with the codes the one-file program gets;
//! * `gabbro link` falls with exactly the probe's codes (`-- link-erwartet: …`), exit 1.

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

/// One refusal probe.
struct Probe {
    name: String,
    /// The exporting unit.
    bib: String,
    /// The importing unit.
    app: String,
    /// The interface the importer is checked with.
    gabi: Gabi,
    /// The file carrying the `-- link-erwartet:` line.
    erwartung: String,
}

enum Gabi {
    /// A stale interface on disk (probes 1241-1244).
    Datei(String),
    /// What `gabbro abi` writes for the library NOW.
    Frisch,
    /// None: the importer imports nothing (probe 1248).
    Keine,
}

/// Every refusal probe, by number. A `.gabi` is a stale view of `tabelle-bib.gab` for
/// `tabelle-app.gab`; an `NNNN-…-app.gab` is an importer, linked with the `NNNN-…-bib.gab`
/// of its number if there is one (Opus F) and with `tabelle-bib.gab` otherwise.
fn proben() -> Vec<Probe> {
    let mut dateien: Vec<String> = std::fs::read_dir(wurzel().join(D))
        .expect("probe dir")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.chars().next().is_some_and(|c| c.is_ascii_digit()))
        .collect();
    dateien.sort();
    let mut aus = Vec::new();
    for name in &dateien {
        if name.ends_with(".gabi") {
            aus.push(Probe {
                name: name.clone(),
                bib: format!("{D}/tabelle-bib.gab"),
                app: format!("{D}/tabelle-app.gab"),
                gabi: Gabi::Datei(format!("{D}/{name}")),
                erwartung: format!("{D}/{name}"),
            });
        } else if name.ends_with("-app.gab") {
            let bib = dateien
                .iter()
                .find(|b| b.ends_with("-bib.gab") && b[..4] == name[..4])
                .map(|b| format!("{D}/{b}"))
                .unwrap_or_else(|| format!("{D}/tabelle-bib.gab"));
            let text = std::fs::read_to_string(wurzel().join(D).join(name)).expect("readable");
            let gabi = if text.lines().any(|z| z.trim_start().starts_with("use ")) {
                Gabi::Frisch
            } else {
                Gabi::Keine
            };
            aus.push(Probe {
                name: name.clone(),
                bib,
                app: format!("{D}/{name}"),
                gabi,
                erwartung: format!("{D}/{name}"),
            });
        }
    }
    aus
}

/// The interface `gabbro abi` writes for ANY library now, in a per-test file under `target/`.
fn schnittstelle_von(bib: &str, name: &str) -> String {
    let (aus, fehler, code) = lauf(&["abi", bib]);
    assert_eq!(code, 0, "{bib} has an interface:\n{fehler}");
    let dir = wurzel().join("target").join("verbund-proben");
    std::fs::create_dir_all(&dir).expect("target dir");
    let p = dir.join(format!("{name}.gabi"));
    std::fs::write(&p, aus).expect("write the interface");
    p.to_string_lossy().into_owned()
}

fn zeile(text: &str, marke: &str) -> Vec<String> {
    let mut v: Vec<String> = text
        .lines()
        .find_map(|z| z.strip_prefix(marke))
        .map(|r| r.split_whitespace().map(str::to_string).collect())
        .unwrap_or_default();
    v.sort();
    v
}

fn sortiert(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

#[test]
fn jede_linkprobe_faellt_mit_ihrem_code_und_nur_am_link() {
    let proben = proben();
    let nummern: Vec<&str> = proben.iter().map(|p| &p.name[..4]).collect();
    assert_eq!(
        nummern,
        vec!["1241", "1242", "1243", "1244", "1245", "1246", "1247", "1248"],
        "the reserved probe numbers, each once"
    );
    for p in proben {
        let name = &p.name;
        let text = std::fs::read_to_string(wurzel().join(&p.erwartung)).expect("probe readable");
        let erwartet = zeile(&text, "-- link-erwartet: ");
        assert!(!erwartet.is_empty(), "{name}: no `-- link-erwartet:` line");
        let app_text = std::fs::read_to_string(wurzel().join(&p.app)).expect("app readable");
        let allein = zeile(&app_text, "-- allein-erwartet: ");
        let mit: Vec<String> = match &p.gabi {
            Gabi::Datei(g) => vec!["--with".into(), g.clone()],
            Gabi::Frisch => vec!["--with".into(), schnittstelle_von(&p.bib, &name[..4])],
            Gabi::Keine => vec![],
        };
        let (_, f0, c0) = lauf(&["check", &p.bib]);
        assert_eq!(c0, 0, "{name}: the library checks CLEAN alone:\n{f0}");
        let mut arg: Vec<&str> = vec!["check"];
        arg.extend(mit.iter().map(String::as_str));
        arg.push(&p.app);
        // `check` prints its refusals on stdout, `link` on stderr.
        let (a1, f1, c1) = lauf(&arg);
        let f1 = format!("{a1}{f1}");
        if allein.is_empty() {
            assert_eq!(c1, 0, "{name}: the importer checks CLEAN alone:\n{f1}");
        } else {
            // Review E F1 (probe 1246): the importer ALONE must now fall, with the codes the
            // same code gets in one file.
            assert_eq!(c1, 1, "{name}: the importer falls alone:\n{f1}");
            assert_eq!(sortiert(codes(&f1)), allein, "{name}: exactly {allein:?} alone:\n{f1}");
        }
        let mut arg: Vec<&str> = vec!["link"];
        arg.extend(mit.iter().map(String::as_str));
        arg.push(&p.bib);
        arg.push(&p.app);
        let (aus, fehler, code) = lauf(&arg);
        assert_eq!(code, 1, "{name}: the link refuses:\n{aus}\n{fehler}");
        assert_eq!(
            sortiert(codes(&fehler)),
            erwartet,
            "{name}: exactly {erwartet:?}, nothing else:\n{fehler}"
        );
    }
}

/// **The positive twins (Opus F):** the guarded read behind a head (twin of 1246) and threads
/// in both units that share nothing unguarded (twin of 1247) -- each unit clean alone, and
/// the pair links with the linked program checked whole.
#[test]
fn die_zwillinge_verbinden_sauber() {
    for paar in ["rennen-bewacht", "faeden-beide"] {
        let bib = format!("{D}/{paar}-bib.gab");
        let app = format!("{D}/{paar}-app.gab");
        let gabi = schnittstelle_von(&bib, paar);
        let (_, f1, c1) = lauf(&["check", &bib]);
        assert_eq!(c1, 0, "{paar}: the library checks alone:\n{f1}");
        let (_, f2, c2) = lauf(&["check", "--with", &gabi, &app]);
        assert_eq!(c2, 0, "{paar}: the app checks alone:\n{f2}");
        let (aus, fehler, code) = lauf(&["link", "--with", &gabi, &bib, &app]);
        assert_eq!(code, 0, "{paar}: the pair links:\n{aus}\n{fehler}");
        assert!(
            aus.contains("the linked program checked whole (0 error(s))")
                && aus.contains("0 refusal(s)"),
            "{paar}: the linked program was really checked:\n{aus}"
        );
    }
}

/// **`gabbro build a.gab b.gab` runs the link** (Opus F, OFFEN O28): the racing pair 1247
/// falls with the one-file codes, the twin passes, and the build says nothing was compiled.
#[test]
fn der_bau_aus_quelldateien_verbindet() {
    let (aus, fehler, code) = lauf(&[
        "build",
        &format!("{D}/1247-rennen-verbund-bib.gab"),
        &format!("{D}/1247-rennen-verbund-app.gab"),
    ]);
    assert_eq!(code, 1, "the racing pair does not build:\n{aus}\n{fehler}");
    assert_eq!(sortiert(codes(&fehler)), vec!["N291".to_string(), "N301".to_string()]);
    let (aus, fehler, code) = lauf(&[
        "build",
        &format!("{D}/faeden-beide-bib.gab"),
        &format!("{D}/faeden-beide-app.gab"),
    ]);
    assert_eq!(code, 0, "the twin builds:\n{aus}\n{fehler}");
    assert!(aus.contains("NOTHING was compiled"), "{aus}");
}

#[test]
fn ein_link_ist_ein_paar() {
    let (_, fehler, code) = lauf(&["link", &format!("{D}/tabelle-bib.gab")]);
    assert_eq!(code, 1, "one unit is no link:\n{fehler}");
    assert!(fehler.contains("a link is a PAIR"), "{fehler}");
}
