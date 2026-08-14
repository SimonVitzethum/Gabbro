//! **Die zwei Regeln, unter denen dieser Uebersetzer ueberhaupt etwas wert ist** -- geprueft,
//! nicht zugesagt.
//!
//! `README.md`: *„In sicherem Rust, `#![forbid(unsafe_code)]`, ohne Abhaengigkeiten ausserhalb
//! einer benannten Liste — dieselbe Regel, die Caprock für seine Handler-Module durchsetzt. Ein
//! Erzeuger, der selbst ausbrechen kann, macht die Eigenschaft seines Erzeugnisses wertlos."*
//!
//! Eine Regel, die in einer Datei steht und die niemand prueft, ist eine Absichtserklaerung.
//! Diese hier faellt, wenn jemand `forbid` zu `deny` macht, `[lints] workspace = true` in einer
//! Kiste vergisst oder die erste fremde Abhaengigkeit eintraegt.

use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn kisten() -> Vec<PathBuf> {
    let mut out = Vec::new();
    let crates = wurzel().join("crates");
    for e in std::fs::read_dir(&crates).expect("crates/ ist lesbar") {
        let p = e.expect("Eintrag lesbar").path();
        if p.join("Cargo.toml").is_file() {
            out.push(p);
        }
    }
    out.sort();
    assert!(!out.is_empty(), "keine Kiste gefunden");
    out
}

#[test]
fn unsafe_ist_verboten_und_zwar_forbid() {
    let ws = std::fs::read_to_string(wurzel().join("Cargo.toml")).expect("Arbeitsbereich");
    assert!(
        ws.contains(r#"unsafe_code = "forbid""#),
        "der Arbeitsbereich muss `unsafe_code = \"forbid\"` fuehren -- `deny` ist \
         abschaltbar, `forbid` nicht"
    );
    for k in kisten() {
        let toml = std::fs::read_to_string(k.join("Cargo.toml")).expect("Cargo.toml");
        assert!(
            toml.contains("[lints]") && toml.contains("workspace = true"),
            "{}: ohne `[lints] workspace = true` gilt das Verbot fuer diese Kiste nicht",
            k.display()
        );
    }
}

#[test]
fn keine_abhaengigkeit_ausserhalb_der_liste() {
    // Die benannte Liste ist heute leer: std und die eigenen Kisten, sonst nichts.
    // Waechst sie, gehoert der Eintrag hierher -- und damit in eine Begruendung.
    const ERLAUBT: &[&str] = &["gabbro-syntax", "gabbro-check"];

    for k in kisten() {
        let toml = std::fs::read_to_string(k.join("Cargo.toml")).expect("Cargo.toml");
        let Some(anfang) = toml.find("[dependencies]") else {
            continue;
        };
        let abschnitt = &toml[anfang + "[dependencies]".len()..];
        let abschnitt = abschnitt.split("\n[").next().unwrap_or(abschnitt);
        for zeile in abschnitt.lines() {
            let zeile = zeile.trim();
            if zeile.is_empty() || zeile.starts_with('#') {
                continue;
            }
            let name = zeile.split(['=', ' ']).next().unwrap_or("").trim();
            assert!(
                ERLAUBT.contains(&name),
                "{}: Abhaengigkeit `{name}` steht nicht auf der benannten Liste",
                k.display()
            );
            assert!(
                zeile.contains("path ="),
                "{}: `{name}` kommt nicht aus dem Arbeitsbereich",
                k.display()
            );
        }
    }
}

#[test]
fn kein_selbst_hosting() {
    // Verbotsliste in SYNTAX.md: *Selbst-Hosting*. Ein Erzeuger, der sich selbst uebersetzt,
    // verliert seinen unabhaengigen Pruefer -- die Kisten bleiben Rust.
    for k in kisten() {
        let src = k.join("src");
        let mut halde = vec![src];
        while let Some(d) = halde.pop() {
            let Ok(eintraege) = std::fs::read_dir(&d) else {
                continue;
            };
            for e in eintraege.flatten() {
                let p = e.path();
                if p.is_dir() {
                    halde.push(p);
                } else {
                    assert_ne!(
                        p.extension().and_then(|s| s.to_str()),
                        Some("gab"),
                        "{}: der Uebersetzer traegt Gabbro-Quelltext",
                        p.display()
                    );
                }
            }
        }
    }
}
