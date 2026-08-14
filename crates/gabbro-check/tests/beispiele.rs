//! **Der Beispielkorpus, in beide Richtungen.**
//!
//! `beispiele/*.gab` muss **sauber** durchgehen -- das ist die eine Richtung, und sie faellt,
//! sobald eine Regel enger wird, als die Sprache es sagt.
//!
//! `beispiele/gift/*.gab` muss **fallen**, und zwar mit dem Code, der in der ersten Zeile der
//! Datei steht (`-- erwartet: M104`). Das ist die andere Richtung, und sie faellt, sobald eine
//! Regel weiter wird oder eine Absage heimlich ihre Bedeutung wechselt.
//!
//! Ein Pruefer, der nicht fehlschlagen kann, ist kein Pruefer -- und ein Korpus, der nur aus
//! sauberen Faellen besteht, ist kein Korpus.

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

fn dateien(unterordner: Option<&str>) -> Vec<PathBuf> {
    let d = match unterordner {
        Some(u) => wurzel().join(u),
        None => wurzel(),
    };
    let mut out: Vec<PathBuf> = std::fs::read_dir(&d)
        .unwrap_or_else(|e| panic!("{}: {e}", d.display()))
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("gab"))
        .collect();
    out.sort();
    assert!(!out.is_empty(), "{}: keine Beispiele", d.display());
    out
}

fn absagen_von(pfad: &Path) -> (Vec<(&'static str, Stufe)>, String, String) {
    let quelle = std::fs::read_to_string(pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let name = pfad
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("?")
        .to_string();
    let (baum, mut absagen) = gabbro_syntax::lies(&name, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let codes = absagen
        .absagen
        .iter()
        .map(|a| (a.code, a.stufe))
        .collect();
    (codes, absagen.zeige(&quelle), name)
}

#[test]
fn jedes_beispiel_geht_sauber_durch() {
    for pfad in dateien(None) {
        let (codes, bericht, name) = absagen_von(&pfad);
        let fehler: Vec<&str> = codes
            .iter()
            .filter(|(_, s)| *s == Stufe::Fehler)
            .map(|(c, _)| *c)
            .collect();
        assert!(
            fehler.is_empty(),
            "{name} ist ein Beispiel und faellt mit {fehler:?}:\n{bericht}"
        );
    }
}

#[test]
fn jedes_gift_faellt_mit_seinem_code() {
    for pfad in dateien(Some("gift")) {
        let quelle =
            std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
        let erwartet = quelle
            .lines()
            .next()
            .and_then(|z| z.strip_prefix("-- erwartet: "))
            .unwrap_or_else(|| {
                panic!(
                    "{}: die erste Zeile muss `-- erwartet: CODE` sein",
                    pfad.display()
                )
            })
            .trim()
            .to_string();
        let (codes, bericht, name) = absagen_von(&pfad);
        let gefallen: Vec<&str> = codes
            .iter()
            .filter(|(_, s)| *s == Stufe::Fehler)
            .map(|(c, _)| *c)
            .collect();
        assert!(
            gefallen.contains(&erwartet.as_str()),
            "{name} sollte mit {erwartet} fallen, gefallen ist {gefallen:?}:\n{bericht}"
        );
    }
}

/// Sprechprobe ueber dem Korpus selbst: es muss beide Sorten geben.
#[test]
fn der_korpus_hat_beide_richtungen() {
    assert!(
        dateien(None).len() >= 5,
        "zu wenige saubere Beispiele -- ein Korpus aus drei Dateien misst nichts"
    );
    assert!(
        dateien(Some("gift")).len() >= 5,
        "zu wenige Gifte -- ein Korpus ohne Gegenprobe belohnt einen stummen Pruefer"
    );
}
