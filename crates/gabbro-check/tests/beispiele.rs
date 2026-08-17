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

/// **K100.4: das Zeugnis muss alles verbuchen, was der Erzeuger absenkt.**
///
/// Das ist die Kreuzprobe, um derentwillen die Einordnung in `zeugnis.rs` **unabhaengig** von
/// der `match`-Kaskade des Erzeugers gefuehrt wird. Zwei Lesungen derselben Datei, und sie
/// muessen sich decken:
///
/// * **Der Erzeuger senkt ab** → das Zeugnis muss die Form kennen.
/// * **Der Erzeuger weigert sich** (`C001`) → dann gibt es kein C, und die Weigerung steht
///   schon da; `UNZUGEORDNET` ist dort erwartbar und kein Befund.
///
/// > *Eine Vertrauensflaeche, die nur der Erzeuger kennt, ist keine gebuchte.*
///
/// **Beim ersten Lauf fand diese Probe sofort etwas:** `lock` senkt zu vier Prototypen ab
/// (`beispiele/10`, `/13` uebersetzen damit sauber), und die Einordnung kannte die Form nicht.
/// Daraus wurde die Klasse `Fremd` — *der Erzeuger schreibt den Prototyp, den Rumpf schreibt
/// jemand anderes*, und das ist weder direkt noch erzeugt.
#[test]
fn was_der_erzeuger_absenkt_steht_im_zeugnis() {
    let mut ohne_buchung = Vec::new();
    let mut emittiert = 0;
    for p in dateien(None) {
        let quelle = std::fs::read_to_string(&p).unwrap();
        let (baum, mut absagen) = gabbro_syntax::lies(&p.display().to_string(), &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
        if absagen.fehler_zahl() > 0 {
            // Der Erzeuger weigert sich -- die Weigerung steht da, das Zeugnis schuldet nichts.
            continue;
        }
        emittiert += 1;
        let e = gabbro_check::zeugnis::erhebe(&baum);
        if !e.unzugeordnet.is_empty() {
            let mut u = e.unzugeordnet.clone();
            u.sort();
            u.dedup();
            ohne_buchung.push(format!("{}: {}", p.display(), u.join(", ")));
        }
    }
    assert!(
        emittiert >= 6,
        "die Probe misst nur, wenn ueberhaupt etwas emittiert -- {emittiert} Dateien"
    );
    assert!(
        ohne_buchung.is_empty(),
        "der Erzeuger senkt Formen ab, die das Zeugnis nicht einordnet:\n  {}",
        ohne_buchung.join("\n  ")
    );
}

/// **Und die Gegenrichtung: das Zeugnis muss melden koennen.**
///
/// Eine Kreuzprobe, die nicht rot werden kann, misst nichts (R14). Hier steht darum eine Form,
/// die der Erzeuger **nicht** kennt und die Einordnung ebenfalls nicht — sie MUSS als
/// `UNZUGEORDNET` herausfallen.
#[test]
fn das_zeugnis_meldet_was_es_nicht_einordnen_kann() {
    let q = "module t { table A count 4 { slot { a : u32, } } \
             table B count 4 { slot { b : u32, } } \
             group G over { A, B } { invariant beides cost O(n) runs offline : \
             forall i in slots of A : A.slots[i].a >= B.slots[i].b; } }";
    let (baum, a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let e = gabbro_check::zeugnis::erhebe(&baum);
    assert!(
        e.unzugeordnet.iter().any(|u| u.contains("group")),
        "eine Form, die niemand eingeordnet hat, muss auffallen: {:?}",
        e.unzugeordnet
    );

    // **Und eine Ebene tiefer, denn die Buchung hat zwei Ebenen.** Ein Item, das durchfaellt,
    // und eine ANWEISUNG, die durchfaellt, sind zwei verschiedene Auffangzweige — und die
    // Probe oben deckte nur den ersten.
    let mit_anweisung = "module t { table A count 4 { slot { a : u32, } invariant p : true; } \
                         impl fn f(x : ptr<normal, rw> A) -> bool effects { writes x } \
                         costs <= 4 ops { breaking p { return true; } } }";
    let (baum_a, _) = gabbro_syntax::lies("p.gab", mit_anweisung);
    assert!(
        gabbro_check::zeugnis::erhebe(&baum_a)
            .unzugeordnet
            .iter()
            .any(|u| u.contains("breaking")),
        "auch eine ANWEISUNG ohne Einordnung muss auffallen"
    );

    // Und eine Datei, die vollstaendig gebucht ist, meldet NICHTS -- sonst waere die Probe
    // oben durch eine dauerrote Zeile erfuellt.
    let sauber = "module t { type P = { a : u32, b : bool, }; \
                  impl fn f() -> P effects { pure } costs <= 4 ops { return P(a: 1, b: true); } }";
    let (baum2, _) = gabbro_syntax::lies("p.gab", sauber);
    assert!(
        gabbro_check::zeugnis::erhebe(&baum2).unzugeordnet.is_empty(),
        "eine vollstaendig gebuchte Datei meldet nichts"
    );
}
