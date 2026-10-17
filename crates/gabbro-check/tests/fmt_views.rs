//! **Lane 197: `fmt --explicit` / `--elide` are pure views.**
//!
//! Lever 3 of `dokumente/PRUEFER.md`: explicitness as a view, not a
//! storage format. For every corpus file the checker accepts, `pruefe(F)`,
//! `pruefe(explicit(F))` and `pruefe(elide(F))` give the same diagnostics
//! (codes, levels and texts — spans excluded, the views move bytes), the same
//! M1 coverage numbers and byte-identical emitted C; and the round trip closes
//! both ways (`elide(explicit(F)) == elide(F)`, `explicit(elide(F)) ==
//! explicit(F)`).
//!
//! What the comparison deliberately excludes: byte spans (insertions move
//! them), the rendered line numbers beside them, and fix spans (same reason;
//! the replacement texts compare). What it deliberately includes: every code,
//! every level, every message text and note, every fix replacement, the M1
//! pair and the C bytes.
//!
//! `FMT_ONLY=<substring>` restricts the run to matching file names (triage;
//! the gate runs the whole corpus).

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn korpus() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for (ordner, tief) in [("beispiele", false), ("beispiele/gift", false), ("messung/fragmente", false)] {
        let d = wurzel().join(ordner);
        let mut dateien: Vec<PathBuf> = std::fs::read_dir(&d)
            .unwrap_or_else(|e| panic!("{}: {e}", d.display()))
            .flatten()
            .map(|e| e.path())
            .filter(|p| {
                p.extension().and_then(|s| s.to_str()) == Some("gab")
                    && (!tief || p.is_file())
            })
            .collect();
        dateien.sort();
        out.extend(dateien);
    }
    if let Ok(nur) = std::env::var("FMT_ONLY") {
        out.retain(|p| p.to_string_lossy().contains(&nur));
    }
    assert!(!out.is_empty(), "kein Korpus gefunden");
    out
}

/// Span-insensitive fingerprint of a diagnostic run.
fn abdruck(a: &gabbro_syntax::diag::Absagen) -> Vec<String> {
    let mut v: Vec<String> = a
        .absagen
        .iter()
        .map(|x| {
            let stufe = match x.stufe {
                Stufe::Fehler => "E",
                Stufe::Hinweis => "H",
            };
            let fix = x
                .fix
                .as_ref()
                .map(|f| format!(" fix-> {}", f.replacement))
                .unwrap_or_default();
            format!("{}:{}:{}{}\n  {}", stufe, x.code, x.text, fix, x.notizen.join("\n  "))
        })
        .collect();
    v.sort();
    v
}

fn pruefe(quelle: &str, name: &str) -> (gabbro_check::Bericht, Vec<String>) {
    let (baum, mut absagen) = gabbro_syntax::lies(name, quelle);
    let bericht = gabbro_check::pruefe(&baum, &mut absagen);
    (bericht, abdruck(&absagen))
}

