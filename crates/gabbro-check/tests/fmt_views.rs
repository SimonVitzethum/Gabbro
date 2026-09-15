//! **Lane 197: `fmt --explicit` / `--elide` are pure views.**
//!
//! Lever 3 of `dokumente/PLAN-EINFACHHEIT.md`: explicitness as a view, not a
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

fn emit(quelle: &str, name: &str) -> (String, Vec<String>) {
    let (baum, mut absagen) = gabbro_syntax::lies(name, quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    (c, abdruck(&absagen))
}

#[test]
fn ansichten_sind_rein() {
    let mut angenommen = 0usize;
    let mut abgelehnt = 0usize;
    let mut befunde: Vec<String> = Vec::new();
    // The corpus-wide count of what `--elide` would remove (and `--explicit`
    // would write): summed over every accepted file, printed below. This is
    // the §0-adjacent number of PLAN-EINFACHHEIT lever 3 — how much ceremony
    // the views carry.
    let mut weg_effects = 0usize;
    let mut weg_costs = 0usize;
    let mut hinzu_effects = 0usize;
    let mut hinzu_costs = 0usize;
    for pfad in korpus() {
        let quelle = std::fs::read_to_string(&pfad).unwrap();
        let name = pfad.display().to_string();
        let (baum, mut absagen) = gabbro_syntax::lies(&name, &quelle);
        let bericht = gabbro_check::pruefe(&baum, &mut absagen);
        if absagen.fehler_zahl() > 0 {
            abgelehnt += 1;
            continue;
        }
        angenommen += 1;
        let vor = abdruck(&absagen);
        let m1_vor = (bericht.m1.gesamt(), bericht.m1.unbekannt);
        let exp = gabbro_check::fmt::explicit(&baum, &quelle);
        let eli = gabbro_check::fmt::elide(&baum, &quelle);
        {
            let mut z = gabbro_check::fmt::Zaehlung::default();
            gabbro_check::fmt::plane_elide(&baum, &quelle, &mut z);
            weg_effects += z.effects_weg;
            weg_costs += z.costs_weg;
            let mut ze = gabbro_check::fmt::Zaehlung::default();
            gabbro_check::fmt::plane_explicit(&baum, &quelle, &mut ze);
            hinzu_effects += ze.effects_hinzu;
            hinzu_costs += ze.costs_hinzu;
        }
        let (bericht_exp, nach_exp) = pruefe(&exp, &name);
        let (bericht_eli, nach_eli) = pruefe(&eli, &name);
        if vor != nach_exp {
            befunde.push(format!("{name}: EXPLICIT moves diagnostics"));
        }
        if vor != nach_eli {
            befunde.push(format!("{name}: ELIDE moves diagnostics"));
        }
        if m1_vor != (bericht_exp.m1.gesamt(), bericht_exp.m1.unbekannt) {
            befunde.push(format!("{name}: EXPLICIT moves M1 coverage"));
        }
        if m1_vor != (bericht_eli.m1.gesamt(), bericht_eli.m1.unbekannt) {
            befunde.push(format!("{name}: ELIDE moves M1 coverage"));
        }
        // The round trip closes both ways, byte-identical.
        let (baum_exp, _) = gabbro_syntax::lies(&name, &exp);
        let (baum_eli, _) = gabbro_syntax::lies(&name, &eli);
        let eli_exp = gabbro_check::fmt::elide(&baum_exp, &exp);
        let exp_eli = gabbro_check::fmt::explicit(&baum_eli, &eli);
        if eli_exp != eli {
            befunde.push(format!("{name}: elide(explicit(F)) != elide(F)"));
        }
        if exp_eli != exp {
            befunde.push(format!("{name}: explicit(elide(F)) != explicit(F)"));
        }
        // Byte-identical emitted C (with the emit diagnostics it stands on).
        let c_vor = emit(&quelle, &name);
        let c_exp = emit(&exp, &name);
        let c_eli = emit(&eli, &name);
        if c_vor != c_exp {
            befunde.push(format!("{name}: EXPLICIT moves emission"));
        }
        if c_vor != c_eli {
            befunde.push(format!("{name}: ELIDE moves emission"));
        }
    }
    for b in &befunde {
        println!("FMT-BEFUND: {b}");
    }
    println!("FMT: {angenommen} accepted, {abgelehnt} refused, {} findings", befunde.len());
    println!(
        "FMT-ZAEHLUNG over {angenommen} accepted files: --elide would remove \
         {weg_effects} effects + {weg_costs} costs clauses; --explicit would write \
         {hinzu_effects} effects + {hinzu_costs} costs clauses"
    );
    assert!(befunde.is_empty(), "{} findings:\n{}", befunde.len(), befunde.join("\n"));
}
