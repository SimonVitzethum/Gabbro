//! **S4 -- the seam witnesses** (`dokumente/PLAN-SICHERHEIT.md` §4).
//!
//! `gabbro_check::lean::witness` writes one `checker_agrees` theorem per carried routine,
//! holding the duty datum against `pruefe`. These tests pin the EMISSION (fast, no Lean
//! run): that the theorem, the program and the `by decide` are there, and that loop
//! variables are bound (adapter A1) with their scope replayed into `schleife`.
//!
//! The corpus measurement itself is the ignored driver below: it emits every
//! `beispiele/*.gab` into `/tmp/seam/` with the Rust verdict beside it, and a shell loop
//! runs `lake env lean` per file. The agreement table lives in the plan paragraph, not
//! here -- a number in two places is a number that drifts.

use gabbro_check::lean::witness;

const PROBE: &str = r#"
module seam::probe {
table K count 4 {
    slot { x : u32, }
}
impl fn setze(i : index into K, v : u32)
    effects { writes K.slots }
{
    K.slots[i].x = v;
}
}
"#;

const SCHLEIFE: &str = r#"
module seam::schleife {
table W count 8 {
    slot { aktiv : bool, }
}
impl fn alle_aus()
    effects { writes W.slots }
{
    traverse i over slots of W by unvisited
        touches writes W.slots
    {
        W.slots[i].aktiv = false;
    }
}
}
"#;

fn baum_von(quelle: &str) -> gabbro_syntax::ast::Programm {
    let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    baum
}

/// The witness names its theorem, its program and its decision procedure -- and the
/// `@seam` line adds up (routines = witnesses + skipped).
#[test]
fn witness_names_theorem_and_program() {
    let w = witness(&baum_von(PROBE), "probe.gab");
    assert!(w.contains("import Gabbro.Sicherheit.Anweisung"), "no Sicherheit import:\n{w}");
    assert!(
        w.contains("theorem checker_agrees_setze"),
        "no witness theorem:\n{w}"
    );
    assert!(w.contains("pruefeBlock seamP_setze"), "no pruefeBlock goal:\n{w}");
    assert!(w.contains(":= by decide"), "no `by decide`:\n{w}");
    assert!(w.contains("def seamSig"), "no shared signatures:\n{w}");
    assert!(w.contains("def seamD_setze : Deklaration"), "no declarations:\n{w}");
    assert!(w.contains("-- @seam 1 routines 1 witnesses 0 skipped"), "no balance line:\n{w}");
}

/// Adapter A1: the loop variable is bound at the routine's entry, and the scope it
/// stands in is replayed into `schleife` -- otherwise `pruefe` cannot see the variable
/// at all and every loop routine refuses.
#[test]
fn witness_binds_loop_variables() {
    let w = witness(&baum_von(SCHLEIFE), "probe.gab");
    assert!(
        w.contains("theorem checker_agrees_alle_aus"),
        "no witness theorem:\n{w}"
    );
    assert!(
        w.contains("(.bindName \"i\" (.lit (.int 0)))"),
        "A1 binding missing:\n{w}"
    );
    assert!(w.contains("seamLoops_alle_aus"), "no loop registry:\n{w}");
    // The replayed entry scope names the variable with its point shape.
    assert!(w.contains("(\"i\", .form (.intIn 0 0))"), "replayed scope missing `i`:\n{w}");
}

/// The corpus driver: emits every `beispiele/*.gab` into `/tmp/seam/` and prints the
/// Rust verdict beside the witness count. The Lean half runs in a shell loop
/// (`lake env lean` per file, under `timeout`); joining both is the S4 measurement.
/// Ignored: it writes files and takes minutes -- run it for the measurement, not in CI.
#[test]
#[ignore]
fn emit_corpus() {
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..");
    // `SEAM_SRC` overrides the source dir (relative to the workspace root) for probes
    // outside the corpus; `SEAM_OUT` overrides the output dir. Both default to the
    // corpus measurement.
    let src = std::env::var("SEAM_SRC").unwrap_or_else(|_| "beispiele".to_string());
    let out = std::env::var("SEAM_OUT").unwrap_or_else(|_| "/tmp/seam".to_string());
    let ziel = std::path::Path::new(&out);
    std::fs::create_dir_all(ziel).unwrap();
    let mut dateien: Vec<_> = std::fs::read_dir(wurzel.join(src))
        .unwrap()
        .filter_map(|e| e.ok().map(|x| x.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "gab"))
        .collect();
    dateien.sort();
    assert!(!dateien.is_empty(), "no corpus files");
    for pfad in dateien {
        let datei = pfad.file_name().unwrap().to_string_lossy().to_string();
        let quelle = std::fs::read_to_string(&pfad).unwrap();
        let (baum, mut absagen) = gabbro_syntax::lies(&datei, &quelle);
        let _ = gabbro_check::pruefe(&baum, &mut absagen);
        let rust = if absagen.fehler_zahl() == 0 { "accept" } else { "refuse" };
        let w = witness(&baum, &pfad.display().to_string());
        let theoreme = w.matches("theorem checker_agrees_").count();
        let seamdatei = format!("Seam{}.lean", gabbro_check::lean::module_name(&datei).trim_start_matches("Duty"));
        std::fs::write(ziel.join(&seamdatei), &w).unwrap();
        println!("{datei}\trust={rust}\ttheorems={theoreme}\t{seamdatei}");
    }
}
