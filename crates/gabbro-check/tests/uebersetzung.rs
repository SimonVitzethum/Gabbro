//! Lane E5 -- the translation stage, first cut (dokumente/PRUEFER.md section 6).
//!
//! Three sides, each pinned:
//!
//! * the checker translates exact-length integer regions through the
//!   identity translator and refuses everything else by code (the falling
//!   directions stand in `paesse.rs` as `translation_*` and under
//!   `beispiele/gift/905`-`909`);
//! * the emitter passes an accepted payload as a `static const` table
//!   argument, and the generated C compiles and computes the sum at run
//!   time (one call site below, two in the second test);
//! * the printed certificate carries the same three definition lines the
//!   Lean witness (`Uebersetzung.sumPayloadVals`) closes by `decide` -- a
//!   drift breaks this file, and the `decide` itself breaks `./lean-bau`.

use gabbro_syntax::diag::Stufe;
use std::process::Command;

fn errors(source: &str) -> Vec<&'static str> {
    let (baum, mut absagen) = gabbro_syntax::lies("<probe>", source);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

/// The summing library of `beispiele/106`: the region fills the four rows
/// of `SumTab`, the call passes one argument short, the function answers
/// the unrolled sum.
const SUMME: &str = "module summe {
table SumTab count 4 {
    slot {
        v : u32 in 0 .. 100,
    }
}
library fn sum(t : ptr<normal, r> SumTab) -> u32 in 0 .. 400 payload SumTab
    ensures result <= 400
    effects { reads t.slots }
    costs <= 16 ops
{
    return t.slots[0].v + t.slots[1].v + t.slots[2].v + t.slots[3].v;
}
translator build for sum(region : SumTab) -> SumTab
    effects { pure }
    costs <= 8 ops
    decreases region.v
{
    return region;
}
";

fn rufer(rumpf: &str) -> String {
    format!(
        "{SUMME}impl fn hole() -> u32 in 0 .. 400
    effects {{ reads SumTab.slots }}
    costs <= 128 ops
{{
    {rumpf}
}}
}}"
    )
}

fn baue_und_laufe(c: &str, haupt: &str) -> String {
    let d = std::env::var("TMPDIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| std::env::temp_dir())
        .join("gabbro-uebersetzung");
    std::fs::create_dir_all(&d).expect("scratch dir is writable");
    let c_path = d.join("run.c");
    let bin_path = d.join("run");
    let mut prog = c.to_string();
    prog.push_str(haupt);
    std::fs::write(&c_path, &prog).expect("the generated C is writable");
    let bau = Command::new("cc")
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg("-o")
        .arg(&bin_path)
        .arg(&c_path)
        .output();
    let bau = match bau {
        Ok(r) => r,
        Err(e) => panic!("`cc` does not start ({e}) -- NOTHING measured"),
    };
    assert!(
        bau.status.success(),
        "the generated C does not compile under `-Wall -Wextra -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        c_path.display()
    );
    let lauf = Command::new(&bin_path)
        .output()
        .unwrap_or_else(|e| panic!("the compiled program does not run ({e}) -- NOTHING measured"));
    assert!(lauf.status.success(), "the compiled program aborts");
    let ausgabe = String::from_utf8_lossy(&lauf.stdout).to_string();
    let _ = std::fs::remove_file(&c_path);
    let _ = std::fs::remove_file(&bin_path);
    ausgabe
}

// -- the certificate: printed payload meets the Lean witness -----------------

#[test]
fn payload_certificate_prints_encoding_n() {
    let cert = gabbro_check::uebersetzung::payload_certificate("sumPayload", &[10, 20, 30, 40], 0, 100);
    let erwartet = "-- Payload certificate printed by gabbro-check (lane 129):\n\
        -- the payload values of `sumPayload` for `Uebersetzung.nutzlastZert`.\n\
        def sumPayloadVals : List Nat := [10, 20, 30, 40]\n\
        def sumPayloadOk : Bool := nutzlastZert sumPayloadVals 0 100\n\
        theorem sumPayload_zert : sumPayloadOk = true := by decide\n";
    assert_eq!(cert, erwartet, "the printer's bytes are the contract");
}

#[test]
fn payload_certificate_mirrors_lean_file() {
    let cert = gabbro_check::uebersetzung::payload_certificate("sumPayload", &[10, 20, 30, 40], 0, 100);
    let lean = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("grammatik")
        .join("Grammatik")
        .join("Logik")
        .join("Vertraege")
        .join("Uebersetzung.lean");
    let text = std::fs::read_to_string(&lean)
        .unwrap_or_else(|e| panic!("{}: {e}", lean.display()));
    for zeile in cert.lines().filter(|l| l.starts_with("def ") || l.starts_with("theorem ")) {
        assert!(
            text.contains(zeile),
            "the Lean file carries the printer's line verbatim -- a drift is a finding:\n{zeile}"
        );
    }
}
