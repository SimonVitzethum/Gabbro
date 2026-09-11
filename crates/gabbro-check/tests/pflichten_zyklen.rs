//! **H022 cycle tests live here, not in `pflichten.rs`.**
//!
//! The kennungen guardian counts one code per file (`K008` in `kosten.rs`
//! already): an inline `#[cfg(test)]` module asserting on `K008` findings
//! would double-assign the code. Tests NAME codes, only source files ASSIGN
//! them -- so this module moved here verbatim on 2026-09-11, with `super::*`
//! replaced by explicit imports and nothing else touched.

use gabbro_check::pflichten::{h022_weigerung, zyklen_ohne_mass, H022, Zyklenluecke};
use gabbro_syntax::diag::Stufe;

const WECHSELRUF: &str = "module gift::wechselruf {\n\
    static mut a : u32 = 0;\n\
    impl fn ping(n : u32) -> u32 effects { writes a } costs <= 8 ops\n\
    { a = n; if n == 0 { return 0; } return pong(n); }\n\
    impl fn pong(n : u32) -> u32 effects { writes a } costs <= 8 ops\n\
    { a = n; if n == 0 { return 0; } return ping(n); }\n\
    }\n";

const HALBES_MASS: &str = "module gift::halbes_mass {\n\
    static mut a : u32 = 0;\n\
    impl fn ping(n : u32) -> u32 effects { writes a } costs <= 8 ops decreases n\n\
    { a = n; if n == 0 { return 0; } return pong(n - 1); }\n\
    impl fn pong(n : u32) -> u32 effects { writes a } costs <= 8 ops\n\
    { a = n; if n == 0 { return 0; } return ping(n - 1); }\n\
    }\n";

const VOLLES_MASS: &str = "module gift::volles_mass {\n\
    static mut a : u32 = 0;\n\
    impl fn ting(n : u32) -> u32 effects { writes a } costs <= 8 ops decreases n\n\
    { a = n; if n == 0 { return 0; } return tong(n - 1); }\n\
    impl fn tong(n : u32) -> u32 effects { writes a } costs <= 8 ops decreases n\n\
    { a = n; if n == 0 { return 0; } return ting(n - 1); }\n\
    }\n";

const KETTE: &str = "module gift::kette {\n\
    static mut a : u32 = 0;\n\
    impl fn f(n : u32) -> u32 effects { writes a } costs <= 8 ops\n\
    { a = n; if n == 0 { return 0; } return g(n); }\n\
    impl fn g(n : u32) -> u32 effects { writes a } costs <= 8 ops\n\
    { a = n; if n == 0 { return 0; } return n; }\n\
    }\n";

fn namen(l: &[Zyklenluecke]) -> Vec<&str> {
    l.iter().map(|x| x.funktion.as_str()).collect()
}

#[test]
fn h022_findet_beide_glieder_des_wechselrufs() {
    let (baum, _) = gabbro_syntax::lies("h022-wechselruf", WECHSELRUF);
    assert_eq!(namen(&zyklen_ohne_mass(&baum)), ["ping", "pong"]);
}

#[test]
fn h022_halbes_mass_nennt_nur_das_blosse_glied() {
    let (baum, _) = gabbro_syntax::lies("h022-halbes-mass", HALBES_MASS);
    assert_eq!(namen(&zyklen_ohne_mass(&baum)), ["pong"]);
}

#[test]
fn h022_schweigt_mit_mass_und_ohne_zyklus() {
    let (voll, _) = gabbro_syntax::lies("h022-volles-mass", VOLLES_MASS);
    assert!(zyklen_ohne_mass(&voll).is_empty());
    let (kette, _) = gabbro_syntax::lies("h022-kette", KETTE);
    assert!(zyklen_ohne_mass(&kette).is_empty());
}

#[test]
fn h022_weigerung_tragt_code_stufe_und_glied() {
    let (baum, _) = gabbro_syntax::lies("h022-halbes-mass", HALBES_MASS);
    let l = zyklen_ohne_mass(&baum);
    assert_eq!(l.len(), 1);
    let w = h022_weigerung(&l[0]);
    assert_eq!(w.code, H022);
    assert!(matches!(w.stufe, Stufe::Fehler));
    assert!(w.text.contains("pong"));
}

/// **The twin through the pipeline stays silent** -- the shape `gift/747` carries
/// in-file. Measured 2026-09-11 over the same bodies: zero `Fehler`.
#[test]
fn h022_zwilling_bleibt_still() {
    let (baum, mut absagen) = gabbro_syntax::lies("h022-volles-mass", VOLLES_MASS);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| matches!(a.stufe, Stufe::Fehler))
        .map(|a| a.code)
        .collect();
    assert!(fehler.is_empty(), "twin fell with {fehler:?}");
}

/// **The bare cycle through the pipeline falls with `K008` on each member** -- what
/// `gift/746` asserts file by file, here per member.
#[test]
fn h022_wechselruf_faellt_je_glied_mit_k008() {
    let (baum, mut absagen) = gabbro_syntax::lies("h022-wechselruf", WECHSELRUF);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let k008 = absagen
        .absagen
        .iter()
        .filter(|a| matches!(a.stufe, Stufe::Fehler) && a.code == "K008")
        .count();
    assert_eq!(k008, 2, "bare cycle fell with {k008} K008, not 2");
}

/// **Gift-file probe readings live here, not in `beispiele.rs`.**
///
/// The file-level gift run only asserts the expected code FIRES, so the exact
/// multiset per file (no `K009` beside it, `K001` where the cost pass owes it)
/// is held HERE -- the same split as `h020_silence_and_single_fire_738` in
/// `beispiele.rs`, kept in the topic file per the one-file rule.
fn gift_wurzel() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
        .join("gift")
}

fn fehler_ueber_datei(datei: &str) -> (String, String, Vec<&'static str>) {
    let pfad = gift_wurzel().join(datei);
    let quelle =
        std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let (baum, mut absagen) = gabbro_syntax::lies(datei, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let mut fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| matches!(a.stufe, Stufe::Fehler))
        .map(|a| a.code)
        .collect();
    fehler.sort();
    let bericht = absagen.zeige(&quelle);
    (quelle, bericht, fehler)
}

/// **Probe 774: the self-cycle draws exactly `H022` + `K001` + `K008`.**
///
/// No gift probe pinned `H022` on the length-one cycle before: `gift/150` predates
/// the wiring and asserts `K008` only (a presence claim, still green). The detector
/// names the single bare member; the pipeline adds nothing past the triple.
/// `K001` belongs to it structurally: the self-call counts the DECLARED `costs`,
/// so a bare member always exceeds its own promise (`kosten.rs`: a recursive call
/// costs nothing only under `decreases`).
#[test]
fn h022_self_cycle_falls_exactly_with_h022_k001_and_k008() {
    let datei = "774-selbstruf-ohne-mass.gab";
    let pfad = gift_wurzel().join(datei);
    let quelle =
        std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let (baum, _) = gabbro_syntax::lies(datei, &quelle);
    assert_eq!(namen(&zyklen_ohne_mass(&baum)), ["f"]);
    let (_, bericht, fehler) = fehler_ueber_datei(datei);
    assert_eq!(
        fehler,
        ["H022", "K001", "K008"],
        "{datei} must fall exactly once with each, fell with {fehler:?}:\n{bericht}"
    );
}

/// **Probe 775: the half-measured three-cycle names only the two bare members.**
///
/// Extends the `gift/747` premise (half a measure is no measure on the cycle) from
/// length two to length three: `f` carries and lowers `decreases n`, so neither
/// `K008` nor `K009` touches it (and its cycle calls cost nothing, so no `K001`
/// either), while `g` and `h` each draw the triple.
#[test]
fn h022_half_measured_three_cycle_names_only_bare_members() {
    let datei = "775-dreierzyklus-halbes-mass.gab";
    let pfad = gift_wurzel().join(datei);
    let quelle =
        std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let (baum, _) = gabbro_syntax::lies(datei, &quelle);
    assert_eq!(namen(&zyklen_ohne_mass(&baum)), ["g", "h"]);
    let (_, bericht, fehler) = fehler_ueber_datei(datei);
    assert_eq!(
        fehler,
        ["H022", "H022", "K001", "K001", "K008", "K008"],
        "{datei} must fall exactly twice with each, fell with {fehler:?}:\n{bericht}"
    );
}
