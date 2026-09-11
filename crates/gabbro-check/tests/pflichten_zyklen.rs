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
