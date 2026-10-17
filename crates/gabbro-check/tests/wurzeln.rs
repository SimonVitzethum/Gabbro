//! **`R014` and `R015`, both directions of each** (`dokumente/A1-OWN-PAPER.md`, slices 1 and 3).
//!
//! `R014` refuses two pointer arguments of one call with a common ROOT when one callee
//! parameter is writable or `own`; a re-view (a function taking and answering a pointer)
//! borrows, so its answer has the root of its argument. `R015` is the boundary: a function
//! that ASSUMES two pointer parameters distinct and is entered from outside the unit says so.
//!
//! *A guard that only ever asserts a refusal is green for a rule pointing the wrong way*
//! (`tests/rechte.rs`), so every refusing row has a silent twin that differs in one place.

use gabbro_syntax::diag::Stufe;

const RAHMEN: &str = r#"module app::w {
type Kopf = { x : u32, };
type Worte = { w : u32, };
extern fn sicht(r : ptr<normal, r> Kopf) -> ptr<normal, r> Worte effects { reads r } costs <= 4 ops;
extern fn frisch() -> ptr<normal, rw> Worte effects { pure } costs <= 4 ops;
"#;

/// Codes of one stufe of `<RAHMEN><zusatz>}`, checker only.
fn codes(zusatz: &str, stufe: Stufe) -> Vec<String> {
    let quelle = format!("{RAHMEN}{zusatz}}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("wurzeln.gab", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == stufe)
        .map(|a| a.code.to_string())
        .collect()
}

/// A callee with one writable and one read-only pointer, and a caller that builds the second
/// argument by `<bindung>` from its own parameters `k` (writable) and `q` (read-only).
fn mit_bindung(bindung: &str, arg2: &str) -> String {
    format!(
        "impl fn ziel(a : ptr<normal, rw> Kopf, b : ptr<normal, r> Worte)\n\
         \x20   effects {{ writes a, reads b }} costs <= 8 ops {{ a.x = b.w; }}\n\
         impl fn ruft(k : ptr<normal, rw> Kopf, q : ptr<normal, r> Kopf)\n\
         \x20   effects {{ writes k, reads k, reads q }} costs <= 32 ops {{ {bindung} ziel(k, {arg2}); }}\n"
    )
}

#[test]
fn eine_sicht_auf_dieselbe_quelle_faellt() {
    let c = codes(&mit_bindung("let w = sicht(k);", "w"), Stufe::Fehler);
    assert_eq!(c, vec!["R014".to_string()], "{c:?}");
}

#[test]
fn eine_sicht_auf_eine_andere_quelle_bleibt_frei() {
    let c = codes(&mit_bindung("let w = sicht(q);", "w"), Stufe::Fehler);
    assert!(c.is_empty(), "{c:?}");
}

#[test]
fn eine_frische_antwort_hat_eine_eigene_wurzel() {
    let c = codes(&mit_bindung("let w = frisch();", "w"), Stufe::Fehler);
    assert!(c.is_empty(), "{c:?}");
}

#[test]
fn die_sicht_ueber_eine_kette_von_lets_behaelt_die_wurzel() {
    let c = codes(&mit_bindung("let v = sicht(k); let w = v;", "w"), Stufe::Fehler);
    assert_eq!(c, vec!["R014".to_string()], "{c:?}");
}

#[test]
fn zwei_lesende_sichten_derselben_quelle_bleiben_frei() {
    let zusatz = "impl fn lesen(a : ptr<normal, r> Kopf, b : ptr<normal, r> Worte)\n\
                  \x20   effects { reads a, reads b } costs <= 8 ops { }\n\
                  impl fn ruft(k : ptr<normal, r> Kopf)\n\
                  \x20   effects { reads k } costs <= 32 ops { let w = sicht(k); lesen(k, w); }\n";
    let c = codes(zusatz, Stufe::Fehler);
    assert!(c.is_empty(), "{c:?}");
}

#[test]
fn die_grenze_wird_an_der_nicht_gerufenen_funktion_genannt_und_nur_dort() {
    // `ziel` has a writable and a read-only pointer and IS called inside the module by `ruft`
    // (the call is held by `R014`); `ruft` has two pointer parameters, one writable, and is
    // called by nobody -- so exactly one boundary hint, and it stands at `ruft`.
    let h = codes(&mit_bindung("let w = frisch();", "w"), Stufe::Hinweis);
    assert_eq!(h.iter().filter(|c| *c == "R015").count(), 1, "{h:?}");
}

#[test]
fn zwei_lesende_zeiger_brauchen_keine_getrenntheit_und_nennen_keine_grenze() {
    let zusatz = "impl fn lesen(a : ptr<normal, r> Kopf, b : ptr<normal, r> Worte)\n\
                  \x20   effects { reads a, reads b } costs <= 8 ops { }\n";
    let h = codes(zusatz, Stufe::Hinweis);
    assert!(h.iter().all(|c| c != "R015"), "{h:?}");
}
