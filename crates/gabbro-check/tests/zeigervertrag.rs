//! **Function-pointer types are signatures (2026-10-21).**
//!
//! In the Lean model a pointer type is STRUCTURAL: a function fits where its own signature
//! conforms (`Deklaration.passt`, `SigPasst`), and the model's signatures carry no contract.
//! The checker holds the same line:
//!
//! * an indirect call passes exactly the TYPE's arguments -- `N296`;
//! * a `requires` (a `Held(..)` included) or an `ensures` at the type is refused -- `N589`;
//! * a function that requires a held lock is no pointer value -- `N590`;
//! * effects `⊆`, costs `<=`, arity and signature stay DECIDED (`M128`/`M141`/`M142`).
//!
//! The contract on pointer types that lane 177 carried (and counted as kind `C`) is gone
//! with it: TODO O43 names the contravariant/covariant model it would need first.

use gabbro_syntax::diag::Stufe;
use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
}

fn lies(datei: &str) -> (String, gabbro_syntax::ast::Programm, gabbro_syntax::diag::Absagen) {
    let pfad = wurzel().join(datei);
    let quelle = std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()));
    let name = pfad.display().to_string();
    let (baum, mut absagen) = gabbro_syntax::lies(&name, &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    (quelle, baum, absagen)
}

fn fehler(absagen: &gabbro_syntax::diag::Absagen) -> Vec<&'static str> {
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

fn hinweise(absagen: &gabbro_syntax::diag::Absagen) -> Vec<&'static str> {
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Hinweis)
        .map(|a| a.code)
        .collect()
}

fn pflichten(
    quelle: &str,
    baum: &gabbro_syntax::ast::Programm,
    name: &str,
) -> String {
    let (bericht, vollstaendig) = gabbro_check::pflichten::zeige(baum, name, quelle);
    assert!(vollstaendig, "E1 gefallen:\n{bericht}");
    bericht
}

/// **A contract at the pointer type is refused at the clause** -- `requires`, `ensures` and
/// `requires Held(..)`, one `N589` each and nothing beside it (the file-level gift run only
/// asserts the code FIRES; purity is held HERE).
#[test]
fn vertrag_am_zeigertyp_wird_abgelehnt() {
    for datei in [
        "gift/247-fnzeiger-mit-requires.gab",
        "gift/248-fnzeiger-mit-ensures.gab",
        "gift/1483-fnzeiger-mit-held.gab",
    ] {
        let (_, _, absagen) = lies(datei);
        assert_eq!(fehler(&absagen), ["N589"], "{datei} must fall exactly once with N589");
    }
}

/// **The arity of an indirect call is the slot's.** Exactly one `N296`.
#[test]
fn indirekter_ruf_haelt_stelligkeit_des_typs() {
    let (_, _, absagen) = lies("gift/959-indirect-call-wrong-arity.gab");
    assert_eq!(fehler(&absagen), ["N296"], "959 must fall exactly once with N296");
}

/// **A function that requires a held lock is no pointer value** -- `N590` at `&schreibe`.
#[test]
fn funktion_mit_held_ist_kein_zeigerwert() {
    let (_, _, absagen) = lies("gift/1484-fnwert-mit-held.gab");
    assert_eq!(fehler(&absagen), ["N590"], "1484 must fall exactly once with N590");
}

/// **The positive sides: a comparator and a driver callback through their slots**, clean,
/// with no hint and no contract-refinement line in `gabbro obligations`.
#[test]
fn zeigertypen_ohne_vertrag_gehen_durch() {
    for datei in ["126-vergleichssortierung.gab", "127-treiberrueckruf.gab"] {
        let (quelle, baum, absagen) = lies(datei);
        assert!(fehler(&absagen).is_empty(), "{datei}:\n{}", absagen.zeige(&quelle));
        assert!(hinweise(&absagen).is_empty(), "{datei}: hints {:?}", hinweise(&absagen));
        let bericht = pflichten(&quelle, &baum, datei);
        assert!(!bericht.contains("\tC\t"), "{datei}: a contract-refinement line:\n{bericht}");
    }
}
