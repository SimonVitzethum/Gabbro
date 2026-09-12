//! **Contract footprint (E220/E221) in both directions.**
//!
//! The poet's half of the gift probes: `beispiele/gift/895-896/898` pin the fall
//! over files, what stands here pins it over snippets -- poison and positive twin
//! side by side, so a rule that goes silent fails here even where the gift corpus
//! has no file for the shape.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("vertragsfuss", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::vertragsfuss {\n\
    static mut z : u32 = 0;\n\
    static mut frei : u32 = 0;\n";

fn einheit(vertrag: &str, wirkungen: &str, rumpf: &str) -> String {
    format!(
        "{KOPF}\
        impl fn ziel() -> u32\n\
            {vertrag}\n\
            effects {{ {wirkungen} }}\n\
            costs   <= 8 ops\n\
        {{\n\
            {rumpf}\n\
        }}\n\
        impl fn schreibt() effects {{ writes z }} costs <= 8 ops {{ z = 1; }}\n\
        }}\n"
    )
}

#[test]
fn requires_ohne_deckung_faellt() {
    let codes = fehler(&einheit("requires z == 0", "pure", "return 0;"));
    assert!(
        codes.iter().any(|c| c == "E220"),
        "uncovered `requires` over a written carrier must fall with E220: {codes:?}"
    );
}

#[test]
fn requires_mit_reads_deckung_schweigt() {
    let codes = fehler(&einheit("requires z == 0", "reads z", "return z;"));
    assert!(
        codes.is_empty(),
        "covered `requires` must stay silent: {codes:?}"
    );
}

#[test]
fn requires_ueber_unbeschriebenem_traeger_schweigt() {
    // `frei` is never written by any function: read-only needs no cover.
    let codes = fehler(&einheit("requires frei == 0", "pure", "return 0;"));
    assert!(
        codes.is_empty(),
        "read-only carrier needs no cover: {codes:?}"
    );
}

#[test]
fn ensures_ohne_deckung_faellt() {
    let codes = fehler(&einheit("ensures result == z", "pure", "return 0;"));
    assert!(
        codes.iter().any(|c| c == "E221"),
        "uncovered `ensures` over a written carrier must fall with E221: {codes:?}"
    );
}

#[test]
fn ensures_mit_writes_deckung_schweigt() {
    // The body writes without reading back, so no E010 joins in: this pins the
    // E221 silence of a `writes`-only cover exactly.
    let codes = fehler(&einheit(
        "ensures result == z",
        "writes z",
        "z = 41; return 0;",
    ));
    assert!(
        codes.is_empty(),
        "`writes` covers a contract read as well: {codes:?}"
    );
}

#[test]
fn fester_zeuge_ist_kein_lesen() {
    // `Has(z)` names a capability, not a read -- the predicate-word prune.
    // Without it this would fall with E220 (`z` is written, nothing covers it).
    let codes = fehler(&einheit("requires Has(z)", "pure", "return 0;"));
    assert!(
        codes.is_empty(),
        "a predicate word names no carrier read: {codes:?}"
    );
}
