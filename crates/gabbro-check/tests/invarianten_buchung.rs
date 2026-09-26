//! **`N496` in both directions, over snippets** (Opus agent D, OFFEN O11).
//!
//! The file half of the probes is `beispiele/gift/1231`-`1234`; what stands here pins the
//! rule over snippets -- poison and positive twin side by side, so a rule that goes silent
//! fails here, and a rule that starts refusing the booked form fails here too.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("invarianten_buchung", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::invarianten_buchung {\n\
    table W count 8 {\n\
        slot { a : u32 in 0 .. 10, }\n\
        invariant klein cost O(n) runs offline :\n\
            forall s in slots of W : W.slots[s].a <= 5;\n\
    }\n";

fn einheit(extra: &str) -> String {
    format!("{KOPF}{extra}}}\n")
}

fn schreiber(name: &str, maintains: &str) -> String {
    format!(
        "impl fn {name}(i : index into W)\n    {maintains}\n    \
         effects {{ reads W.slots, writes W.slots }}\n    costs <= 64 ops\n{{\n    \
         W.slots[i].a = 0;\n}}\n"
    )
}

#[test]
fn ein_schreiber_ohne_maintains_faellt() {
    let codes = fehler(&einheit(&schreiber("leeren", "")));
    assert!(codes.contains(&"N496".to_string()), "N496 expected, got {codes:?}");
}

#[test]
fn ein_schreiber_mit_maintains_ist_gebucht() {
    let codes = fehler(&einheit(&schreiber("leeren", "maintains klein")));
    assert!(codes.is_empty(), "the booked writer must check clean, got {codes:?}");
}

#[test]
fn ein_leser_schuldet_nichts() {
    let codes = fehler(&einheit(
        "impl fn lesen(i : index into W) -> u32\n    effects { reads W.slots }\n    \
         costs <= 8 ops\n{\n    return W.slots[i].a;\n}\n",
    ));
    assert!(codes.is_empty(), "a reader owes no invariant, got {codes:?}");
}

#[test]
fn der_rufer_eines_schreibers_schuldet_mit() {
    let ohne = format!(
        "{}impl fn aussen(i : index into W)\n    effects {{ reads W.slots, writes W.slots }}\n    \
         costs <= 128 ops\n{{\n    setzen(i);\n}}\n",
        schreiber("setzen", "maintains klein")
    );
    let mit = format!(
        "{}impl fn aussen(i : index into W)\n    maintains klein\n    \
         effects {{ reads W.slots, writes W.slots }}\n    costs <= 128 ops\n{{\n    setzen(i);\n}}\n",
        schreiber("setzen", "maintains klein")
    );
    assert!(fehler(&einheit(&ohne)).contains(&"N496".to_string()));
    let codes = fehler(&einheit(&mit));
    assert!(codes.is_empty(), "both writers booked must check clean, got {codes:?}");
}

/// **The two corpus programs the rule reached, repaired and clean.**
#[test]
fn die_korpusprogramme_sind_gebucht() {
    for datei in ["09-ohne-zeiger.gab", "17-gruppe-ueber-zwei-sperren.gab"] {
        let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../beispiele")
            .join(datei);
        let quelle = std::fs::read_to_string(&pfad).unwrap();
        let codes = fehler(&quelle);
        assert!(codes.is_empty(), "{datei} must check clean, got {codes:?}");
    }
}
