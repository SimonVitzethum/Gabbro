//! Machine-applicable repairs (lane 187, lever 4 of `dokumente/PLAN-EINFACHHEIT.md`).
//!
//! Every diagnostic that carries a fix is applied to its gift probe (or, where no gift
//! probe fires the code, to a minimal inline source), and the result is re-checked: the
//! expected code is gone, so the file either checks or reaches the next, DIFFERENT
//! diagnostic. What the tests never assert is silence -- a fix that merely quieted the
//! refusal would pass a weaker test, and that is exactly what lane 187 refuses to build.
//!
//! No new gift files: the probes below are the ones the corpus already carries, opened
//! read-only. The three inline sources cover the three codes no gift probe fires
//! (`E003`, `L001`, `L004`), plus the `E002` shape whose gift probe exercises the arm
//! that must stay manual.

use gabbro_syntax::diag::{Absagen, Stufe};
use std::path::{Path, PathBuf};

fn giftwurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("beispiele")
        .join("gift")
}

fn gift(datei: &str) -> String {
    std::fs::read_to_string(giftwurzel().join(datei))
        .unwrap_or_else(|e| panic!("{datei}: {e}"))
}

fn fehler(absagen: &Absagen) -> Vec<&'static str> {
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect()
}

fn alle(absagen: &Absagen) -> Vec<&'static str> {
    absagen.absagen.iter().map(|a| a.code).collect()
}

/// Apply the fixes to the named gift probe: the expected code fires before (or the
/// probe drifted and the test says so), at least one fix is applied, and afterwards
/// the expected code fires no more -- clean or a different diagnostic.
fn gift_repariert(datei: &str, erwartet: &'static str) {
    let q = gift(datei);
    let (baum0, mut vor) = gabbro_syntax::lies(datei, &q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(
        alle(&vor).contains(&erwartet),
        "{datei}: `{erwartet}` no longer fires before the fix -- the probe drifted"
    );
    assert!(
        vor.absagen
            .iter()
            .any(|a| a.code == erwartet && a.fix.is_some()),
        "{datei}: `{erwartet}` fires but carries no fix"
    );
    let (neu, nach, n) = gabbro_check::fix::fix_to_stable(datei, &q, 10);
    assert!(n > 0, "{datei}: no fix applied for `{erwartet}`");
    let rest = fehler(&nach);
    assert!(
        !rest.contains(&erwartet),
        "{datei}: `{erwartet}` still fires after --fix, over:\n{neu}\nleft: {rest:?}"
    );
}

// --- the fix carries, one test per code --------------------------------------------

#[test]
fn k001_bound_rises_to_computed() {
    gift_repariert("34-kosten-ueberschritten.gab", "K001");
}

#[test]
fn p001_semicolon_is_inserted() {
    gift_repariert("623-statement-without-semicolon.gab", "P001");
}

#[test]
fn a005_arch_becomes_the_declared_one() {
    gift_repariert("462-annahme-fuer-fremde-maschine.gab", "A005");
}

#[test]
fn f002_literal_is_marked_rounded() {
    gift_repariert("84-literal-still-gerundet.gab", "F002");
}

#[test]
fn e005_write_is_declared() {
    gift_repariert("28-pure-schreibt.gab", "E005");
}

#[test]
fn e010_read_is_declared() {
    gift_repariert("62-lesen-ohne-reads.gab", "E010");
}

#[test]
fn n016_demand_is_carried_on() {
    gift_repariert("127-axiom-merkmal-ungetragen.gab", "N016");
}

#[test]
fn s001_label_becomes_the_visible_one() {
    gift_repariert("10-marke-fehlt.gab", "S001");
}

#[test]
fn e006_lock_is_declared() {
    gift_repariert("30-sperre-nicht-erklaert.gab", "E006");
}

#[test]
fn e007_declaration_goes_exclusive() {
    gift_repariert("41-geteilt-erklaert-exklusiv-genommen.gab", "E007");
}

#[test]
fn e011_touch_is_declared() {
    gift_repariert("117-touches-deckt-nicht.gab", "E011");
}

#[test]
fn e002_double_pure_becomes_single() {
    // No gift probe fires the duplicate arm (probe 13 fires the contradiction arm,
    // which must stay manual -- see the next test), so the source is inline.
    let q = "module gift {\nimpl fn still() effects { pure, pure } costs <= 8 ops {\n    return;\n}\n}\n";
    let (baum0, mut vor) = gabbro_syntax::lies("e002-doppelt", q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(fehler(&vor).contains(&"E002"));
    let (neu, nach, n) = gabbro_check::fix::fix_to_stable("e002-doppelt", q, 10);
    assert!(n > 0, "no fix applied, over:\n{q}");
    let rest = fehler(&nach);
    assert!(
        !rest.contains(&"E002"),
        "`E002` still fires after --fix, over:\n{neu}\nleft: {rest:?}"
    );
}

/// The contradiction arm (`pure` beside a real entry) offers two directions in its own
/// text, so no fix may be unique there -- and this test pins that the probe keeps its
/// refusal without one.
#[test]
fn e002_contradiction_stays_manual() {
    let q = gift("13-pure-und-schreiben.gab");
    let (baum0, mut vor) = gabbro_syntax::lies("13-pure-und-schreiben.gab", &q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(fehler(&vor).contains(&"E002"));
    assert!(
        vor.absagen
            .iter()
            .filter(|a| a.code == "E002")
            .all(|a| a.fix.is_none()),
        "the contradiction arm must carry no fix -- its text offers two directions"
    );
}

#[test]
fn k012_deadline_takes_the_declared_arch() {
    gift_repariert("696-frist-ohne-maschine.gab", "K012");
}

#[test]
fn p033_stray_semicolon_is_removed() {
    gift_repariert("624-block-form-with-trailing-semicolon.gab", "P033");
}

#[test]
fn n202_translator_goes_pure() {
    gift_repariert("872-translator-with-effects.gab", "N202");
}

#[test]
fn n036_uncarryable_word_is_removed() {
    gift_repariert("243-fnzeiger-verspricht-locks.gab", "N036");
}

#[test]
fn g002_gate_becomes_the_only_build() {
    gift_repariert("312-when-auf-etwas-anderem.gab", "G002");
}

#[test]
fn e003_divergence_is_declared() {
    // No gift probe fires `E003`: the hint needs a `divergent fn` whose clause
    // stands but lacks the word, a shape the corpus never writes. Inline instead.
    let q = "module gift {\nextern fn halte_an() effects { diverges } costs <= 1 ops;\ndivergent fn wartet() effects { pure } costs <= 2 ops {\n    halte_an();\n}\n}\n";
    let (baum0, mut vor) = gabbro_syntax::lies("e003-hinweis", q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(
        vor.absagen
            .iter()
            .any(|a| a.code == "E003" && a.stufe == Stufe::Hinweis && a.fix.is_some()),
        "expected an `E003` hint with a fix, got:\n{}",
        vor.zeige(q)
    );
    let (neu, nach, n) = gabbro_check::fix::fix_to_stable("e003-hinweis", q, 10);
    assert!(n > 0, "no fix applied, over:\n{q}");
    let rest = alle(&nach);
    assert!(
        !rest.contains(&"E003"),
        "`E003` still fires after --fix, over:\n{neu}\nleft: {rest:?}"
    );
}

#[test]
fn l001_string_is_closed() {
    // No gift probe writes an unterminated string: every literal in the corpus is
    // closed. Inline, modelled on the `reason` shape of probe 47.
    let q = "module gift {\nreason Grund {\n    Leer = 1 \"kein Wert\n    exhaustive\n}\n}\n";
    let (baum0, mut vor) = gabbro_syntax::lies("l001-offen", q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(fehler(&vor).contains(&"L001"), "got:\n{}", vor.zeige(q));
    let (neu, nach, n) = gabbro_check::fix::fix_to_stable("l001-offen", q, 10);
    assert!(n > 0, "no fix applied, over:\n{q}");
    let rest = fehler(&nach);
    assert!(
        !rest.contains(&"L001"),
        "`L001` still fires after --fix, over:\n{neu}\nleft: {rest:?}"
    );
}

#[test]
fn l004_prefix_is_lowercased() {
    // No gift probe writes `0X`/`0B`: the corpus spells every prefix lowercase.
    let q = "module gift {\nimpl fn gib() -> u32 effects { pure } costs <= 1 ops {\n    return 0X7;\n}\n}\n";
    let (baum0, mut vor) = gabbro_syntax::lies("l004-gross", q);
    gabbro_check::pruefe(&baum0, &mut vor);
    assert!(fehler(&vor).contains(&"L004"), "got:\n{}", vor.zeige(q));
    let (neu, nach, n) = gabbro_check::fix::fix_to_stable("l004-gross", q, 10);
    assert!(n > 0, "no fix applied, over:\n{q}");
    let rest = fehler(&nach);
    assert!(
        !rest.contains(&"L004"),
        "`L004` still fires after --fix, over:\n{neu}\nleft: {rest:?}"
    );
}
