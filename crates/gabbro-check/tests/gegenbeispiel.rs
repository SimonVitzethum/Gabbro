//! **Counterexample search (`gabbro counterexample`), over snippets.**
//!
//! The Lean half of each assertion -- that the file the search prints
//! elaborates green -- is measured, not tested here: `./lean-probe` over
//! the probes and the nine corpus programs the exporter accepts (booked in
//! `messung/muse/MUSE-REPORT-180.md`). What stands here pins the
//! searcher's verdicts over snippets: a wrong `ensures` yields confirmed
//! hits (with the confirmation shape the kernel checks), a right one yields
//! "none found" and never "proved", and everything `lean-g` refuses is
//! refused here with the same `LG` code.

use gabbro_check::gegenbeispiel::{export, Suche};

fn checked(quelle: &str) -> gabbro_syntax::ast::Programm {
    let (baum, mut absagen) = gabbro_syntax::lies("gegenbeispiel", quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert!(
        absagen.fehler_zahl() == 0,
        "snippet must check: {}",
        absagen.zeige(quelle)
    );
    baum
}

fn suche(quelle: &str, nur: Option<&str>) -> String {
    let baum = checked(quelle);
    export("gegenbeispiel", &baum, nur, &Suche::default()).expect("search must export")
}

const KOPF: &str = "module test::gx {\n\
    table T count 2 { slot { v : u32 in 0 .. 10, } }\n";

/// A tableless unit: the input space is the parameters alone.
const KOPF_PUR: &str = "module test::gxp {\n";

fn einheit(extra: &str) -> String {
    format!("{KOPF}{extra}}}\n")
}

fn einheit_pur(extra: &str) -> String {
    format!("{KOPF_PUR}{extra}}}\n")
}

/// **A wrong `ensures` (`result > x` for `return x`) yields confirmed
/// counterexamples**: four exhaustive candidates, four kernel-checked
/// confirmations (contract verdict, `requires`, and the failing conjunct).
#[test]
fn falsches_ensures_meldet_treffer() {
    let text = suche(
        &einheit_pur(
            "impl fn f(x : u32 in 0 .. 3) -> u32 in 0 .. 10\n\
            \x20   ensures result > x\n\
            \x20   effects { pure }\n\
            \x20   costs <= 2 ops\n\
            {\n\
            \x20   return x;\n\
            }\n",
        ),
        None,
    );
    assert!(text.contains("-- f: 4 confirmed counterexample(s) above"), "summary must count 4 hits");
    for teil in [
        "example : gx_f_t0 = true := by decide",
        "example : gx_f_q0 = true := by decide",
        "example : gx_f_c0_0 = false := by decide",
        "#eval gx_f_t3",
        "def gx_f_erg3 : String",
        "NONE FOUND",
    ] {
        if teil == "NONE FOUND" {
            assert!(!text.contains(teil), "a hit file must not say none found");
        } else {
            assert!(text.contains(teil), "hit file must contain {teil:?}");
        }
    }
}

/// **A right `ensures` (`result == x`) yields none within the budget** --
/// and the tool says "none found", never "proved".
#[test]
fn richtiges_ensures_meldet_keinen_treffer() {
    let text = suche(
        &einheit_pur(
            "impl fn f(x : u32 in 0 .. 3) -> u32 in 0 .. 10\n\
            \x20   ensures result == x\n\
            \x20   effects { pure }\n\
            \x20   costs <= 2 ops\n\
            {\n\
            \x20   return x;\n\
            }\n",
        ),
        None,
    );
    assert!(text.contains("NONE FOUND among 4 candidate(s)"), "must say none found");
    assert!(text.contains("never \"proved\""), "must never claim proved");
    assert!(!text.contains("example : gx_f_t"), "no hit, no confirmation");
}

/// **A wrong `ensures` over a table slot hits, with the witness against
/// both contracts**: the input, that it meets `requires` (vacuous -- the
/// export sets `.wahr`), the computed end state, and the failing conjunct.
#[test]
fn falsches_schlitz_ensures_meldet_treffer() {
    let text = suche(
        &einheit(
            "impl fn set(i : index into T, x : u32 in 0 .. 10)\n\
            \x20   ensures T.slots[i].v == 7\n\
            \x20   effects { writes T.slots }\n\
            \x20   costs <= 3 ops\n\
            {\n\
            \x20   T.slots[i].v = x;\n\
            }\n",
        ),
        None,
    );
    assert!(text.contains("confirmed counterexample(s)"), "must confirm hits");
    assert!(text.contains("example : gx_set_q"), "requires confirmation travels");
    assert!(text.contains("example : gx_set_c"), "conjunct confirmations travel");
    assert!(text.contains("Endzustand: "), "the witness shows the end state");
}

/// **The 104 `lies` shape (correct `ensures` over a slot read) finds
/// nothing**: sampled space, zero confirmations.
#[test]
fn richtiges_lesen_meldet_keinen_treffer() {
    let text = suche(
        &einheit(
            "impl fn lies(i : index into T) -> u32 in 0 .. 10\n\
            \x20   ensures result == T.slots[i].v\n\
            \x20   effects { reads T.slots }\n\
            \x20   costs <= 2 ops\n\
            {\n\
            \x20   return T.slots[i].v;\n\
            }\n",
        ),
        None,
    );
    assert!(text.contains("NONE FOUND"), "must say none found");
    assert!(text.contains("242 candidate(s) exhaustive"), "the space is small and covered fully");
    assert!(!text.contains("example : gx_lies_t"), "no hit, no confirmation");
}

/// **A function without `ensures` is skipped loudly**: nothing to violate.
#[test]
fn ohne_ensures_keine_suche() {
    let text = suche(
        &einheit(
            "impl fn f(x : u32 in 0 .. 3) -> u32 in 0 .. 10\n\
            \x20   effects { pure }\n\
            \x20   costs <= 2 ops\n\
            {\n\
            \x20   return x;\n\
            }\n",
        ),
        None,
    );
    assert!(text.contains("SKIPPED (no ensures -- nothing to violate)"), "skip must be loud");
}

/// **The function filter selects one function**; an unknown name is an
/// `LG005` refusal, like every unknown name at the export.
#[test]
fn filter_waehlt_funktion() {
    let quelle = einheit(
        "impl fn f(x : u32 in 0 .. 3) -> u32 in 0 .. 10\n\
        \x20   ensures result == x\n\
        \x20   effects { pure }\n\
        \x20   costs <= 2 ops\n\
        {\n\
        \x20   return x;\n\
        }\n\
        impl fn g(x : u32 in 0 .. 3) -> u32 in 0 .. 10\n\
        \x20   ensures result == x\n\
        \x20   effects { pure }\n\
        \x20   costs <= 2 ops\n\
        {\n\
        \x20   return x;\n\
        }\n",
    );
    let text = suche(&quelle, Some("g"));
    assert!(text.contains("-- FUNCTION g:"), "filter must select g");
    assert!(!text.contains("-- FUNCTION f:"), "filter must drop f");
    let baum = checked(&quelle);
    let w = export("gegenbeispiel", &baum, Some("h"), &Suche::default()).expect_err("must refuse");
    assert_eq!(w.code, "LG005", "{w}");
}

/// **What `lean-g` refuses is refused here with the same code** (`LG001`:
/// an `extern fn` has no G form -- and no searchable body either). Like the
/// `lean_g` tests, this runs on the parsed tree: the refusal is the
/// exporter's, not the checker's.
#[test]
fn lean_g_absage_gilt_hier() {
    let quelle = einheit("extern fn e(x : u32) -> u32 effects { pure } costs <= 1 ops;\n");
    let (baum, _) = gabbro_syntax::lies("gegenbeispiel", &quelle);
    let w = export("gegenbeispiel", &baum, None, &Suche::default()).expect_err("must refuse");
    assert_eq!(w.code, "LG001", "{w}");
}
