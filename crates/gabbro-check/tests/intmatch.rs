//! Integer `match` lowers to a C `switch` (lane 227).
//!
//! Lane 222 added the syntax (exact and range arms over an integer scrutinee);
//! this file pins the lowering: exact arms become one `case` each, range arms
//! expand to one stacked `case` per value, the scrutinee expression stands once
//! in the header (a `switch` evaluates it exactly once, so no temporary), and
//! there is no `default` -- exhaustiveness stays the checker's (lane 228).
//! Every refusal below is `C001`: the emitter refuses by name instead of
//! emitting something plausible.

use gabbro_syntax::diag::Stufe;

/// The emitted C of a unit that checks clean. **The clean check is asserted, not
/// assumed** -- a positive probe over a file the checker refuses measures the
/// checker, and would read as a passed lowering test.
fn erzeugt(source: &str) -> String {
    let (tree, mut refusals) = gabbro_syntax::lies("intmatch", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let gefallen: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        gefallen.is_empty(),
        "the positive probe does not check clean -- fell with {gefallen:?}"
    );
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let nachher: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(nachher.is_empty(), "the emitter refused: {nachher:?}");
    c
}

/// The emitted C, plus whatever the EMITTER refused -- for the rows where the
/// checker is silent and the emitter is not.
fn erzeugt_mit_absagen(source: &str) -> (String, Vec<String>) {
    let (tree, mut refusals) = gabbro_syntax::lies("intmatch", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let pruefer: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        pruefer.is_empty(),
        "the poison probe should reach the emitter -- fell at pruefe with {pruefer:?}"
    );
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let codes: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    (c, codes)
}

fn einheit(rumpf: &str) -> String {
    format!(
        "module test::intmatch {{\n\
         impl fn klassifiziere(x : u32) -> u32\n\
         \x20   effects {{ pure }}\n\
         \x20   costs   <= 64 ops\n\
         {{\n\
         {rumpf}\
         }}\n\
         }}\n"
    )
}

#[test]
fn exact_arms_become_one_case_each() {
    let c = erzeugt(&einheit(
        "    match x {\n\
         \x20       0 => { return 10; }\n\
         \x20       1 => { return 11; }\n\
         \x20       7 => { return 17; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(c.contains("switch (x) {"), "the switch header:\n{c}");
    assert!(c.contains("case 0: {"), "exact 0:\n{c}");
    assert!(c.contains("case 1: {"), "exact 1:\n{c}");
    assert!(c.contains("case 7: {"), "exact 7:\n{c}");
    assert!(c.contains("} break;"), "every arm breaks:\n{c}");
    assert!(!c.contains("default"), "no default is added:\n{c}");
}

#[test]
fn inclusive_range_expands_to_stacked_cases() {
    let c = erzeugt(&einheit(
        "    match x {\n\
         \x20       2 .. 4 => { return 12; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(c.contains("case 2:\n"), "first value stacked:\n{c}");
    assert!(c.contains("case 3:\n"), "middle value stacked:\n{c}");
    assert!(c.contains("case 4: {"), "last value opens the body:\n{c}");
    assert!(!c.contains("case 5"), "nothing past the upper bound:\n{c}");
}

#[test]
fn exclusive_range_drops_its_upper_bound() {
    let c = erzeugt(&einheit(
        "    match x {\n\
         \x20       5 ..< 7 => { return 13; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(c.contains("case 5: {") || c.contains("case 5:\n"), "lower bound kept:\n{c}");
    assert!(c.contains("case 6: {"), "value below the bound kept:\n{c}");
    assert!(!c.contains("case 7"), "excluded bound dropped:\n{c}");
}

#[test]
fn negative_exacts_lower_over_a_signed_scrutinee() {
    let quelle = "module test::intmatch {\n\
         impl fn klassifiziere(x : i32) -> i32\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       -1 => { return 1; }\n\
         \x20       0 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         }\n";
    let c = erzeugt(quelle);
    assert!(c.contains("case -1: {"), "negative label:\n{c}");
    assert!(c.contains("case 0: {"), "zero beside it:\n{c}");
}

#[test]
fn u64_max_spells_with_the_u_suffix() {
    let quelle = "module test::intmatch {\n\
         impl fn klassifiziere(x : u64) -> u64\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       18446744073709551615 => { return 1; }\n\
         \x20       0 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         }\n";
    let c = erzeugt(quelle);
    assert!(
        c.contains("case 18446744073709551615u: {"),
        "past i64::MAX the label carries `u`:\n{c}"
    );
}

#[test]
fn duplicate_value_across_arms_is_refused() {
    let (_, codes) = erzeugt_mit_absagen(&einheit(
        "    match x {\n\
         \x20       3 => { return 1; }\n\
         \x20       3 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "two arms naming one value refuse -- fell with {codes:?}"
    );
}

#[test]
fn range_overlapping_an_exact_is_refused() {
    let (_, codes) = erzeugt_mit_absagen(&einheit(
        "    match x {\n\
         \x20       3 => { return 1; }\n\
         \x20       0 .. 5 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "the expansion meets the exact -- fell with {codes:?}"
    );
}

#[test]
fn range_past_256_values_is_refused() {
    let (_, codes) = erzeugt_mit_absagen(&einheit(
        "    match x {\n\
         \x20       0 .. 1000 => { return 1; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "unfolding 1001 labels is no lowering -- fell with {codes:?}"
    );
}

#[test]
fn inverted_range_is_refused() {
    let (_, codes) = erzeugt_mit_absagen(&einheit(
        "    match x {\n\
         \x20       5 .. 3 => { return 1; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "no value could ever meet it -- fell with {codes:?}"
    );
}

#[test]
fn mixed_integer_and_variant_arms_are_refused() {
    let (_, codes) = erzeugt_mit_absagen(&einheit(
        "    match x {\n\
         \x20       0 => { return 1; }\n\
         \x20       Some => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "one switch cannot meet both -- fell with {codes:?}"
    );
}

#[test]
fn integer_arms_over_a_tagged_value_are_refused() {
    let quelle = "module test::intmatch {\n\
         tagged type Nachricht = { Leer, Kurz(u32 in 0 .. 100) };\n\
         impl fn klassifiziere(m : Nachricht) -> u32 in 0 .. 100\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match m {\n\
         \x20       0 => { return 0; }\n\
         \x20       1 => { return 1; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         }\n";
    let (tree, mut refusals) = gabbro_syntax::lies("intmatch", quelle);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let codes: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        codes.contains(&"C001".to_string()),
        "integer arms meet no variant -- fell with {codes:?}:\n{c}"
    );
}

/// **Review G07 (2026-09-21): an integer `match` does not end a `narrow` arm.**
///
/// No pass checks that integer arms cover the scrutinee, and the `switch` has no
/// `default`: for `y != 0` the arm below falls through, and the narrowed `i` would
/// index `T` unchecked. Before the repair `crate::endet_immer` read the `match` as
/// ending (every arm returns) and `M105` stayed silent -- a checker-clean program
/// whose C reads `T.slots[i]` for any `i`.
#[test]
fn integer_match_does_not_end_a_narrow_arm() {
    let quelle = "module test::intmatch {\n\
         table T count 4 { slot { v : u32, } }\n\
         impl fn f(i : u32, y : u32) -> u32\n\
         \x20   effects { reads T }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   narrow i to 0 ..< 4 else {\n\
         \x20       match y {\n\
         \x20           0 => { return 0; }\n\
         \x20       }\n\
         \x20   }\n\
         \x20   return T.slots[i].v;\n\
         }\n\
         }\n";
    let (tree, mut refusals) = gabbro_syntax::lies("intmatch", quelle);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let codes: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        codes.contains(&"M105".to_string()),
        "a `narrow` arm ending in an integer `match` can fall through -- fell with {codes:?}"
    );
}

