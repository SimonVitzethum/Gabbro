//! Integer `match` lowers to a C `switch` (lane 227).
//!
//! Lane 222 added the syntax (exact and range arms over an integer scrutinee);
//! this file pins the lowering: exact arms become one `case` each, range arms
//! expand to one stacked `case` per value, the scrutinee expression stands once
//! in the header (a `switch` evaluates it exactly once, so no temporary), and
//! there is no `default` -- exhaustiveness is the checker's.
//!
//! **Fix lane F1 (2026-09-21) built that checker rule**: `N411` (a value of the
//! scrutinee's M1 range no arm names), `N412` (an arm naming a value twice or no
//! value), `N413` (an arm value outside the scrutinee's storage type), `N414`
//! (integer arms over a non-integer, or a variant arm among them). The positive
//! probes below therefore cover their scrutinee -- by a declared range
//! (`u32 in 0 .. 7`), a full narrow type (`u8`) or a `narrow` -- and every poison
//! row names BOTH lines where both exist: the checker code and the emitter's
//! `C001`, which stays as the second line.

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

/// Checker codes and emitter codes separately, with no assertion -- for the rows
/// where both lines refuse (fix lane F1: the checker says it first, the emitter's
/// `C001` stays).
fn beide(source: &str) -> (Vec<String>, Vec<String>, String) {
    let (tree, mut refusals) = gabbro_syntax::lies("intmatch", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let pruefer: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    let (tree2, mut r2) = gabbro_syntax::lies("intmatch", source);
    let c = gabbro_check::emit::emittiere(&tree2, &mut r2);
    let erzeuger: Vec<String> = r2
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    (pruefer, erzeuger, c)
}

/// One pure function over a scrutinee of type `typ`.
fn einheit_typ(typ: &str, rumpf: &str) -> String {
    format!(
        "module test::intmatch {{\n\
         impl fn klassifiziere(x : {typ}) -> u32\n\
         \x20   effects {{ pure }}\n\
         \x20   costs   <= 64 ops\n\
         {{\n\
         {rumpf}\
         }}\n\
         }}\n"
    )
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
    let c = erzeugt(&einheit_typ(
        "u32 in 0 .. 7",
        "    match x {\n\
         \x20       0 => { return 10; }\n\
         \x20       1 => { return 11; }\n\
         \x20       2 .. 6 => { return 12; }\n\
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
    let c = erzeugt(&einheit_typ(
        "u32 in 2 .. 4",
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
    let c = erzeugt(&einheit_typ(
        "u32 in 5 .. 6",
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
         impl fn klassifiziere(x : i32 in -1 .. 0) -> i32\n\
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
         impl fn klassifiziere(x : u64 in 18446744073709551614 .. 18446744073709551615) -> u64\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       18446744073709551615 => { return 1; }\n\
         \x20       18446744073709551614 => { return 0; }\n\
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
    let (pruefer, codes, _) = beide(&einheit(
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
    assert!(
        pruefer.contains(&"N412".to_string()),
        "the checker says it first (N412) -- fell with {pruefer:?}"
    );
}

#[test]
fn range_overlapping_an_exact_is_refused() {
    let (pruefer, codes, _) = beide(&einheit(
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
    assert!(
        pruefer.contains(&"N412".to_string()),
        "the checker says it first (N412) -- fell with {pruefer:?}"
    );
}

#[test]
fn range_past_256_values_is_refused() {
    // Covered (`u32 in 0 .. 1000`), so the checker is silent and the refusal is the
    // emitter's alone: this is a lowering limit, not a coverage fault.
    let (_, codes) = erzeugt_mit_absagen(&einheit_typ(
        "u32 in 0 .. 1000",
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
    let (pruefer, codes, _) = beide(&einheit(
        "    match x {\n\
         \x20       5 .. 3 => { return 1; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "no value could ever meet it -- fell with {codes:?}"
    );
    assert!(
        pruefer.contains(&"N412".to_string()),
        "the checker says it first (N412) -- fell with {pruefer:?}"
    );
}

#[test]
fn mixed_integer_and_variant_arms_are_refused() {
    let (pruefer, codes, _) = beide(&einheit(
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
    assert!(
        pruefer.contains(&"N414".to_string()),
        "the checker says it first (N414) -- fell with {pruefer:?}"
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
    let (pruefer, codes, c) = beide(quelle);
    assert!(
        codes.contains(&"C001".to_string()),
        "integer arms meet no variant -- fell with {codes:?}:\n{c}"
    );
    assert!(
        pruefer.contains(&"N414".to_string()),
        "the checker says it first (N414) -- fell with {pruefer:?}"
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

/// **Review G07 (2026-09-21): a label outside the scrutinee's type is refused.**
///
/// C converts a `case` constant to the scrutinee's promoted type, so over a `u32`
/// scrutinee `case -1:` would fire for `x == 4294967295` -- a different value than
/// the arm names. The signed twin (`negative_exacts_lower_over_a_signed_scrutinee`)
/// keeps `-1` over an `i32`.
#[test]
fn label_outside_the_scrutinee_type_is_refused() {
    let (pruefer, codes, _) = beide(&einheit(
        "    match x {\n\
         \x20       -1 => { return 1; }\n\
         \x20       0 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(
        codes.contains(&"C001".to_string()),
        "`-1` over a `u32` names no value it can hold -- fell with {codes:?}"
    );
    assert!(
        pruefer.contains(&"N413".to_string()),
        "the checker says it first (N413) -- fell with {pruefer:?}"
    );
}

// ---------------------------------------------------------------------------------
// Fix lane F1 (2026-09-21): the coverage rule itself, `N411`-`N414`.
// ---------------------------------------------------------------------------------

/// **The poison the emitter cannot see.** One arm over a `u32`: the C compiles (a
/// `switch` without `default` over an integer draws no `-Wswitch`), and every value
/// but `0` skips the statement. Only `N411` stands between this and the product.
#[test]
fn a_gap_is_n411_and_only_the_checker_sees_it() {
    let (pruefer, erzeuger, c) = beide(&einheit(
        "    match x {\n\
         \x20       0 => { return 1; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(pruefer.contains(&"N411".to_string()), "fell with {pruefer:?}");
    assert!(erzeuger.is_empty(), "the emitter lowers it -- fell with {erzeuger:?}:\n{c}");
    assert!(c.contains("switch (x) {"), "and writes the switch:\n{c}");
}

/// A gap inside a declared range, not at its end: `0`, `2 .. 3` over `u32 in 0 .. 3`.
#[test]
fn a_gap_inside_a_declared_range_is_n411() {
    let (pruefer, _, _) = beide(&einheit_typ(
        "u32 in 0 .. 3",
        "    match x {\n\
         \x20       0 => { return 1; }\n\
         \x20       2 .. 3 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(pruefer.contains(&"N411".to_string()), "`1` is named by no arm -- {pruefer:?}");
}

/// **Positive: the full range of a narrow type**, two arms tiling `u8`.
#[test]
fn full_u8_range_in_two_arms_checks_clean() {
    let c = erzeugt(&einheit_typ(
        "u8",
        "    match x {\n\
         \x20       0 .. 127 => { return 1; }\n\
         \x20       128 .. 255 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(c.contains("case 255: {"), "the last label:\n{c}");
}

/// **Positive: M1's flow range decides, not only the declaration.** After `narrow x
/// to 0 ..< 4` the scrutinee holds `0 .. 3`, and one arm covers it -- the same
/// range an index into a four-slot table is trusted on.
#[test]
fn a_narrowed_scrutinee_is_covered_by_its_narrowed_range() {
    let c = erzeugt(&einheit(
        "    narrow x to 0 ..< 4 else { return 9; }\n\
         \x20   match x {\n\
         \x20       0 .. 3 => { return x; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(c.contains("case 3: {"), "the narrowed range is spelled out:\n{c}");
    // And without the narrow the same arm is a gap.
    let (pruefer, _, _) = beide(&einheit(
        "    match x {\n\
         \x20       0 .. 3 => { return x; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(pruefer.contains(&"N411".to_string()), "without the narrow -- {pruefer:?}");
}

/// **`-2^63` is spelled as a constant expression** (review G07 F5): `-9223372036854775808`
/// is unary minus on a literal that does not fit `long long`, and `cc -Werror` refuses it.
#[test]
fn i64_min_label_is_a_constant_expression() {
    let quelle = "module test::intmatch {\n\
         impl fn klassifiziere(x : i64 in -9223372036854775808 .. -9223372036854775807) -> i64\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       -9223372036854775808 => { return 1; }\n\
         \x20       -9223372036854775807 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         }\n";
    let c = erzeugt(quelle);
    assert!(c.contains("case (-9223372036854775807 - 1): {"), "INT64_MIN:\n{c}");
}

/// **The positive probes compile.** Every clean shape above, emitted and handed to
/// `cc -std=c11 -Wall -Wextra -Werror`: a lowering that `cc` refuses is no lowering.
/// A missing `cc` is a missing measurement and panics (W1).
#[test]
fn covered_matches_compile_under_werror() {
    let quelle = "module test::intmatch {\n\
         impl fn a(x : u8) -> u32\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       0 .. 127 => { return 1; }\n\
         \x20       128 .. 255 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         impl fn b(x : i64 in -9223372036854775808 .. -9223372036854775807) -> i64\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       -9223372036854775808 => { return 1; }\n\
         \x20       -9223372036854775807 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         impl fn c(x : u64 in 18446744073709551614 .. 18446744073709551615) -> u64\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   match x {\n\
         \x20       18446744073709551615 => { return 1; }\n\
         \x20       18446744073709551614 => { return 0; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         impl fn d(x : u32) -> u32\n\
         \x20   effects { pure }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   narrow x to 0 ..< 4 else { return 9; }\n\
         \x20   match x {\n\
         \x20       0 .. 3 => { return x; }\n\
         \x20   }\n\
         \x20   return 0;\n\
         }\n\
         }\n";
    let c = erzeugt(quelle);
    let ziel = std::env::temp_dir().join(format!("gabbro-intmatch-{}.c", std::process::id()));
    std::fs::write(&ziel, &c).expect("the emitted C is writable");
    let r = std::process::Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fsyntax-only"])
        .arg(&ziel)
        .output()
        .unwrap_or_else(|e| panic!("`cc` does not start ({e}) -- NOTHING measured"));
    let _ = std::fs::remove_file(&ziel);
    assert!(
        r.status.success(),
        "`cc` refused the covered matches:\n{}\n{c}",
        String::from_utf8_lossy(&r.stderr)
    );
}

/// **`bool` is no integer scrutinee** (`N414`): branch on it with `if`.
#[test]
fn integer_arms_over_a_bool_are_n414() {
    let (pruefer, _, _) = beide(&einheit_typ(
        "bool",
        "    match x {\n\
         \x20       0 => { return 1; }\n\
         \x20       1 => { return 2; }\n\
         \x20   }\n\
         \x20   return 0;\n",
    ));
    assert!(pruefer.contains(&"N414".to_string()), "fell with {pruefer:?}");
}

/// **The empty `match` over an integer names nothing**: `N411` names the whole range,
/// and it no longer ends a `narrow` arm (`all()` over no arms was vacuously "ends").
#[test]
fn the_empty_match_is_n411_and_ends_nothing() {
    let (pruefer, _, _) = beide(&einheit(
        "    match x { }\n\
         \x20   return 0;\n",
    ));
    assert!(pruefer.contains(&"N411".to_string()), "fell with {pruefer:?}");
    let quelle = "module test::intmatch {\n\
         table T count 4 { slot { v : u32, } }\n\
         impl fn f(i : u32, y : u32) -> u32\n\
         \x20   effects { reads T }\n\
         \x20   costs   <= 64 ops\n\
         {\n\
         \x20   narrow i to 0 ..< 4 else {\n\
         \x20       match y { }\n\
         \x20   }\n\
         \x20   return T.slots[i].v;\n\
         }\n\
         }\n";
    let (pruefer, _, _) = beide(quelle);
    assert!(
        pruefer.contains(&"M105".to_string()),
        "an empty `match` does not end the `else` of a `narrow` -- fell with {pruefer:?}"
    );
}

/// **The conservative reading stays beside `N411`** (fix lane F1, safety first): even a
/// COVERED integer `match` whose arms all return does not end a `narrow` arm, because the
/// flow passes still count the path past all arms (`crate::int_match_may_miss`). This
/// pins the documented precision cost; lifting it needs a proof that `N411` makes the
/// path dead in every pass that reads `endet_immer`.
#[test]
fn a_covered_match_still_does_not_end_a_narrow_arm() {
    let quelle = "module test::intmatch {\n\
         table T count 4 { slot { v : u32, } }\n\
         impl fn f(i : u32, y : u8) -> u32\n\
         \x20   effects { reads T }\n\
         \x20   costs   <= 600 ops\n\
         {\n\
         \x20   narrow i to 0 ..< 4 else {\n\
         \x20       match y {\n\
         \x20           0 .. 255 => { return 0; }\n\
         \x20       }\n\
         \x20   }\n\
         \x20   return T.slots[i].v;\n\
         }\n\
         }\n";
    let (pruefer, _, _) = beide(quelle);
    assert!(!pruefer.contains(&"N411".to_string()), "covered -- {pruefer:?}");
    assert!(pruefer.contains(&"M105".to_string()), "still not ending -- {pruefer:?}");
}
