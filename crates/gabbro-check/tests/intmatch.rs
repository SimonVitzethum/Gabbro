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

// ---------------------------------------------------------------------------------
// Fix lane F1 (2026-09-21): the coverage rule itself, `N411`-`N414`.
// ---------------------------------------------------------------------------------

