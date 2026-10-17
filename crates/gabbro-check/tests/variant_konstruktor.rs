//! **The `tagged` case construction (lane 167) in both directions.**
//!
//! A `tagged` type could be matched (`match`) but never built: `Kurz(x)` fell
//! through as an unknown call (`H021`, pinned by `beispiele/gift/938`), a
//! nullary `Leer` fell at `M119`, a `static` initialiser fell at `C001` in the
//! emitter. The surface parses as an ordinary `Ruf` / `Ort` -- the parser knows
//! no declarations -- and the resolution stands in the checker
//! (`Umgebung::variante`, one predicate every pass asks) against the model's
//! `Expr.fall cs i nutz`: the case index is the declaration order, the payload
//! is held against the case's type, the construction answers the owning sum.
//!
//! What each row is:
//!
//! * a bare name over a case WITH payload falls with `N283` (the bare name is
//!   the nullary form, and it stands only where there is nothing to carry);
//! * labels at a case fall with `N284` (a case carries its payload
//!   positionally, like `Some(x)`);
//! * the bare nullary case and the `Leer()` call form both check clean and both
//!   lower to the compound literal with the mark alone;
//! * a function of the same name wins over the case -- no behaviour change
//!   where a name already means something (and the emitter agrees);
//! * a function of the name ANYWHERE in the unit blocks the construction --
//!   the emitter reads callees unit-wide, so an invisible same-named function
//!   would take the call lowering while the checker typed a case;
//! * a `let` shadowing the case wins at the bare form for the same reason;
//! * a payload of the wrong SHAPE falls at `M135`/`M140`, not at a constructor
//!   rule (the range half is `M101`'s, pinned by `beispiele/gift/945` -- a truth
//!   value against a number is `M135`'s crossing, anything else misshapen is
//!   `M140`'s);
//! * a bare name that is neither a value nor a case falls with `N280` beside
//!   `M119` (the call twin is `beispiele/gift/944`, the ambiguous twin
//!   `beispiele/gift/938`).

use gabbro_syntax::diag::Stufe;

fn errors(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("variant_konstruktor", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const HEAD: &str =
    "module test::variante {\ntagged type Nachricht = { Leer, Kurz(u32), Lang(u64) };\n";

fn unit(extra: &str) -> String {
    format!("{HEAD}{extra}}}\n")
}

#[test]
fn n283_bare_name_over_a_payload_case_falls() {
    let src = unit(
        "impl fn baue() -> Nachricht effects { pure } costs <= 4 ops \
         { let m : Nachricht = Kurz; return m; }\n",
    );
    assert_eq!(
        errors(&src),
        vec!["N283"],
        "a bare name carries no payload (`beispiele/gift/947` is the call twin)"
    );
}

#[test]
fn n284_labelled_variant_call_falls() {
    let src = unit(
        "impl fn baue(x : u32) -> Nachricht effects { pure } costs <= 8 ops \
         { return Kurz(x: x); }\n",
    );
    let gefallen = errors(&src);
    assert!(
        gefallen.contains(&"N284".to_string()),
        "labels exist only at a record constructor -- fell with {gefallen:?}"
    );
}

#[test]
fn function_elsewhere_in_the_unit_blocks_the_construction() {
    // `a::Kurz` is invisible from `b`, so the checker could type `Kurz(x)` as
    // the case -- but the emitter reads callees unit-wide and would lower the
    // call as the function. Refused (`N280`) instead of miscompiled; there is
    // no qualified case syntax that could name the case past the function.
    let src = "module test::a {\n\
         impl fn Kurz(x : u32) -> u32 effects { pure } costs <= 1 ops { return x; }\n\
         }\n\
         module test::b {\n\
         tagged type Nachricht = { Leer, Kurz(u32) };\n\
         impl fn baue(x : u32) -> Nachricht effects { pure } costs <= 8 ops \
         { return Kurz(x); }\n\
         }\n";
    let gefallen = errors(src);
    assert!(
        gefallen.contains(&"N280".to_string()),
        "a case sharing its name with a function has no writable construction \
         -- fell with {gefallen:?}"
    );
}

#[test]
fn local_shadowing_wins_at_the_bare_form() {
    let src = unit(
        "impl fn baue() -> u32 effects { pure } costs <= 4 ops \
         { let Leer : u32 = 5; return Leer; }\n",
    );
    let gefallen = errors(&src);
    assert!(
        gefallen.is_empty(),
        "a bound value is no case -- fell with {gefallen:?}"
    );
}

#[test]
fn payload_of_the_wrong_shape_falls_at_m135() {
    let src = unit(
        "impl fn baue() -> Nachricht effects { pure } costs <= 8 ops \
         { return Kurz(true); }\n",
    );
    let gefallen = errors(&src);
    assert!(
        gefallen.contains(&"M135".to_string()),
        "a truth value is no number -- `M135` owns the bool/number crossing, \
         not the constructor and not `M140` -- fell with {gefallen:?}"
    );
}

#[test]
fn unknown_bare_name_draws_n280_beside_m119() {
    let src = unit(
        "impl fn baue() -> u32 effects { pure } costs <= 4 ops \
         { return GibtsNicht; }\n",
    );
    let gefallen = errors(&src);
    assert!(
        gefallen.contains(&"N280".to_string()) && gefallen.contains(&"M119".to_string()),
        "neither a value nor a case -- fell with {gefallen:?}"
    );
}
