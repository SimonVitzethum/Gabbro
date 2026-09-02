//! **The shape at a slot -- and the half that matters is the SILENT one.**
//!
//! `M139` was written on 2026-09-02 out of a measurement: eighteen parameter kinds against
//! eighteen argument kinds, the wrong thing passed at a call, one file per cell.
//! **283 of 306 off-diagonal cells went through with `0 errors`**, and the run printed
//! `100 % coverage` at every one of them. `cc` caught 165, the emitter refused 96 (`C001`,
//! an array has no lowering as a parameter), and **22 reached green C**.
//!
//! The poison probes for the loud half live in `beispiele/gift/603`, `604` and `606`. This
//! file is the other half, and it is the one a widening rule breaks first: **a call that is
//! CORRECT must stay silent.** Every row below is a form the corpus writes or the language
//! promises --
//!
//! * the same record behind a pointer, and a pointer whose RIGHTS are narrower than the slot;
//! * a range alias at its carrier, in both directions -- `type Zaehler = u32 in 0 .. 9`
//!   lowers to its carrier and is transparent by construction (`N030`, 2026-08-20);
//! * an `opaque type` at its carrier INSIDE the module that declares it -- `D004` owns that
//!   crossing and is silent at home;
//! * the literal zero at a pointer (`beispiele/38`) and at an array (`beispiele/08`, `64`);
//! * an array at a pointer to its element -- C's decay, and `beispiele/64` rests on it;
//! * `bool` against a number, which is `M135`'s with its `0 .. 1` exception, and a reason
//!   value, which is `M124`'s.
//!
//! *The first version of this rule refused four of these*, and the corpus said so within one
//! run: `beispiele/08`, `38` and `64` went red, and three poison probes changed their code
//! out from under their own first line. **Every exemption below was measured, not designed.**

use gabbro_syntax::diag::Stufe;

/// One frame for every case -- a lock-free module carrying each kind exactly once, so that
/// the rows differ in the call and in nothing else.
const RAHMEN: &str = r#"module app::g {
const KAP : u32 = 8;
type Text = { bytes : [u8; KAP], len : u32 in 0 .. KAP, };
type Andr = { zahl : u32 in 0 .. 9, };
type Zaehler = u32 in 0 .. 9;
opaque type Deck = u32 in 0 .. 9;
static mut PUFFER : [u8; KAP] = 0;
"#;

/// The refusal codes of `<RAHMEN><zusatz>}`, checker only.
fn codes(zusatz: &str) -> Vec<String> {
    let quelle = format!("{RAHMEN}{zusatz}}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("gestalt.gab", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

/// A callee taking `slot`, and a caller handing it something of type `arg`.
fn ruf(slot: &str, arg: &str) -> String {
    format!(
        "impl fn ziel(q : {slot}) -> u32 in 0 .. 9\n\
         \x20   effects {{ pure }} costs <= 4 ops {{ return 0; }}\n\
         impl fn ruft(a : {arg}) -> u32 in 0 .. 9\n\
         \x20   effects {{ pure }} costs <= 20 ops {{ return ziel(a); }}\n"
    )
}

/// **The counter-direction, and it is the whole guard.** Each row is a call that is right;
/// none of them may produce a single refusal.
#[test]
fn ein_richtiger_ruf_bleibt_still() {
    let paare: &[(&str, &str, &str)] = &[
        ("the same record behind a pointer", "ptr<normal, r> Text", "ptr<normal, r> Text"),
        // `rw` promises MORE than `r`, and narrowing at the slot is what a reader wants.
        ("a wider right at a narrower slot", "ptr<normal, r> Text", "ptr<normal, rw> Text"),
        ("the same record by value", "Text", "Text"),
        ("a range alias at its carrier", "u32 in 0 .. 9", "Zaehler"),
        ("a carrier at its range alias", "Zaehler", "u32 in 0 .. 9"),
        // `D004` owns the opaque crossing and stays silent in the declaring module.
        ("an opaque type at home", "u32 in 0 .. 9", "Deck"),
        ("a narrower range at a wider slot", "u32 in 0 .. 9", "u8 in 0 .. 3"),
        ("a pointer to a number", "ptr<normal, r> u32 in 0 .. 9", "ptr<normal, r> u32 in 0 .. 9"),
        ("the same function pointer", "fn(u32) effects { pure } costs <= 2 ops",
                                      "fn(u32) effects { pure } costs <= 2 ops"),
    ];
    for (was, slot, arg) in paare {
        let g = codes(&ruf(slot, arg));
        assert!(
            g.is_empty(),
            "{was}: `{arg}` at `{slot}` is a CORRECT call and must stay silent -- fell with {g:?}"
        );
    }
}

/// **The zero and the decay** -- three forms the clean corpus writes, and the first version
/// of `M139` refused all three. They are not calls, so they get their own frame.
#[test]
fn die_null_und_der_zerfall_bleiben_still() {
    let faelle: &[(&str, &str)] = &[
        (
            "the null pointer (beispiele/38)",
            "static tz : ptr<normal, rw> Text = 0;\n",
        ),
        (
            "the zero-initialiser of an array (beispiele/08, 64)",
            "static mut feld : [u32; 4] = 0;\n",
        ),
        (
            "the zero-initialiser of a record",
            "static mut satz : Text = Text(bytes: 0, len: 0);\n",
        ),
        (
            "an array decaying to a pointer to its element (beispiele/64)",
            "extern fn schreib(p : ptr<normal, r> u8, n : u32) \
             effects { reads p } costs <= 8 ops;\n\
             impl fn ruft() effects { reads PUFFER } costs <= 12 ops \
             { schreib(PUFFER, 4); }\n",
        ),
    ];
    for (was, zusatz) in faelle {
        let g = codes(zusatz);
        assert!(g.is_empty(), "{was} must stay silent -- fell with {g:?}");
    }
}

/// **Two crossings belong to older rules, and `M139` must not take them.**
///
/// A rule that answered here would silence the rule that says more: `M135` carries the
/// `0 .. 1` exception a device flag needs (`beispiele/gift/416`), and `M124` is structural
/// with four doors. *Two refusals at one site look like two rules, and the older one's
/// poison probe would fall green while it is out.*
#[test]
fn was_anderen_regeln_gehoert_bleibt_ihnen() {
    let g = codes(&ruf("bool", "u32 in 0 .. 9"));
    assert_eq!(g, vec!["M135"], "the bool/number crossing is `M135`'s, not `M139`'s");
    let g = codes(&ruf("u32 in 0 .. 9", "bool"));
    assert_eq!(g, vec!["M135"], "and in the other direction too");
}

/// **The loud half, so that the counter-direction above cannot pass over a rule that is
/// simply out.** A guard that only ever asserts silence is green when nothing is measured.
#[test]
fn die_falsche_gestalt_faellt() {
    let faelle: &[(&str, &str, &str)] = &[
        ("the wrong record behind a pointer", "ptr<normal, r> Text", "ptr<normal, r> Andr"),
        ("a pointer at a bool", "bool", "ptr<normal, r> Text"),
        ("a number at a pointer", "ptr<normal, r> Text", "u32 in 0 .. 9"),
        ("a record at a number", "u32 in 0 .. 9", "Text"),
        ("an array at a record", "Text", "[u8; 4]"),
        ("a function pointer at a number", "u32 in 0 .. 9",
                                           "fn(u32) effects { pure } costs <= 2 ops"),
        ("two records by value", "Text", "Andr"),
    ];
    for (was, slot, arg) in faelle {
        let g = codes(&ruf(slot, arg));
        assert!(
            g.contains(&"M139".to_string()),
            "{was}: `{arg}` at `{slot}` must fall with `M139` -- got {g:?}"
        );
    }
}

/// **`.bytes = 0` is not C, and this is the line that says the braces are still there.**
///
/// Measured 2026-09-02 over the unchanged tree: the checker reported `5 items, 0 errors,
/// 0 hints` and the emitter wrote `{ .bytes = 0, .len = 0 }`, which `cc -std=c11 -O0 -Wall
/// -Wextra -Werror` refuses with `error: missing braces around initializer`. Both designator
/// sites had it -- the file-scope `static` and the compound literal.
#[test]
fn ein_feldfeld_bekommt_seine_klammern() {
    let quelle = "module app::b {\n\
        const KAP : u32 = 8;\n\
        type Text = { bytes : [u8; KAP], len : u32 in 0 .. KAP, };\n\
        static mut T : Text = Text(bytes: 0, len: 0);\n\
        impl fn baue() -> Text effects { pure } costs <= 4 ops \
            { return Text(bytes: 0, len: 0); }\n\
        impl fn haupt() -> u32 in 0 .. 8 effects { reads T } costs <= 4 ops \
            { return T.len; }\n\
        }\n";
    let (baum, mut absagen) = gabbro_syntax::lies("klammern.gab", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    let fehler: Vec<&str> = absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code)
        .collect();
    assert!(fehler.is_empty(), "the frame itself must check clean: {fehler:?}");
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(
        !c.contains(".bytes = 0"),
        "an array field must be braced -- `.bytes = 0` is `-Werror=missing-braces`:\n{c}"
    );
    assert_eq!(
        c.matches(".bytes = {0}").count(),
        2,
        "BOTH designator sites carry it -- the file-scope `static` and the compound \
         literal:\n{c}"
    );
}
