//! **Two residues of the 18 x 18 call matrix, and both halves of each.**
//!
//! The matrix run of 2026-09-02 closed the nominal-shape hole with `M140` and left two cells
//! open with a structural reason. Both were reproduced by hand against the unchanged checker
//! before a line was written, and both gave the same three-stage picture:
//!
//! | | checker | emitter | `cc -Werror` |
//! |---|---|---|---|
//! | `ptr<normal, r>` at a `ptr<normal, rw>` parameter | `0 errors` | faithful: `const Text *` into `Text *` | *discards `const` qualifier* |
//! | `&eng` (`u8 -> u8`) at a `fn(u32) -> u32` slot | `0 errors`, `100 % coverage` | faithful: `.f = &eng` | *incompatible pointer type* |
//!
//! **The `N041` shape twice: the checker confirms, and the foreign compiler holds the line.**
//!
//! ## Why the silent half is the one that carries the claim
//!
//! Both rules are DIRECTIONAL, and in opposite ways -- that is the whole reason they are two
//! rules and not one:
//!
//! * `R013` is a subsumption. `rw` at an `r` parameter NARROWS and is legitimate; only the
//!   widening falls. Get that backwards and every reader in the corpus goes red.
//! * `M142` is an EQUALITY. Nothing converts at an indirect call, so `fn(u32)` at a `fn(u8)`
//!   slot is exactly as wrong as `fn(u8)` at a `fn(u32)` slot. Get that backwards -- write it
//!   as a subsumption, the way `M128`'s sentence reads -- and half the defect stays invisible.
//!
//! *A guard that only ever asserts a refusal is green for a rule pointing the wrong way.*
//! Each test below therefore drives both directions.

use gabbro_syntax::diag::Stufe;

/// One frame per case, so that rows differ in the declaration and in nothing else.
const RAHMEN: &str = r#"module app::r {
static mut STAND : u32 = 0;
type Text = { n : u32, };
"#;

/// The refusal codes of `<RAHMEN><zusatz>}`, checker only.
fn codes(zusatz: &str) -> Vec<String> {
    let quelle = format!("{RAHMEN}{zusatz}}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("rechte.gab", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

/// A callee whose pointer parameter is declared `slot`, and a caller handing it a bare
/// parameter of its own declared `arg`. **A bare parameter name is the only argument form
/// `R013` reads**, the same under-approximation `R008` states about the space.
fn ruf_mit_rechten(slot: &str, arg: &str) -> String {
    // **Both bodies are empty and both contracts are `pure`**, and that is deliberate: an
    // effect line or a dereference would drag `E005`, `R002` or `R003` into rows whose
    // subject is the DECLARED right. *`R013` reads the declaration and nothing else.*
    format!(
        "impl fn ziel(p : ptr<normal, {slot}> Text)\n\
         \x20   effects {{ pure }} costs <= 4 ops {{ }}\n\
         impl fn ruft(a : ptr<normal, {arg}> Text)\n\
         \x20   effects {{ pure }} costs <= 20 ops {{ ziel(a); }}\n"
    )
}

/// **`R013`, the loud half.** Every row hands a callee a right its argument never had.
#[test]
fn ein_weiteres_recht_am_engeren_argument_faellt() {
    let faelle: &[(&str, &str, &str)] = &[
        ("read-only into a read-write parameter", "rw", "r"),
        ("read-only into an owning parameter", "own", "r"),
        ("write-only into a read-write parameter", "rw", "w"),
        ("read-only into a write-only parameter", "w", "r"),
    ];
    for (was, slot, arg) in faelle {
        let g = codes(&ruf_mit_rechten(slot, arg));
        assert!(
            g.contains(&"R013".to_string()),
            "{was}: `{arg}` at `{slot}` must fall with `R013` -- got {g:?}"
        );
    }
}

/// **`R013`, the counter-direction -- and it is the half a wrong-way rule breaks first.**
///
/// `tests/gestalt.rs` already carried the `rw` at `r` row before this rule existed
/// (*a wider right at a narrower slot*), which is why the corpus stayed byte-identical.
/// It is repeated here because that file is about `M140` and would not say why it broke.
#[test]
fn ein_engerer_slot_bleibt_still() {
    let paare: &[(&str, &str, &str)] = &[
        ("the same right", "r", "r"),
        ("the same right, writing", "rw", "rw"),
        // The legitimate narrowing: the callee promises to do less than it could.
        ("a wider right at a narrower slot", "r", "rw"),
        // `own` lowers to a non-`const` `T *` -- `emit::zeiger_schreibend` is the one home of
        // that decision -- so it carries read AND write, and the corpus writes it bare.
        ("an owning argument at a read-write slot", "rw", "own"),
        ("an owning argument at a read-only slot", "r", "own"),
        ("`rw + own` at a read-write slot", "rw", "rw + own"),
        // A spelling, not a set: `r + w` and `rw` are one pointer.
        ("`r + w` spelled out at a `rw` slot", "rw", "r + w"),
    ];
    for (was, slot, arg) in paare {
        let g = codes(&ruf_mit_rechten(slot, arg));
        assert!(
            g.is_empty(),
            "{was}: `{arg}` at `{slot}` is a CORRECT call and must stay silent -- fell with {g:?}"
        );
    }
}

/// A `fn(...)` slot of shape `slot`, and a function of shape `fun` put into it with `&`.
/// Both sides carry the same contract, so anything that falls here is the SIGNATURE.
///
/// **`slot` and `fun` carry their own closing `)`** -- they have to, because the result
/// arrow stands behind it and the two halves differ in whether there is one.
fn ruf_mit_fnzeiger(slot: &str, fun: &str) -> String {
    format!(
        "type Tafel = {{ f : fn({slot} effects {{ pure }} costs <= 4 ops, }};\n\
         impl fn g({fun}\n\
         impl fn baue() -> Tafel\n\
         \x20   effects {{ pure }} costs <= 8 ops {{ return Tafel(f: &g); }}\n"
    )
}

/// **`M142`, the loud half -- and both directions of the SAME crossing are in it.**
///
/// `u8` at a `u32` slot and `u32` at a `u8` slot both fall, and that pair is the evidence
/// that this is an equality and not `M128`'s subsumption. *A rule written as a subsumption
/// would pass one of these two rows and look finished.*
#[test]
fn eine_andere_unterschrift_faellt() {
    let faelle: &[(&str, &str, &str)] = &[
        (
            "a narrower word at the parameter",
            "u32) -> u32",
            "b : u8) -> u8 effects { pure } costs <= 2 ops { return b; }",
        ),
        (
            "a WIDER word at the parameter -- the same crossing, reversed",
            "u8) -> u8",
            "b : u32) -> u32 effects { pure } costs <= 2 ops { return b; }",
        ),
        (
            "a signed word where the slot is unsigned",
            "u32) -> u32",
            "b : i32) -> i32 effects { pure } costs <= 2 ops { return b; }",
        ),
        (
            "no result where the slot promises one",
            "u32) -> u32",
            "b : u32) effects { pure } costs <= 2 ops { }",
        ),
        (
            "a result where the slot takes none",
            "u32)",
            "b : u32) -> u32 effects { pure } costs <= 2 ops { return b; }",
        ),
        (
            "the wrong record behind a pointer parameter",
            "ptr<normal, r> Text) -> u32",
            "b : ptr<normal, r> u32) -> u32 effects { pure } costs <= 2 ops { return 0; }",
        ),
    ];
    for (was, slot, fun) in faelle {
        let g = codes(&ruf_mit_fnzeiger(slot, fun));
        assert!(
            g.contains(&"M142".to_string()),
            "{was}: `{fun}` at `fn({slot})` must fall with `M142` -- got {g:?}"
        );
    }
}

/// **`M142`, the counter-direction.** A signature that agrees must stay silent -- including
/// through a range alias, which is transparent by construction (`N030`) and lowers to the
/// same C word.
#[test]
fn dieselbe_unterschrift_bleibt_still() {
    let paare: &[(&str, &str, &str)] = &[
        (
            "the same signature",
            "u32) -> u32",
            "b : u32) -> u32 effects { pure } costs <= 2 ops { return b; }",
        ),
        (
            "no result on either side",
            "u32)",
            "b : u32) effects { pure } costs <= 2 ops { }",
        ),
        (
            "no parameters and no result",
            ")",
            ") effects { pure } costs <= 2 ops { }",
        ),
        (
            "the same record behind a pointer",
            "ptr<normal, r> Text)",
            "b : ptr<normal, r> Text) effects { pure } costs <= 2 ops { }",
        ),
        (
            "a declared RANGE the slot does not repeat -- one C word, one ABI",
            "u32) -> u32",
            "b : u32 in 0 .. 9) -> u32 effects { pure } costs <= 2 ops { return b; }",
        ),
    ];
    for (was, slot, fun) in paare {
        let g = codes(&ruf_mit_fnzeiger(slot, fun));
        assert!(
            g.is_empty(),
            "{was}: `{fun}` at `fn({slot})` is CORRECT and must stay silent -- fell with {g:?}"
        );
    }
}

/// **The two rules are independent, and a pointer can be wrong in both ways at once.**
///
/// `M128` holds the contract, `M142` the signature; the arity arm is `M128`'s alone and
/// `M142` returns before it, so an arity mismatch must give exactly one of them. *Without
/// this row the division of labour between the two codes is an intention, not a fact.*
#[test]
fn vertrag_und_unterschrift_sind_zwei() {
    // Arity: `M128`'s, and `M142` must not double-report it.
    let g = codes(&ruf_mit_fnzeiger(
        "u32, u32)",
        "b : u32) effects { pure } costs <= 2 ops { }",
    ));
    assert!(g.contains(&"M128".to_string()), "arity is `M128`'s -- got {g:?}");
    assert!(
        !g.contains(&"M142".to_string()),
        "`M142` must not also report an arity mismatch -- got {g:?}"
    );
    // The contract alone: same signature, an effect the slot forbids.
    let g = codes(
        "type Tafel = { f : fn(u32) effects { pure } costs <= 4 ops, };\n\
         impl fn g(b : u32) effects { writes STAND } costs <= 2 ops { STAND = b; }\n\
         impl fn baue() -> Tafel\n\
         \x20   effects { pure } costs <= 8 ops { return Tafel(f: &g); }\n",
    );
    assert!(g.contains(&"M128".to_string()), "the contract is `M128`'s -- got {g:?}");
    assert!(
        !g.contains(&"M142".to_string()),
        "the signature agrees, so `M142` must stay out of it -- got {g:?}"
    );
}
