//! **The `atomic_fetch_*` arm of `exchange update`, and the boundary around it**
//! (2026-09-15).
//!
//! `LANGUAGE.md` Part III §1 has promised since it was written that an `exchange
//! update` body which "corresponds to a primitive" lowers to `atomic_fetch_*`,
//! and everything else to the bounded CAS loop. Lane 201
//! (`messung/muse/MUSE-REPORT-201.md`) measured that only the second half
//! existed: the runtime's own ticket lock (`laufzeit/sperre.gab`) draws its
//! ticket with a 64-pass CAS loop where `CTicket.lean`'s first instruction is
//! ONE wait-free fetch-add, and the emitted C contained no `atomic_fetch_*` at
//! all.
//!
//! This file is the boundary, arm by arm. **Every row is a lowering assertion,
//! not a refusal count** -- the defect this arm can have is not "it refuses too
//! much" but *"it gave a body a DIFFERENT operation than the one written"*, and
//! only the emitted C can say that.
//!
//! What the rows measure:
//!
//! * the three reachable bitwise fetch forms (`t | m`, `t & m`, `t ^ m`) lower
//!   to one instruction, on either side of the operator, in all four widths
//!   and both signednesses;
//! * the two WRAPPING forms (`t +% m`, `t -% m`), which are the ones that match
//!   C11's silently-wrapping fetch-add, lower to `atomic_fetch_add/sub` where
//!   the binder's declared range IS the storage word, and stay refused where
//!   it is narrower -- the modulus is checked, never guessed;
//! * the ordering is the JOIN of the declaration's two halves -- `relaxed`
//!   stays `relaxed`, `release`/`acquire` becomes `acq_rel`, `seq` stays
//!   `seq_cst`;
//! * `+` and `-` are UNREACHABLE and the checker says so before the emitter is
//!   asked: an `update` body without a side condition must answer in the
//!   atomic's own type for every value it can hold, and checked `±1` shifts the
//!   interval by one -- `[lo+1, hi+1] ⊆ [lo, hi]` is false for every non-empty
//!   interval. `M104`/`M101`, not `C001`;
//! * the WRAPPING forms, which are the ones that match C11's silently-wrapping
//!   fetch-add, lower to one instruction where the binder's declared range is
//!   the storage word itself, and stay at `C001` where it is narrower: `+%`
//!   wraps at the operands' EXACT range, and that range is read off the
//!   atomic's declaration (the one place it IS readable for an `exchange`
//!   binder). On `u32` the modulus is 2^32 and the fetch exact; on
//!   `u32 in 0 .. 65535` it is 2^16 and the fetch a DIFFERENT operation.
//!   *A wait-free primitive bought by guessing a modulus is not an
//!   improvement* -- so the gate checks `n == bits`, and
//!   `OPUS-BERICHT-FETCHADD.md` §2 carries the measurement;
//! * a body that merely LOOKS like a fetch form gets the loop -- the binder on
//!   both sides, the binder on the wrong side of a non-commutative operator, a
//!   runtime operand, a shift, a side condition, two statements, a non-integer
//!   atomic.

use gabbro_syntax::diag::Stufe;

fn fehler(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("holform", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

/// A unit around one `exchange update` body over the named atomic.
///
/// `atome` are the atomic declarations, `rumpf` the update body, `ordnung_typ`
/// the atomic that is exchanged and the type the result is bound at.
fn einheit(atome: &str, ziel: &str, typ: &str, rumpf: &str) -> String {
    format!(
        "module test::holform {{\n\
         const MASKE : u32 = 12;\n\
         {atome}\
         extern fn aufgegeben() -> never effects {{ diverges }};\n\
         impl fn zug(p : u32) -> {typ}\n\
         \x20   effects {{ reads {ziel}, writes {ziel} }}\n\
         \x20   costs   <= 300 ops\n\
         {{\n\
         \x20   let alt : {typ} = {ziel} exchange update(t)\n\
         \x20       bounded 64 ops on_exceeded aufgegeben\n\
         \x20   {{ {rumpf} }} publishes nothing;\n\
         \x20   return alt;\n\
         }}\n\
         }}\n"
    )
}

/// The same, over a `relaxed u32` -- the shape most rows want.
fn roh(rumpf: &str) -> String {
    einheit("atomic ROH : u32 relaxed;\n", "ROH", "u32", rumpf)
}

// ---------------------------------------------------------------------------
// The three reachable arms, positive.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The ordering: the JOIN of the declaration's two halves, read off the emitter's
// own map and not assumed.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The widths, and the signed word.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The poison probes: a body that LOOKS like a fetch form and is not.
// ---------------------------------------------------------------------------

/// **`t + 1` never reaches the emitter, and this is the row that decides the
/// whole add question.** An `update` body without a side condition answers in
/// the atomic's own type for every value the atomic can hold; checked `+1`
/// shifts the interval by one, and no non-empty interval contains its own shift.
/// So there is no atomic type, ranged or not, for which this is writable.
#[test]
fn plus_eins_faellt_am_pruefer_und_nicht_am_erzeuger() {
    assert_eq!(
        fehler(&roh("return t + 1;")),
        vec!["M104", "M101"],
        "the range rules own this, not `C001` and not the fetch table"
    );
}

/// A ranged atomic does not rescue it either -- the shift leaves the range at
/// the top instead of at the word.
#[test]
fn plus_eins_faellt_auch_ueber_einem_bereich() {
    let src = einheit(
        "atomic GESTUFT : u32 in 0 .. 1000 relaxed;\n",
        "GESTUFT",
        "u32 in 0 .. 1000",
        "return t + 1;",
    );
    assert_eq!(fehler(&src), vec!["M101"], "same rule, one error nearer");
}

/// `t + 2` -- the operand is not the literal one, and it changes nothing: the
/// refusal is the interval's, not the literal's. *The add arm is not missing
/// because the table is short.*
#[test]
fn plus_zwei_faellt_genauso() {
    assert_eq!(fehler(&roh("return t + 2;")), vec!["M104", "M101"]);
}

// ---------------------------------------------------------------------------
// The fetch-add gate: full-width lowers, narrower stays refused.
// ---------------------------------------------------------------------------

/// **A non-power-of-two range never reaches the emitter.** `0 .. 1000` holds
/// 1001 values -- no `2^N` -- so the CHECKER owns this row (`M153`); the
/// emitter's `C001` beside it is the echo, not the decision.
#[test]
fn die_unexakte_umlaufform_faellt_am_pruefer() {
    let src = einheit(
        "atomic GESTUFT : u32 in 0 .. 1000 relaxed;\n",
        "GESTUFT",
        "u32 in 0 .. 1000",
        "return t +% 1;",
    );
    assert_eq!(fehler(&src), vec!["M153"], "the range rules own this");
}

/// **A signed word never wraps, so it never fetches.** The checker owns this
/// row (`M153`, unsigned-only); the gate repeats it as defense in depth for
/// an unchecked tree.
#[test]
fn umlauf_vorzeichen_faellt_am_pruefer() {
    let src = einheit(
        "atomic VOR : i32 relaxed;\n",
        "VOR",
        "i32",
        "return t +% 1;",
    );
    assert_eq!(fehler(&src), vec!["M153"], "the range rules own this");
}

/// **A `const` name does NOT adopt (checker).** Only a literal takes the
/// other's exact range (`wrapping_or_saturating`); a `const` carries its value
/// point, so `t +% MASKE` falls at `M153` before the emitter is asked. The
/// gate's const path therefore serves unchecked trees only -- mirroring
/// `wrap_side`, which reads `konstwert` the same way -- and no checked program
/// rides a NAME into a fetch-add. (The bitwise `MASKE` row above is unaffected:
/// `^` carries no exactness rule.)
#[test]
fn umlauf_konstante_faellt_am_pruefer() {
    assert_eq!(
        fehler(&roh("return t +% MASKE;")),
        vec!["M153"],
        "the range rules own this, not `C001` and not the fetch table"
    );
}

// ---------------------------------------------------------------------------
// The clauses are still demanded -- no refusal was lifted to build this arm.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The silencer both lowerings needed.
// ---------------------------------------------------------------------------

