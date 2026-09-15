//! **The `atomic_fetch_*` arm of `exchange update`, and the boundary around it**
//! (2026-09-15).
//!
//! `SPRACHE.md` Part III §1 has promised since it was written that an `exchange
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
//! * the three reachable fetch forms (`t | m`, `t & m`, `t ^ m`) lower to one
//!   instruction, on either side of the operator, in all four widths and both
//!   signednesses;
//! * the ordering is the JOIN of the declaration's two halves -- `relaxed`
//!   stays `relaxed`, `release`/`acquire` becomes `acq_rel`, `seq` stays
//!   `seq_cst`;
//! * `+` and `-` are UNREACHABLE and the checker says so before the emitter is
//!   asked: an `update` body without a side condition must answer in the
//!   atomic's own type for every value it can hold, and checked `±1` shifts the
//!   interval by one -- `[lo+1, hi+1] ⊆ [lo, hi]` is false for every non-empty
//!   interval. `M104`/`M101`, not `C001`;
//! * the WRAPPING forms, which are the ones that match C11's silently-wrapping
//!   fetch-add, stay at `C001`: the modulus cannot be read off an `exchange`
//!   binder, and a fetch-add bought by guessing a modulus is not an
//!   improvement;
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

/// The emitted C of a unit that checks clean. **The clean check is asserted, not
/// assumed** -- a positive probe over a file the checker refuses measures the
/// checker, and would read as a passed lowering test.
fn erzeugt(source: &str) -> String {
    let (tree, mut refusals) = gabbro_syntax::lies("holform", source);
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
    let (tree, mut refusals) = gabbro_syntax::lies("holform", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let codes: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    (c, codes)
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

#[test]
fn oder_wird_eine_anweisung() {
    let c = erzeugt(&roh("return t | 4;"));
    assert!(
        c.contains("atomic_fetch_or_explicit(&ROH, (uint32_t)(4), memory_order_relaxed)"),
        "`t | 4` is C11's `atomic_fetch_or`, not a loop:\n{c}"
    );
    assert!(
        !c.contains("compare_exchange"),
        "and no CAS is left beside it:\n{c}"
    );
}

#[test]
fn und_wird_eine_anweisung() {
    let c = erzeugt(&roh("return t & 4294967291;"));
    assert!(
        c.contains("atomic_fetch_and_explicit(&ROH, (uint32_t)(4294967291), memory_order_relaxed)"),
        "`t & m` is `atomic_fetch_and`:\n{c}"
    );
    assert!(!c.contains("compare_exchange"), "{c}");
}

#[test]
fn xor_wird_eine_anweisung() {
    let c = erzeugt(&roh("return t ^ 8;"));
    assert!(
        c.contains("atomic_fetch_xor_explicit(&ROH, (uint32_t)(8), memory_order_relaxed)"),
        "`t ^ m` is `atomic_fetch_xor`:\n{c}"
    );
    assert!(!c.contains("compare_exchange"), "{c}");
}

/// **All three are commutative, so the binder may stand on either side** -- and
/// the operand that comes out is the OTHER side, never the binder.
#[test]
fn der_binder_darf_links_stehen() {
    let c = erzeugt(&roh("return 4 | t;"));
    assert!(
        c.contains("atomic_fetch_or_explicit(&ROH, (uint32_t)(4), memory_order_relaxed)"),
        "`4 | t` is the same instruction as `t | 4`:\n{c}"
    );
}

/// A `const` name is a translation-time value and rides out as the NAME -- the
/// `#define` stands beside it, so changing the constant changes the operand.
#[test]
fn eine_konstante_faehrt_als_name_hinaus() {
    let c = erzeugt(&roh("return t ^ MASKE;"));
    assert!(
        c.contains("atomic_fetch_xor_explicit(&ROH, (uint32_t)(MASKE), memory_order_relaxed)"),
        "the constant's NAME, not its value:\n{c}"
    );
}

// ---------------------------------------------------------------------------
// The ordering: the JOIN of the declaration's two halves, read off the emitter's
// own map and not assumed.
// ---------------------------------------------------------------------------

#[test]
fn entspannt_bleibt_entspannt() {
    let c = erzeugt(&roh("return t | 1;"));
    assert!(c.contains("(&ROH, (uint32_t)(1), memory_order_relaxed)"), "{c}");
}

#[test]
fn freigabe_wird_acq_rel() {
    let c = erzeugt(&einheit(
        "atomic FREI : u32 release;\n",
        "FREI",
        "u32",
        "return t | 1;",
    ));
    assert!(
        c.contains("(&FREI, (uint32_t)(1), memory_order_acq_rel)"),
        "a `release` declaration is (store release, load acquire); ONE RMW carries \
         their join:\n{c}"
    );
}

#[test]
fn erwerb_wird_acq_rel() {
    let c = erzeugt(&einheit(
        "atomic HOLE : u32 acquire;\n",
        "HOLE",
        "u32",
        "return t & 4294967294;",
    ));
    assert!(
        c.contains("(&HOLE, (uint32_t)(4294967294), memory_order_acq_rel)"),
        "`acquire` and `release` name the same pair -- so the same join:\n{c}"
    );
}

#[test]
fn seq_bleibt_seq_cst() {
    let c = erzeugt(&einheit(
        "atomic ALLES : u32 seq;\n",
        "ALLES",
        "u32",
        "return t | 1;",
    ));
    assert!(
        c.contains("(&ALLES, (uint32_t)(1), memory_order_seq_cst)"),
        "{c}"
    );
}

/// **A declaration with no ordering word is `relaxed`, and the fetch arm must
/// not read that absence as anything else.** The `Atomic` arm of `sammle_namen`
/// was repaired once for exactly this class -- a catch-all that chose a memory
/// model.
#[test]
fn keine_ordnung_ist_entspannt() {
    let c = erzeugt(&einheit("atomic BLOSS : u32;\n", "BLOSS", "u32", "return t | 1;"));
    assert!(
        c.contains("(&BLOSS, (uint32_t)(1), memory_order_relaxed)"),
        "{c}"
    );
}

// ---------------------------------------------------------------------------
// The widths, and the signed word.
// ---------------------------------------------------------------------------

#[test]
fn alle_breiten_und_beide_vorzeichen() {
    for (dekl, name, typ, ctyp, operand) in [
        ("atomic W8 : u8 relaxed;\n", "W8", "u8", "uint8_t", "128"),
        ("atomic W16 : u16 relaxed;\n", "W16", "u16", "uint16_t", "256"),
        ("atomic W64 : u64 relaxed;\n", "W64", "u64", "uint64_t", "1"),
        ("atomic S32 : i32 relaxed;\n", "S32", "i32", "int32_t", "1"),
    ] {
        let c = erzeugt(&einheit(dekl, name, typ, &format!("return t | {operand};")));
        let erwartet =
            format!("{ctyp} alt = atomic_fetch_or_explicit(&{name}, ({ctyp})({operand}), memory_order_relaxed)");
        assert!(c.contains(&erwartet), "missing `{erwartet}` in:\n{c}");
    }
}

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

/// **The wrapping form is the one that MATCHES C11's fetch-add, and it stays a
/// refusal.** `atomic_fetch_add` wraps silently by definition; `+%` says wrap.
/// But `+%` wraps at the operands' EXACT range, and that range cannot be read
/// off an `exchange` binder (`wrap_side`/`ort_typ` resolve statics and
/// parameters only). On `u32` the modulus would be 2^32 and the fetch exact; on
/// `u32 in 0 .. 65535` it would be 2^16 and the fetch a DIFFERENT operation.
/// *A wait-free primitive bought by guessing a modulus is not an improvement* --
/// so `C001` stands, and `OPUS-BERICHT-FETCHADD.md` §2 carries what would have
/// to move.
#[test]
fn die_umlaufform_bleibt_eine_absage() {
    let (c, codes) = erzeugt_mit_absagen(&roh("return t +% 1;"));
    assert_eq!(codes, vec!["C001"], "the emitter refuses, the checker does not");
    assert!(
        !c.contains("atomic_fetch"),
        "and no fetch was emitted on the way out:\n{c}"
    );
}

#[test]
fn die_umlaufende_differenz_bleibt_eine_absage() {
    let (_, codes) = erzeugt_mit_absagen(&roh("return t -% 1;"));
    assert_eq!(codes, vec!["C001"]);
}

/// **The binder on BOTH sides is not a fetch form**: the operand would be `t`,
/// a name that exists only inside the loop this arm would have removed.
#[test]
fn der_binder_auf_beiden_seiten_bleibt_eine_schleife() {
    let c = erzeugt(&roh("return t | t;"));
    assert!(!c.contains("atomic_fetch"), "`t | t` is no fetch form:\n{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// **The row that matters most: a non-commutative operator with the binder on
/// the WRONG side.** `atomic_fetch_sub(&X, t)` computes `X - t`; the body says
/// `m - t`. A table that commuted would give this body a different operation and
/// nothing would say so. (It is also unreachable as a fetch form for the reason
/// above -- this row measures the SHAPE test, independently of that.)
#[test]
fn die_differenz_andersherum_bleibt_eine_schleife() {
    let c = erzeugt(&roh("return 4294967295 - t;"));
    assert!(
        !c.contains("atomic_fetch"),
        "`m - t` is not `atomic_fetch_sub`:\n{c}"
    );
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// A shift is no C11 fetch form at all, and it checks clean -- so only the table
/// keeps it out.
#[test]
fn eine_verschiebung_bleibt_eine_schleife() {
    let c = erzeugt(&roh("return t >> 1;"));
    assert!(!c.contains("atomic_fetch"), "{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// **A runtime operand stays a loop.** In the loop the body is re-run per pass;
/// as a fetch operand it is evaluated once. For a translation-time constant those
/// are the same value by construction. For a parameter they are the same only if
/// the emitter reasons about what may change between passes -- and it would then
/// be doing that silently.
#[test]
fn ein_laufzeitoperand_bleibt_eine_schleife() {
    let c = erzeugt(&roh("return t | p;"));
    assert!(!c.contains("atomic_fetch"), "{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// **A body with a side condition stays a loop** -- the whole corpus shape
/// (`beispiele/05`, `41`, `42`). It is not one operation, and no single
/// instruction computes it.
#[test]
fn eine_nebenbedingung_bleibt_eine_schleife() {
    let src = einheit(
        "atomic GESTUFT : u32 in 0 .. 1000 relaxed;\n",
        "GESTUFT",
        "u32 in 0 .. 1000",
        "if t < 1000 { return t + 1; } return t;",
    );
    let c = erzeugt(&src);
    assert!(!c.contains("atomic_fetch"), "{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// The identity body (`messung/proben/absenkung/probe-absenkung-exchange.gab`)
/// is not a binary shape and keeps its loop -- byte for byte what it had.
#[test]
fn der_blosse_binder_bleibt_eine_schleife() {
    let c = erzeugt(&roh("return t;"));
    assert!(!c.contains("atomic_fetch"), "{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

/// **A non-integer atomic has no fetch instruction in C11**, so the word list is
/// part of the table and not a formality.
#[test]
fn ein_bool_atomic_bleibt_eine_schleife() {
    let c = erzeugt(&einheit(
        "atomic JANEIN : bool relaxed;\n",
        "JANEIN",
        "bool",
        "return t;",
    ));
    assert!(!c.contains("atomic_fetch"), "{c}");
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
}

// ---------------------------------------------------------------------------
// The clauses are still demanded -- no refusal was lifted to build this arm.
// ---------------------------------------------------------------------------

/// **`bounded … ops on_exceeded …` stays mandatory even where the lowering is
/// one instruction.** The clauses lose their consequence, not their obligation:
/// lifting them would be a language change riding in on a lowering change.
#[test]
fn die_schranke_bleibt_pflicht_auch_fuer_die_holform() {
    let src = "module test::holform {\n\
         atomic ROH : u32 relaxed;\n\
         impl fn zug() -> u32 effects { reads ROH, writes ROH } costs <= 300 ops {\n\
         let alt : u32 = ROH exchange update(t) { return t | 4; } publishes nothing;\n\
         return alt; }\n\
         }\n";
    let (c, codes) = erzeugt_mit_absagen(src);
    assert_eq!(codes, vec!["C001"], "the missing clauses are still `C001`");
    assert!(!c.contains("atomic_fetch"), "{c}");
}

/// And so is the `never` exit: a bound whose exit returns is a number without a
/// consequence, fetch form or not.
#[test]
fn der_ausgang_muss_weiter_never_sein() {
    let src = "module test::holform {\n\
         atomic ROH : u32 relaxed;\n\
         impl fn heim() effects { pure } costs <= 2 ops { }\n\
         impl fn zug() -> u32 effects { reads ROH, writes ROH } costs <= 300 ops {\n\
         let alt : u32 = ROH exchange update(t) bounded 64 ops on_exceeded heim \
         { return t | 4; } publishes nothing;\n\
         return alt; }\n\
         }\n";
    let (c, codes) = erzeugt_mit_absagen(src);
    assert_eq!(codes, vec!["C001"]);
    assert!(!c.contains("atomic_fetch"), "{c}");
}

// ---------------------------------------------------------------------------
// The silencer both lowerings needed.
// ---------------------------------------------------------------------------

/// **An `exchange` result nothing reads back is `-Werror` in C, out of BOTH
/// lowerings** -- `unused-variable` from the single instruction,
/// `unused-but-set-variable` from the loop. Measured 2026-09-15 on
/// `probe/p3.gab`: both families fell. `Austritt::stille_exchanges` carries the
/// weighing, and the silencer stands after the declaration.
#[test]
fn eine_ungelesene_holung_wird_ruhiggestellt() {
    let src = "module test::holform {\n\
         atomic ROH : u32 relaxed;\n\
         extern fn aufgegeben() -> never effects { diverges };\n\
         impl fn zug() effects { reads ROH, writes ROH } costs <= 300 ops {\n\
         let alt : u32 = ROH exchange update(t) bounded 64 ops on_exceeded aufgegeben \
         { return t | 4; } publishes nothing; }\n\
         }\n";
    let c = erzeugt(src);
    assert!(c.contains("atomic_fetch_or_explicit"), "{c}");
    assert!(c.contains("(void)alt;"), "the silencer is missing:\n{c}");
}

#[test]
fn eine_ungelesene_schleife_wird_auch_ruhiggestellt() {
    let src = "module test::holform {\n\
         atomic ROH : u32 relaxed;\n\
         extern fn aufgegeben() -> never effects { diverges };\n\
         impl fn zug() effects { reads ROH, writes ROH } costs <= 300 ops {\n\
         let alt : u32 = ROH exchange update(t) bounded 64 ops on_exceeded aufgegeben \
         { return t; } publishes nothing; }\n\
         }\n";
    let c = erzeugt(src);
    assert!(c.contains("compare_exchange_weak_explicit"), "{c}");
    assert!(c.contains("(void)alt;"), "the silencer is missing:\n{c}");
}

/// And a result that IS read gets none -- a silencer on a live name would hide
/// the next real finding.
#[test]
fn eine_gelesene_holung_bekommt_keine_ruhigstellung() {
    let c = erzeugt(&roh("return t | 4;"));
    assert!(c.contains("atomic_fetch_or_explicit"), "{c}");
    assert!(!c.contains("(void)alt;"), "{c}");
}
