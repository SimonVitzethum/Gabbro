//! **`publishes { payload }` / `awaits { payload }` — the memory orderings of message passing.**
//!
//! The payload of a publication is written by ordinary stores BEFORE the flag store, and the
//! payload of a reception is read by ordinary loads AFTER the flag load (the checker holds
//! both facts: V001-V004 pair the places, V009-V011 the branch fact, `N270` forbids a bare
//! store). What this backend owes is therefore exactly one thing: the flag store must order
//! every earlier write before itself (release), and the flag load must order every later read
//! after itself (acquire). LLVM keeps ordinary accesses on the right side of a release store and
//! an acquire load, on x86_64 (plain `mov`, TSO) and on aarch64 (`stlr` / `ldar`).
//!
//! **Source of the ordering.** LANGUAGE.md §11.1/§11.5: `publishes` forces AT LEAST release,
//! `awaits` AT LEAST acquire; `seq` is the stronger declaration and stays. The C emitter
//! (`emit.rs`, `atomics.insert`) maps the declaration the same way (release/acquire -> release
//! store + acquire load, `seq` -> `seq_cst` on both). The Lean model: machine G reads the
//! atomic as one sequentially consistent word, and `SchwachX` (Zielsatz, the atomic rely)
//! answers a shared-atomic read from the weak memory -- release/acquire pairing is the weakest
//! order for which the DRF-SC bridge holds, so a declaration of `relaxed` (or none, which
//! the LLVM backend reads as `seq_cst`, see `sammle_atomic`) is never taken as WEAKER than that
//! pair. Chosen: store = `seq_cst` if declared `seq` (or undeclared), else `release`; load =
//! `seq_cst` if declared `seq` (or undeclared), else `acquire`. Never weaker than the pair.

use super::*;

/// Store ordering for the stored declaration string (`acquire`, `release`, `seq_cst`,
/// `monotonic`): `seq_cst` stays, everything else is lifted to `release`.
pub(super) fn schreib_ordnung(deklariert: &str) -> &'static str {
    if deklariert == "seq_cst" {
        "seq_cst"
    } else {
        "release"
    }
}

/// Load ordering for the stored declaration string: `seq_cst` stays, everything else is
/// lifted to `acquire`.
pub(super) fn lese_ordnung(deklariert: &str) -> &'static str {
    if deklariert == "seq_cst" {
        "seq_cst"
    } else {
        "acquire"
    }
}

/// The declared ordering of the atomic behind a place (`REGEL[r]` is its base name).
pub(super) fn deklarierte_ordnung(k: &Koerper, ort: &Ort) -> String {
    k.s.atomare.get(&ort.basis.text).map(|(_, o)| o.clone()).unwrap_or_else(|| "seq_cst".to_string())
}
