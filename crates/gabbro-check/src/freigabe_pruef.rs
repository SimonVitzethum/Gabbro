//! **The release refusal (lane 263, OFFEN O12 half (2)).**
//!
//! At every exit of a locked section (`release`, early `return`, `leave`, `next`) the
//! lock invariant must FOLLOW from the invariant at acquire, the section's own writes
//! and what the section's callees PROMISE (their `ensures`) -- never their bodies.
//! What cannot be shown is refused with **`N511`**, naming the invariant, the lock,
//! the exit and the cell(s) whose value is not determined.
//!
//! The verdict is [`crate::freigabe::beurteile`], shared with the `RELEASE HOLDS` rows
//! of `gabbro obligations --g` and `gabbro counterexample`: one analysis, one verdict,
//! so the row and the refusal agree by construction (pinned by
//! `freigabe_zeile_und_n511_stimmen_ueberein`).
//!
//! What stays silent, and why:
//!
//! * `beispiele/119` (lane 204 measured a promises-only rule would falsely refuse it):
//!   `k.slots[0].x = 40` through `k : ptr<normal, rw> A` establishes `A.slots[0].x == 40`,
//!   and `40 <= GRENZE` (`GRENZE == 100`) re-establishes the bound. The rule reads the
//!   write through the parameter and the constant through the `const`, so the section
//!   holds -- a promises-only reading was the false positive, not the program.
//! * `beispiele/124` and `beispiele/157`: `setze` promises both slots (`s0 == s1`), so
//!   both sections hold from the callee's promise.
//! * `beispiele/118`: signature-held, no `locks` section -- silent by construction.
//!
//! The sentence stands at `saetze::SPERREN` as `sperren.freigabe`.
//!
//! Model correspondence (stated, not proved -- OFFEN O12): this refusal discharges the
//! release half of `SperrWechselG` (`grammatik/Grammatik/Zielsatz/Spec.lean`: every
//! release leaves a memory where the lock invariant holds), with the acquire half as
//! the frame premise. The bridge from the Rust verdict to the G term is open: the
//! analysis runs on surface syntax, the leg on `RufMaschineG` memories.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

use crate::freigabe::{Abschnitt, beurteile, menge_text};

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    for abschnitt in &beurteile(baum) {
        let crate::freigabe::Abschnitt::Urteil(u) = abschnitt else {
            continue;
        };
        for ausgang in &u.ausgaenge {
            if ausgang.fehlt.is_empty() {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "N511",
                    ausgang.span,
                    format!(
                        "the locked section in `{}` locking `{}` cannot re-establish the \
                         invariant over {} at the `{}` exit: {}",
                        u.funktion,
                        u.sperre,
                        menge_text(&u.braucht),
                        ausgang.art,
                        ausgang.fehlt.join("; ")
                    ),
                )
                .mit_notiz(
                    "a `locks L { … }` exit must re-establish the lock invariant from the \
                     invariant at acquire, the section's own writes and what its callees \
                     PROMISE (their `ensures`), never their bodies. Strengthen a callee's \
                     `ensures`, write the cell in the section, or move the write before \
                     the last promising call",
                ),
            );
        }
    }
}
