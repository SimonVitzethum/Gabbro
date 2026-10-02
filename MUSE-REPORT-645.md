# MUSE-REPORT-645: Independent review of lane 644 (source-to-final-byte closure plan)

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a645`, branch `muse/645`
  (`git rev-parse --show-toplevel` and `git branch --show-current` confirm).
- Pinned snapshot: author 644, HEAD `ef8e47df794053b1f6fdb05aad1bd742610cc386`,
  base `24e625c0bd1eee21de891d417c18dc4d64d8af0c`, `clean: true`.
- Candidate scope verified by direct diff `base..head`: exactly 2 added files,
  `MUSE-REPORT-644.md` + `dokumente/x86/SOURCE-CLOSURE-PLAN-644.md`
  (641 insertions, 0 deletions of tracked content). No Lean, checker, Spec,
  goal, Rust, emitter, ledger or control file touched. Report-only review:
  no source edits made by this reviewer.

CANDIDATE: 644 ef8e47df794053b1f6fdb05aad1bd742610cc386

VERDICT: ACCEPT

## What was checked (independently, in this clone)

1. **Scope.** `git diff base..head --stat` shows only the two owned paths.
   No umbrella import, no friend-reserved optimiser file, no ledger edit.
2. **Producer definitions resolved in-tree** (each name the plan cites):
   - 599 `ExpressionLowering.lean`: `senkFrag`, `senkung_korrekt`,
     `senkFrag_verweigert_mul/tief` present.
   - 628 `SourceAssignmentLowering.lean`: `senkAssign_korrekt` carries
     `hExec`/`hTgt`/`hRd` plus `hOk`/`hsenk`/`hrenv`/`hFr`/`hrsp`/
     `hBasis`/`hBaseR`/`hdisp`/`ha`; joint witness
     `senkAssign_korrekt_zeuge` present. Matches the plan's premise list.
   - 634 `quellDaten_schritt_laesst_code` + `_zeuge` present.
   - 630 `fragmentDelta_voll` present.
   - 598 `valEintrittStark` present.
   - 603 `GruppeNachW` inductive + `keine_gruppe_nach_w` void bridge
     present; the plan correctly reports no source-bridge claim inside.
   - 565 `fpEncodeMovsdRR`/`fpDecode`/`fpGeholt`/`fpByteschritt` and the
     refusal family present.
   - 632 `SourceValidatorConnection.lean`: `witD`, `srcCertOk`, `.p48`
     pin, `srcCert_sound` + joint witness, four planted refusals
     (bytes/profile/map/base) present. The plan's "fixed witness,
     off the generic trust path" characterisation is accurate.
3. **Task count.** Eight follow-ups T-A through T-H, exactly at the
   allowed maximum. All eight NEW paths (`BranchLowering`,
   `CallLowering`, `ValidatorAdapter`, `AccessSimulation`,
   `FoldCertificate`, `ValidationCost`, `ProfileClosure`,
   `NarrowLowering`) confirmed absent from `grammatik/Grammatik/X86/`.
4. **No duplication.** In-flight lanes 646/648/650/652/654/656/658 all
   exist with their boundaries respected in §6; `ExtendedExecution.lean`
   is named as 575-reserved, not re-owned; no second IR, miniature
   interpreter, alternative executor or parallel checker is proposed.
5. **No fake closure.** 632's replacement is specified as three parts
   that "no single lane may collapse" (full-unit computation,
   generic `valX86_sound`, derived `schluss_x86`); `adapterZerlegung`
   explicitly claims no soundness; M1–M10 register stays OPEN;
   §4 separates decoders from silicon fidelity; §8 rejection
   criteria cover desired-premise smuggling, proof-valued
   certificates, quantified-away ghosts, `ensures` derivation,
   warning-downgrades, per-program rules, unbridged W/GX reuse,
   guarantee weakening, Rust-print trust and degenerate witnesses.
6. **No speculative numbers.** No percentage, ETA, speedup or
   maximum-performance claim found; validation cost is stated as
   fuel/work bounds with exhaustion-to-refusal, cache as
   recompute-on-hit congruence. The standing 15-model policy is
   cited without inflating it into a completion claim.
7. **Mechanics.** All 15 relative links in the plan resolve to
   existing files; `git diff --check` over `base..head` is clean.
   Note: link check re-ran in this clone (different working base),
   same 15/15 result as the author's evidence.

## Accepted bounded claim

The candidate is an organiser work plan, not a proof: it assigns
exact NEW-file ownership, accepted-only producer dependencies,
statement sketches, non-degenerate witness demands and semantic
rejection criteria for eight follow-up tasks toward generic
source-to-final-byte validation, with `SourceValidatorConnection632`
fixed as a witness and its three-part generic replacement named.
It proves nothing and closes nothing; every future ACCEPT/REPAIR
stays with the paired reviewer on the exact committed candidate.

## Minimal notes (not repairs)

- Line references in the plan point at the author's pinned base;
  this clone sits at a different base, so line numbers were
  verified by symbol, not by line. All symbols resolved.
- `lanes/646.md`–`lanes/658.md` name no owned Lean file at this
  base either, consistent with the report's stated collision check
  plus coordinator re-check at launch.
- T-D and T-F both gate on accepted 654; the plan staggers them
  explicitly (§9). Coordinator must enforce this at dispatch.

## CUTS

- Review-only lane: no theorems added, no `#print axioms`
  applicable, no `lean-bau` run required (zero Lean files in
  candidate; docs-only scope confirmed by diff).
- Everything the plan marks OPEN (M1–M10, T-A–T-H, `valX86_sound`,
  per-access TSO→W/GX simulation, `f32` path, whole-image
  reachability) remains OPEN after this review.
