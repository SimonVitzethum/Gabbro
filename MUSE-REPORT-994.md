# MUSE-REPORT-994: Exact review of author 844 (profile-selection closing)

CANDIDATE: 844 929e23b253cf1478015effba88bc988d832e109c
VERDICT: ACCEPT (bounded; scope is the zeroing form family only, per the file's own CUTS)

## What was reviewed

- Pinned snapshot: base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, files
  `MUSE-REPORT-844.md`, `grammatik/Grammatik.lean` (+1 import line),
  `grammatik/Grammatik/X86/ComposeProfileSelect.lean` (new, 193 lines).
- Owner task (lane 844): close backend form choice to the named CPU
  profile, tuning-only measured traits, every selected byte re-validated,
  generic over arbitrary admitted inputs, reached memory-changing runs
  plus planted refusals, missing legs as explicit CUTS.
- Reference: local Intel SDM snapshot (`REFERENCES.json`, edition
  325462-093US, sha256-verified 2026-10-02): MXCSR Figure 10-3 and
  section 10.2.3.3 confirm FTZ is bit 15.

## Independent verification (each producer use checked against this clone)

- `composeInstr_eq_waehleNull`: `waehleNull` (`InstructionSelection.lean:29`)
  is `if flagsLive then [.movImm64 dst 0] else [.xorReg64 dst dst]`;
  `composeInstr` is its single element. Proof by `cases + rfl` is exact.
- `compose_zero`: routes through canonical `schritt` with explicit
  lengths rewritten by `null_laengen` (`10 vs 3`) into exactly the
  premises of accepted `schritt_null_mov` / `schritt_null_xor`. Lengths
  match the pinned bytes (`pin_xor_rax` = 48 31 C0, `pin_mov0_rax` =
  48 B8 + imm64). No length is invented.
- `compose_bytes_revalidated`: `roundtrip (b) (suffix)`
  (`Codec.lean:561`) has exactly the stated shape, generic over all
  `Befehl` including both composed forms. `ValidatorSkeleton` imports
  `Codec` and uses canonical `decode` for coverage (incl.
  `decodeErw_kanonisch`: extension never shadows it), so the "same
  canonical decoder" claim is true.
- `compose_profil_verweigert`: `sse_verweigert_bei_ftz` is about exactly
  `merkmalZugelassen basisHw <0x9F80, true> .sseDoppel = false`, and
  `waehle_verweigert_strikt` turns exactly that into the `waehle = none`
  conclusion. 0x9F80 = 0x1F80 | 0x8000 sets MXCSR bit 15 (FTZ, confirmed
  in the Intel SDM text); the profile requires FTZ off
  (`mxcsrGueltig`, `Gleitprofil.lean:36`). Architecturally grounded,
  reused from accepted lanes, nothing invented.
- `compose_live_refuses_clobber` / `compose_dead_allows_clobber`:
  after the `rfl` rewrite the goals are exactly accepted
  `wahlOk_verweigert_xor_le` / `wahlOk_erlaubt_tot`. Real refusal plus
  positive twin, both through the composed definition.
- `ComposeProfileSelect_verbindung`: all four conjuncts discharged from
  the lemmas above plus accepted `schreibLese_zeuge` (`Bild.lean:454`,
  nonzero write 42 reads back, byte observably changes). Every data
  premise is used; no Prop-typed premises; no `intro _`; conclusion is a
  proved conjunction, not a restated premise.
- `ComposeProfileSelect_verbindung_zeuge`: ONE joint application of
  `verbindung` at concrete values plus accepted `wit_schreibt`
  (contract writes its table, `rfl`) and `wit_step` (reached run, slot
  reads 5; statement matches the restated match-expression exactly).
  Non-degenerate: table-writing contract and memory-changing reached
  runs on both the source side and the image-memory side.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (grepped the snapshot file; only `#print axioms` lines match
  "axiom"); `#print axioms` per BUILD-EVIDENCE are subsets of
  `[propext, Classical.choice, Quot.sound]`; `./lean-probe` 0 errors;
  `./lean-bau` 509 jobs green at the author base. File list is the new
  module + one import line + report: no diagnostic/gift/example/CLI
  numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits,
  no friend-reserved optimiser files.

## Bounded acceptance and precise claim boundary

- Accepted: profile-gated zeroing-form selection composes fail-closed
  fallback, flag-liveness gating, canonical re-decoding and canonical
  zeroing execution, with joint witness and planted refusals.
- NOT claimed (file's CUTS, accurate): no `valX86` image embedding of
  composed bytes; no source lowering correspondence; no budget
  transfer; no call-log effect; no silicon/hardware claim; no
  cost/time claim (tuning-only is about values); only the zeroing
  family is composed (multiply/shift/vector/LOCK stay with owners).

## Non-blocking notes (do not affect the verdict)

- At the concrete witness, leg 3's premise (`waehle basisHw basisBereit
  .skalar64 = none`) is false since scalar is admitted on baseline, so
  that leg is vacuous at the witness point; the generic leg is fully
  proved. A refused-feature instance (e.g. via `compose_profil_verweigert`)
  would exercise the fallback literally.
- At `valZeugeZustand` all registers read 0, so the concrete
  `compose_zero` instance is value-vacuous there; the generic theorem
  covers arbitrary (nonzero) states. A witness state with `rax != 0`
  would show a literally-changing composed-step run.

## Review method note

- The candidate module is not present in this clone (verified: no
  `ComposeProfileSelect*` under `grammatik/Grammatik/X86/`), so no
  rebuild of the candidate was run here; every reused producer
  statement was read and checked in this clone instead, and all match
  the candidate's use exactly. Build evidence (`lean-probe` at each
  step, final `lean-bau`, axiom prints) is complete and consistent.
- No source files touched: this review owns only this report.
