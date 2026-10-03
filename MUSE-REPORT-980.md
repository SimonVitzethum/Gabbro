# MUSE-REPORT-980: Exact review of author 830 (spill-privacy closing)

## CANDIDATE and VERDICT

- CANDIDATE: 830 735b6d5aa59c4a95e69b2510ff4853b4be5eaecf
- VERDICT: ACCEPT (bounded: composition closing only, per CUTS below)

Snapshot base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4` equals this
clone's HEAD on branch `muse/980`; snapshot reports `clean: true`.
Pinned files: `MUSE-REPORT-830.md`, `grammatik/Grammatik.lean` (one added
import line), `grammatik/Grammatik/X86/ComposeSpillPrivacy.lean` (new,
259 lines). BUILD-EVIDENCE shows the candidate committed as `735b6d5a`
with `lean-bau` green at 509 jobs.

## Task fidelity

Owner task: close allocation spills to fresh private frame slots,
token-threaded, disjointness plus permissions checked, save/restore on
all paths; compose accepted modules without re-proving internals or
duplicating an interpreter; ZEUGE `ComposeSpillPrivacy_verbindung` with
companion `ComposeSpillPrivacy_verbindung_zeuge`, jointly inhabited,
non-degenerate, memory-changing reached run. The candidate delivers
exactly this interface: `spillPrivatSchritt` threads one
`Option Speicher` token through checked save then checked reload, so any
refusal yields `none` loudly.

## Independent verification (this review)

- Reproduced with the queued wrapper on the exact snapshot content:
  `./lean-probe .tmp/review/author-830/grammatik/Grammatik/X86/ComposeSpillPrivacy.lean`
  prints `== 0 error(s) in the COMPLETE output; exit 0`.
- `#print axioms` (reproduced): every new theorem depends only on
  subsets of `[propext, Quot.sound]` (several on no axioms); within the
  `gabbro_ziel` standard set. No new project-wide axiom.
- Forbidden-token scan of the pinned file: no `sorry`, `admit`,
  `axiom` (declaration), `native_decide`, `unsafe`, `intro _`,
  `have _ :=` (only hits are the words "admitted" in comments and the
  required `#print axioms` lines).
- Every referenced producer name verified present in the base tree with
  matching role: `spillSlot`, `SpillFrisch`, `GetrenntK`,
  `spillPrivatOk`, `SpillZugelassen` (a `def` unfolding to validator
  admission `/\` freshness, matching the `⟨hok, hfrisch⟩` construction),
  `spill_speichern_ist_write64`,
  `spill_zugelassen_verweigert_genommen`, `spill_frisch0`,
  `spill_getrennt_rW`, `spillSlot_rW_null`, `spillTSO0`,
  `spillRahmenW`, `speicherZeuge`, `sichereWort`, `ladeWort`,
  `sichere_lade_rundreise`, `sichereWort_erhaelt_berechtigungen`,
  `sichereWort_ausserhalb`, `sichereWort_verweigert`, `read64_rahmen`,
  `writeBytesN_hit`, `addrOff_null`, `zeugenU`, `zeugenU_schreibt`.
- Premise use: `hb`/`hrd`/`hwr` through round-trip and permission
  preservation, `hok`/`hfrisch` through joint admission,
  `hdis`/`hwr` through foreign stability, `hrd2` by injection against
  the round-trip. No unused premise, no `Prop`-typed premise.
- No conclusion-is-premise: `w = v` is derived by injection of two
  independent loads; the step equation, admission, permissions, foreign
  `read64` stability and reload are each genuinely derived.
- Joint witness instantiates all seven closing premises on
  `speicherZeuge`/`spillZeuM1`/`spillRahmenW`/slot 0/`42`/`16`/
  `spillTSO0`, beside `zeugenU_schreibt` (table `konto` written by
  `setze`, confirmed in `TableLayout.lean`), the observable memory
  change (slot byte `0x00` becomes low byte of `42`) and the threaded
  step equation. Non-degenerate by the lane standard.
- Planted refusals, each showing raw save AND composed step are `none`:
  address-taken (`verweigert_genommen`), out-of-frame
  (`verweigert_aussen`), write-protected (`verweigert_schutz`).

## Architecture (not just Lean green)

- No new ISA/byte forms, no REX/register/width/flag semantics, no
  decoder or execution claims; imports are only `SpillPrivate` and
  `TableLayout`. No second IR, no second evaluator.
- No invented determinism and no ignored defined effects: refusals
  propagate as `none` on every path; the save IS the accepted
  permission-checked store (`spill_speichern_ist_write64`).
- No TSO/multi-byte atomicity beyond byte-extensional commutation of the
  accepted producers; the file explicitly CUTS aligned multi-byte
  atomicity, LOCK RMW, source-to-target simulation, `valX86_sound`,
  cost/fairness/timing. Feature/MXCSR/interrupt gates are untouched and
  unclaimed. No vendor/silicon claim (local reference is Intel SDM
  edition 093, Intel-profile only; the module adds no hardware claim).
- Missing legs are explicit CUTS naming owners 287/303 (SCFG side),
  573/574 (W bridges), 575 (extended decoder) — never assumed.
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files. Base tree contains no `ComposeSpillPrivacy` reference, so the
  candidate applies cleanly onto this base.

## Review method note

Two `git` invocations were refused by the permission classifier
(`git log --all --grep`, `git show <commit>:<path>` via process
substitution). Worked around with in-clone `rg`/file reads and the
queued `lean-probe` reproduction above; no evidence gap results.

## Open (as CUT by the author, endorsed)

SCFG-side application (287/303), W store/read bridges (573/574),
extended decoder path (575), aligned multi-byte atomicity, LOCK RMW,
source-to-target simulation, `valX86_sound`, cost/fairness/timing.
