# Muse Report 1004: Exact review of author 854 (support-bytes closing)

## Candidate and verdict

CANDIDATE: 854 242ab56253f67b30fb8e1171c92939c2c4d37856

VERDICT: ACCEPT

Acceptance is bounded: scope bounds are listed below, all already stated as CUTS in the candidate file. The substantive verdict is unchanged by this format fix.

## What was reviewed

Author 854 ("Composition closing: support-bytes closing") adds one new Lean file
`grammatik/Grammatik/X86/ComposeSupportBytes.lean` (429 lines) plus one import
line in `grammatik/Grammatik.lean`, plus its own report. Pinned snapshot base
`b040b155` equals this clone's HEAD (branch `muse/1004` verified, tree clean
at review time); the snapshot's BUILD-EVIDENCE git log corroborates the
candidate hash (`242ab562` on top of `cc3fe4e4` on top of `b040b155`).

I inspected, in full: the owner task, the author report, the complete
533-line PATCH (every added line), BUILD-EVIDENCE.json, and the local
reference record (Intel SDM 325462-093US, September 2026, sha-pinned in
`.tmp/HARDWARE-REFERENCES/REFERENCES.json`; AMD unavailable, no AMD claim
made — consistent with the candidate, which claims no silicon correspondence).

## Verification performed (real evidence)

1. Producer cross-check (mechanical, in this checkout): every one of the 30+
   reused names exists with a matching definition/theorem — `valX86`,
   `valTore`, `valLayout`, `valZeuge`, `valWx` (ValidatorSkeleton);
   `torOkB`, `schreibTor`, `trapBytes`, `stubEndsTrapB`,
   `bindungErstelltB`, `zeugenMoves` (GateStub); `layoutFuer`, `layoutOk`,
   `slotAufz`, `zeugenU`, `zeugenU_schreibt`, `zeugenLayout_ok`,
   `zeugenSlot_ne` (TableLayout); `eintrittOk`, `zeugenSpeicherE`,
   `zeugenEintrittHosted` (EntryState); `mxcsrGueltig`,
   `mxcsr_ftz_verweigert` (Gleitprofil); `byteschritt`, `fetchDekodiert`,
   `schritt`, `byteschritt_weiter`, `byteschritt_verweigert_ohne_fetch`,
   `byteschritt_verweigert_ohne_schritt`, `ausgangByte`, `ausgangRip`
   (Byteschritt); `bildZustand`, `bildStore`, `bildStoreStart`,
   `bildStoreStartMutiert`, `bildStore_schritt_speichert`,
   `bildStore_datenRip_verweigert`, `bildStore_mutiert_verweigert`,
   `storeReg`, `storeFlags`, `geladen` (LoadedExecution/Bild);
   `schreibLese_zeuge` (Bild). No producer file is modified by the PATCH.
2. Queued-wrapper reproduction (read-only, no source touched):
   `./lean-probe grammatik/Grammatik/X86/LoadedExecution.lean` → 0 errors;
   `./lean-probe grammatik/Grammatik/X86/Byteschritt.lean` → 0 errors;
   `./lean-probe grammatik/Grammatik/X86/Gleitprofil.lean` → 0 errors.
   Reported axiom footprints are `[propext]` / `[propext, Quot.sound]`,
   matching the producers (Quot.sound is inherited, e.g. via the
   `wohlgeformt_*` simp legs — no new axiom).
3. Hand-verified load-bearing steps against producer definitions read in
   this checkout: `stuetzWit_schritt ... := rfl` holds definitionally
   (`bildZustand` builds exactly the updated `stuetzWitS` record);
   both step-refusal inversions are valid `ausgangRip` case splits over
   accepted `... = none` refusals; `valTore [tor]` follows from `torOkB`
   by unfolding `List.all`; `stuetzOk_teile` is a sound `Bool` inversion.
4. Forbidden-tactic scan of all added lines: no `sorry`, `admit`, `axiom`,
   `native_decide`, `unsafe`; no `Prop`-typed premise; every theorem
   premise is used.
5. Author BUILD-EVIDENCE shows an honest trail (several failing
   `./lean-probe` iterations fixed during development) ending in
   `./lean-bau` green (511 jobs) and probe 0 errors.

## Architecture review (not just Lean green)

- The candidate defines no instruction semantics, decoder, loader, or
  executor: byte forms, REX/register/width/flag behavior, operand roles,
  pre-fault effects, and memory-access order are all inherited from the
  accepted `fetchDekodiert`/`schritt` via `byteschritt`. Nothing is
  re-decided or re-interpreted, so there is no invented determinism and
  no zeroed/ignored defined effect. This is the correct shape for a
  composition lane.
- `stuetzSchritt` forces caller memory to `geladen bild bias`, so no
  unvalidated byte is ever fetched — the closing's core mechanism, and
  genuine execution (not a conjunction of checks) via the reached run.
- MXCSR, entry-state, gate, layout, and trap-suffix halves are admission
  `Bool`s, never execution or silicon claims. TSO/atomicity: the file
  claims nothing beyond per-byte model memory and explicitly leaves the
  per-access W/GX bridge to owners 573-574. Interrupt-enable (IF) is
  inside accepted `eintrittOk`, reused, not re-judged. Sound abstraction
  throughout; the REPAIR triggers in the lane task do not fire.
- Witnesses are non-degenerate and memory-changing: computed layout
  accepted, carrier enumeration nonempty, `setze` writes `konto`, real
  write/read change (`schreibLese_zeuge`), reached run storing 42 into
  `0x102000` through the composed step with zero-before. Planted
  refusals are genuine inversions of accepted producer refusals
  (data-section RIP, forged REX.X opcode, W^X image, FTZ word), with the
  mapping-still-holds pins at producer level.
- No guarantee weakening: purely additive (one file + one import line);
  all refusals are `= false` inversions; no source/checker/Spec/goal/
  emitter/optimiser edits; no new diagnostic/gift/example/CLI numbers;
  no MARKE_EMIT changes.

## Accepted bounds (all already CUTS in the file — no fake closure)

1. Split-image witness: admission is exhibited on the minimal `ret` image
   (`valZeuge`), the storing run and step refusals on the store image
   (`bildStore`). No single image exhibits an admitted thread-root entry
   together with a storing run. (Root cause visible in producers: the
   store entry is `0x101000` at bias `0x100000` while the hosted entry
   witness sits at `0x1000`/bias 0.) The generic theorem is over one
   arbitrary image; only the end-to-end instance is split. Disclosed.
2. `StuetzArt` (`arena`/`faden`/`gleit`) appears in no theorem statement:
   the closing is uniform over image bytes and the per-kind mapping
   (layout/entry/MXCSR halves) is documentary. A per-kind statement or
   removal is follow-up work, not a soundness defect.
3. `eintrittOk` is fixed at bias 0 while `stuetzSchritt` takes arbitrary
   bias; no cross-leg transfer is claimed, so nothing false follows, but
   a future tightening should thread bias through `stuetzOk`.
4. No source correspondence (waits on IR lane 287), no hardware
   correspondence, no TSO/W/GX bridge, no budget transfer, no
   whole-binary/relocation/ABI claims — each cut with its owning lane.

## Review boundary (honest partial status)

The candidate file itself was verified by complete textual inspection plus
producer cross-checks plus hand derivation of the load-bearing steps — not
by probing the candidate file in this clone: applying the staged patch
would have touched source files this review lane does not own (and the
`git apply` from the staging path was refused), so I reproduced the three
load-bearing producer modules through the queued wrapper instead, all
green. I did not run full `./lean-bau` (no source change was made by this
lane, so there was nothing of mine to build). Re-verification at merge
time via the merge gate's build remains appropriate and is not waived by
this ACCEPT.

## Task remarks

- Nothing in the lane task text appears wrong; the ZEUGE line
  (`ComposeSupportBytes_verbindung` + `_zeuge`, jointly inhabited,
  non-degenerate, memory-changing reached run) is met within the
  split-image bound above, which the author discloses rather than hides.
- Suggested follow-ups for the coordinator (none verdict-flipping):
  single-image admitted-entry + storing-run witness; use-or-drop
  `StuetzArt`; thread bias through `stuetzOk`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/LoadedExecution.lean`: `0 error(s)`,
exit 0. `./lean-probe grammatik/Grammatik/X86/Byteschritt.lean`: `0
error(s)`, exit 0. `./lean-probe grammatik/Grammatik/X86/Gleitprofil.lean`:
`0 error(s)`, exit 0. Full `./lean-bau` not run by this lane (no source
changes owned; see boundary above). Author evidence: `./lean-bau` `Build
completed successfully (511 jobs)`, exit 0.
