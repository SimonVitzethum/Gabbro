# MUSE-REPORT-1120: Exact review of candidate 1119 (LOCK/RMW)

Lane: 1120. Reviewer lane, report-only. Owns only this file.

## Verdict

CANDIDATE: 1119 aea7085a53a6936270494df250fa961927c6ff3e

VERDICT: ACCEPT

Pinned base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`, snapshot clean.
Reviewed from the coordinator snapshot in `.tmp/review/author-1119/`
(`PATCH.diff`, 835 lines; `MUSE-REPORT-1119.md`; `OWNER-TASK.md`;
`BUILD-EVIDENCE.json`), cross-checked against my own clone's accepted
662/660 modules. No unsupported desired-correctness premises, no weakened
guarantees, no fake closure found.

## What was checked

- Scope: exactly 3 files (`MUSE-REPORT-1119.md`,
  `grammatik/Grammatik.lean` (+1 import line, confirmed in diff),
  `grammatik/Grammatik/X86/HwLockRmw.lean` new, 721 lines). No existing
  file edited or weakened.
- Forbidden tokens over the full diff: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`, `sorryAx` in code (matches are prose only);
  no `axiom` declarations; no `intro _` / `have _ :=` premise discards.
- Axioms: author evidence shows every main theorem within the standard
  trio (max `[propext, Quot.sound]`); per-theorem `#print axioms` present
  (30 prints, one per main theorem plus pins).
- Premise use (manual audit of every theorem): each premise flows into
  the accepted 662 equation (`hstep`), the read-back lemma, or the
  refusal bridge. `hles`/`hwr` pin the read-back/write-back conjuncts;
  `hfehl`/`hfehlt`/`hfehl` select the exact refusal equation. Nothing
  vacuous; conclusions are computed outcomes, not renamed premises.
- Lifted, not copied: `hwLockSchritt`/`hwLockSchrittEv` call the
  accepted `lockSchrittVoll`; agreement theorems rewrite with the
  accepted equations. All 8 cited 662 equations verified present in
  `LockedInstructionExecution.lean`, all 14 cited helpers
  (`lockZeugSpeicher`, `lockZeugReg`, `hwOhneSse2`, `basisHw`,
  `basisBereit`, `hwWf_aus_zugelassen`, `setTso_wf`,
  `setKernDaten_wf`, `tsoAnsicht`, `flushKern`, `loadByte`,
  `read64_nach_write64`, `write64_braucht_schreibbar`,
  `lockAufRegister`) verified present in this clone's tree. Witness
  memory/register definitions reused from 662, not duplicated.
- Refusals really refuse: 4 general refusal theorems (register/fence
  #UD, pending own store, misaligned, SSE2-off fence) each via its
  accepted 662 equation through the ok/none bridge; 5 closed pins
  (`reg_ud`, `puffer`, `unaligned`, `sse2`, `lesefehler`,
  `schreibfehler` + art pins) by `decide` on concrete machines; the
  failing-CMPXCHG shape has a permitted-failure positive twin
  (`cmpxchg_nein_ok`: word stays 10, rax takes 10).
- Witness non-degenerate: `hwLock_zeuge`, 15 conjuncts on reached runs
  — word 10->15 (core 0) ->22 (core 1), memory-changing steps on two
  cores, owner-only forwarding (99 vs 0), shared 99 after drain, `HwWf`,
  all five refusal shapes beside the run.
- Silicon: no new silicon claim; CUTS cites SDM rows via accepted 662
  and records the author's honest scoping note (task says "aligned
  WortGruppe", lifted guard is 662's `ausgerichtet8`; distinction
  recorded, no second check invented).
- CUTS honest: disclaims hardware correspondence beyond
  self-consistency, fetched-byte dispatch, W/GX refinement,
  linearisation, timing/progress, narrower widths and split-lock
  detection. No claim larger than the proof.

## Verification runs

- `./lean-bau` in this clone (base, no Lean change by this lane):
  `Build completed successfully (602 jobs)`, first line
  `== exit 0; 0 error line(s) in the COMPLETE output`. Green.
- Candidate build evidence (author clone): `./lean-probe` 0 errors at
  every commit, final `./lean-bau` 601 jobs green. Not independently
  re-executed here (would require applying the candidate into this
  clone's `grammatik/`, outside my owned files); static verification
  above plus the clean snapshot support this ACCEPT.

## Remarks (non-blocking)

- Report wording "replacing the refusal" overstates: `adapterLocked662`/
  `hwLock_verweigert` correctly remain (no-edit rule); the new
  `adapterLockRmw` coexists, unwired to fetch dispatch — honestly cut.
  No behavioral conflict: plugs are values, nothing dispatches both.
- `hwLockWit_mfence_ok` rip arithmetic (4096+3=4099) consistent.

## Definitions/theorems added by this lane

None — reviewer lane, report-only by design.
