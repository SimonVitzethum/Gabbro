# MUSE-REPORT-1282: exact re-review after author repair

CANDIDATE: 1281 0df79741a3fb88e905171bd1467acfb986f2c317
VERDICT: ACCEPT

## Materials and procedure

Clone `/home/simon/Dokumente/gabbro-muse/a1282`, branch `muse/1282`, verified.
Re-reviewed the NEW pinned snapshot only (`.tmp/review/SNAPSHOT.json`: head as
in the candidate line above, base `738366545afbddf7ac664db92804703db24f8868`,
`clean: true`; author repair commit `6d011bb2` plus report commit `0df79741`).
Read the full new `IntSignXchg.lean` (1779 lines) at the changed regions,
`PATCH.diff` (same three owned files, single import line), the updated
`MUSE-REPORT-1281.md` (now with a repair section), and the extended
`BUILD-EVIDENCE.json` (final `./lean-bau` green, 659 jobs, same axiom sets).
The previous repair decision is superseded by this re-review; every prior
finding was re-inspected below. Own tree `grammatik/` untouched; reviewer added
no definitions. Last `./lean-bau` on this clean tree (no changes since):
`Build completed successfully (672 jobs).`

## Prior findings, each re-inspected

- Primary defect (REX-prefixed `90H` self decoded as zero-extending exchange):
  FIXED. `decodeSx90` now routes every `90H` with `bb == 0 && lo == 0` to
  `.nop` at length `npfx + 1` under every prefix combination; the old
  REX.R gate on the 64-bit arm is gone (`_rb`, uniformly ignored, matching the
  stated assumption). New `decide` pins cover `[40,90]`, `[66,90]`, `[48,90]`,
  `[4C,90]`, `[66,48,90]` as NOP; the old wrong-behavior pins are gone.
- Label-only rows (`66 90`, `48 90` as identity exchanges): FIXED, same edit.
- Refused-but-valid rows (`4C/4D 90`, `66`+REX.W `90`): FIXED, now correct NOPs.
- Missing no-shadow rows: FIXED. New `decodeExt = none` rows for `[40,90]`,
  `[4C,90]`, `[66,48,90]`; CUTS count updated to 19, matching the file.
- CUTS citing the NOTE: FIXED. The alias NOTE is cited, the assumption list
  states every RAX-self `90H` changes nothing but RIP, and the canonicalization
  to the `87` forms is documented with the equivalence theorems named.
- Repair side change (top-level REX.X refusal dropped, now ignored): checked
  SAFE. Every ModRM use requires `mod == 3`, so no SIB shape can enter; no pin
  or table row depended on the old refusal.

## Checks on the repaired candidate

- Forbidden tokens: clean re-scan (only English "admit*" in comments). Axiom
  prints unchanged in kind (`propext` / `propext + Quot.sound`).
- Honest reshaping, no weakened-guarantee relabeling: the three
  `sxRoundtrip_xchgRax*` carry an explicit `r ≠ .rax` premise discharged by
  `absurd rfl hne` (premise used, self case excluded openly); the self case is
  covered by the new step-equivalence theorems `sxXchgRax16/32/64rax_ist`
  (proved `cases <;> simp`, premises used). Encoder pins rewritten to the
  `87`-family bytes; no `90H` byte encodes a zero-extension anymore.
- Earlier passing checks re-confirmed unaffected: lift theorems, accepted-XCHG
  bridge, flag/memory silence, halt-freedom, adapter/embedding theorems, joint
  witness (uses a distinct-register exchange and TSO legs the repair does not
  touch), LOCK/memory refusal directions, single-import file discipline.
- Author report now records the repair (defect accepted as wrong definition,
  commit named, verification restated). Its older body bullets still carry
  stale counts and the superseded redundant-REX sentence; the Lean CUTS is the
  consistent record. Non-blocking nit, listed below.

## Nits for follow-up (not blocking)

Stale prose inside `MUSE-REPORT-1281.md` body (§5 row count, §6
redundant-REX sentence, §8/§10 pin counts — the file's CUTS is correct).
Two CUTS over-refusal bullets look like stale text for refusals that no
longer occur ("non-`0x48` REX on `98`/`99`", "REX without W on `87` outside
`66`": the decoder correctly accepts those valid inputs, e.g. REX.B-extended
forms). Harmless direction, suggest rewording on a later touch.

## Open (unchanged)

No silicon proof beyond the cited rows (author scope, accepted); no W/GX
bridge, timing, source/loader/entry/budget link. Nothing in this candidate
claims them.
