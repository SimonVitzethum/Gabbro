# MUSE-REPORT-867: Range-check elimination rule lemma

## Task

Lane 867: optimiser rule lemma for range/bound-check elimination
(DIRECT-COMPILER-DESIGN section 7 row). Remove checks only on a source
extent proof AT the site (N571/N463/N506 over once-bound names);
entry-invariant-across-call removals refuse. Target theorems:
`OptRangeElim_verbindung` + joint companion
`OptRangeElim_verbindung_zeuge`.

## What was done

New file `grammatik/Grammatik/X86/OptRangeElim.lean` (owned), plus the
one-line import at the end of `grammatik/Grammatik.lean` (owned).
No other files touched. No diagnostic/gift/example/CLI numbers, no
MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
friend-reserved optimiser files.

Exact new definitions/theorems (namespace `Gabbro.Grammatik.X86`):

- `RangeElimCert` (structure): validator-decided side conditions for one
  range-check site — `extentAmOrt`, `einmalGebunden`,
  `keinSchreiberDazwischen` (DESIGN local premise, one Bool each).
- `rangeElimZulassen` (def): admission gate, conjunction of the three.
- `rangeElimVerweigert_ohneAusmass`: no at-site extent proof refuses.
- `rangeElimVerweigert_zweitbindung`: twice-bound name carries no
  extent (N571, gift 1387 shape) refuses.
- `rangeElimVerweigert_schreiberDazwischen`: intervening writer refuses —
  pins BOTH DESIGN failure cases (entry invariant across a writing call;
  entry invariant removing a check inside the writer's own mutating
  loop), since both are the same decided bit; without admission no `hz`
  exists, so the connection theorem cannot fire.
- `probe_rangeElimZulassen_ok / _ohneAusmass / _zweitbindung /
  _schreiber`: four `decide` probes (pass / three refusals).
- `OptRangeElim_verbindung`: CONNECTION. For arbitrary `e`, an admitted
  `Block.narrow e lo' hi' sonst rest` has the same `execBlock` outcome as
  its checked continuation `rest` with the same evaluated value. The
  DESIGN premise arrives as `hRegel` (validator-recomputed at-site range
  fact), conditional on admission `hz` — the same shape as the admitted
  float fold of the sibling file. The single outcome equality carries
  value, fault (incl. `logik bereich`/IEEE ranges), contract-at-place,
  call-log, concurrency-footprint (both sides read `e.orte` through the
  same `lese`) and step-budget preservation. Proof:
  `simp only [execBlock]; rw [dif_pos (hRegel hz)]`.
- `OptRangeElim_verbindung_zeuge`: JOINT witness. All premises
  instantiated together: literal `3` narrows into `0..10` with a `leave`
  else-branch and `nil` continuation on non-degenerate `refD`
  (`refEin_schreibt`), beside reached run `MB` (`refB_erreicht`,
  `refB_schreibt`, slot `0 -> 100`).

Axioms: `OptRangeElim_verbindung` and `_zeuge` depend on exactly
`[propext, Classical.choice, Quot.sound]` (standard set); refusals on
`[propext]`; gate and probes on none. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptRangeElim.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (each piece).
- `./lean-bau`: `exit 0; 0 error line(s)`, `Build completed
  successfully (511 jobs)`, whole project green including the new
  module (`Built Grammatik.X86.OptRangeElim`).
- Branch `muse/867` in clone `/home/simon/Dokumente/gabbro-muse/a867`
  (verified); skeleton pre-committed green, this report commits the rest.

## What remains open (also in the file's CUTS block)

- No `pruefung` (where-condition) connection; no arithmetic
  overflow-guard elimination (third shape of the DESIGN row).
- No formal level-(c) machine-work/totalCost inequality.
- No silicon correspondence, TSO/GX bridge, or ABI/loader claim.
- The validator's B+C recomputation behind `hRegel` is the consumer's
  obligation; this file is its interface.

## Task remarks

Nothing in the task turned out wrong. One interpretation worth
recording: the two DESIGN failure cases map to one decided bit
(`keinSchreiberDazwischen`), pinned by a single refusal theorem whose
doc names both shapes — adding a second identical theorem for the loop
shape alone would have duplicated the statement, so I did not.
