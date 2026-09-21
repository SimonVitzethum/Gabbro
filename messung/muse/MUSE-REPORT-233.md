# MUSE-REPORT-233 — syscall/fd model in Lean (wave B, pure Lean)

## What was built

New file `grammatik/Grammatik/FremdRuf.lean` (+ import line in
`grammatik/Grammatik.lean`), modelling a reduced form of the lane-226 shape (review G10: no `opaque`
type, no `buf`/`len` parameters, read writes no memory; see the file's
CUTS block): a
descriptor as a plain carrier value (opacity not modelled) plus user-declared gates as
oracle calls. Answers are constrained only by the declared ensures;
dispatch labels, register bindings, costs and effects are program DATA
(`GateData`) that the semantic theorems never consult except for the
effect/frame match.

- `GateData D`: `num`, `regs` (abstract parameter indices, no platform
  registers), `kosten`, `eff`, `effG`. Illustration labels 1001/1002
  are program data, not OS facts (commented as such in the file).
- Fixture `fdD`: one table (2 slots, `0..100`), no locks/globals/marks,
  two gates (`fdOpen : Aparms [] → 0..7`, `fdRead : Aparms [0..7] →
  0..100`, both may write the table), one function `fdArbeit` writing
  the table. No ABI constant, no syscall number, no errno, no arch
  name anywhere in the file (checked by grep; the only hits are the
  substring `rdi` inside the English word `recording`, the same wording
  `Satz.lean` uses).
- `fdQ` (open promises nonzero descriptor, read promises answer =
  current slot value), `fdO` (open stores a marker, records, answers
  3; read records, keeps memory, answers the slot value, ignoring the
  passed descriptor).
- Theorems: `gate_daten_gleich`, `fdO_gut` (frame + recording over
  complete domains), `fdQ_vertrag`, `fremdruf_gate_gilt` (one call:
  ensures + frame in gate-effect terms), `fremdruf_offen_lesen`
  (open-then-read composition), `fd_opak` (the WITNESS oracle's read answer is independent of
  the passed descriptor), `fremdruf_falsch_abgelehnt` (wrong ensures
  demanding 6 refused), `fdPC_erreicht` + `fdPC_schreibt` (one writing
  leaf reached from `GenStart`, slot `0 -> 5`), witnesses
  `fremdruf_fd_zeuge` (ZEUGE), `fremdruf_offen_lesen_zeuge`,
  `fremdruf_gate_gilt_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/FremdRuf.lean`: 0 errors.
- `./lean-bau` last line: `Build completed successfully (275 jobs).`
- `#print axioms`: every theorem depends only on subsets of the
  standard three (`propext`, `Classical.choice`, `Quot.sound`); the
  run lemmas use exactly the three.
- Planted-defect check: `.tmp/defekt233.lean` (not committed) attempts
  `AxVertragO fdQfalsch fdO` and fails at line 23 col 31:
  `Tactic 'decide' proved that the proposition 3 = 6 is false`.
  The committed file proves the negation instead
  (`fremdruf_falsch_abgelehnt`).

## Open / cuts (also in the file's CUTS block)

- Labels/bindings/costs are uninterpreted (emitter stub contract, S6).
- No pairing with a proved kernel entry (that is `SyscallPaarung`).
- The reached run fires a plain leaf, not a gate call; gate calls
  appear as oracle answers at concrete sites (`fdFitO`, `fdFitR`).
- Four linter warnings (unused guard binders `hgt`/`hgg` in the
  recording helpers) kept named deliberately: same shape as merged
  `swEff` in `SyscallPaarung.lean`; rule 4(d) forbids discarding them
  with `intro _`.

## Task feedback

- The wave-5 preamble ("independent reviewer, write only the verdict
  file") contradicts the lane task (new model file + ZEUGE); I followed
  the lane task, since it is the specific instruction.
- The ZEUGE parenthetical asks for "an fd opened and read" in the
  reached run; the run fires a plain leaf while the open/read calls
  are witnessed as oracle answers at concrete sites (documented cut).
  A run stepping through `bindAxiom` needs the F-machine residue shape
  and did not fit this lane.
- Two commits after the first used `git commit` directly because
  `arbeitsprotokoll/` is gitignored (the message file cannot be
  staged); all messages carry the required co-author line.
