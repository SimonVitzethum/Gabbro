# MUSE-REPORT-861: Copy propagation rule lemma

## Task
Lane 861: optimiser rule — copy propagation. Drop copies under recomputed
avail plus dominance with width preserved; redefinition between definition
and use refuses. Generic rule lemma over arbitrary values with
validator-decided side conditions; value/fault/observation preservation;
exact certificate shape; precise refusal case. ZEUGE:
`OptFoldCopy_verbindung` + `OptFoldCopy_verbindung_zeuge`.

## What was done
New file `grammatik/Grammatik/X86/OptFoldCopy.lean` (288 lines), registered
as `import Grammatik.X86.OptFoldCopy` at the end of
`grammatik/Grammatik.lean`. Built incrementally (skeleton → refusals →
value → connection → witness), each step checked with `./lean-probe`
(0 errors), final `./lean-bau` green.

Modeled directly on the accepted const-fold lane (OptFoldConst.lean):
the recomputation obligation `hEq` is conditional on admission (`hz`),
so nothing is claimed where the validator refused the site.

### New definitions
- `CopyCert` (structure, 4 Bool citations: `verfuegbar`, `dominiert`,
  `breiteOk`, `keineNeudef`) — the certificate shape: local rewrite
  record (the two `Var`s at the `bind` window) plus recomputed analysis
  citations (the four Bools, re-decided by the validator, never trusted).
- `copyZulassen` (admission Bool: conjunction of all four).

### New theorems
- `copyVerweigert_neudef` — redefinition between definition and use
  refuses (the DESIGN failure case).
- `copyVerweigert_dominanz`, `copyVerweigert_verfuegbar`,
  `copyVerweigert_weite` — the other three citations each refuse.
- `probe_copyZulassen_ok`, `probe_copyZulassen_neudef`,
  `probe_copyZulassen_dominanz` — decided probes.
- `copyVar_wert` — admitted copy preserves `eval` value, arbitrary
  type `τ`, arbitrary values (conditional `hEq` + `hz`).
- `probe_copyVar_wert` — environment read probe.
- `copyVar_orte` — both sides read no carrier (`orte` equal, `rfl`):
  no shared access added/removed (concurrency), no call-log event, no
  contract-visible read.
- `copyGleit_passt` — float copy keeps the same `gleitPasst` outcome
  (IEEE: bit-identical value, no recomputation, no rounding scope crossed).
- `OptFoldCopy_verbindung` — CONNECTION at an `Endblock.bind` window
  with arbitrary continuation `rest`: eval-value equality AND `execEnd`
  outcome equality (same constructor/successor worlds: no fault added
  or removed, contracts/call logs/concurrency agree, step-budget
  accounting unchanged — same block shape, pure unbudgeted read) AND
  `orte` equality.
- `OptFoldCopy_verbindung_zeuge` — JOINT witness: all premises
  instantiated together on `refD` (two context slots both holding `7`,
  `hEq` by `rfl`, `leave` continuation), with non-degeneracy conjuncts
  (`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`: reached F-machine
  run `MB`, slot `0 -> 100`, memory-changing).

### Axioms (`#print axioms`, from `./lean-bau` output)
All within the standard set (`propext`, `Classical.choice`,
`Quot.sound`): `copyZulassen` axiom-free; refusal/orte/float lemmas on
`[propext]`; `copyVar_wert`, `OptFoldCopy_verbindung`,
`OptFoldCopy_verbindung_zeuge` on `[propext, Classical.choice,
Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

### Last `./lean-bau` result line
`Build completed successfully (511 jobs).` — `== exit 0; 0 error
line(s) in the COMPLETE output`; `Grammatik.X86.OptFoldCopy` built.

## What remains open (see CUTS in the file)
- No lowering to target blocks/bytes and no per-access bridge (source-level
  `bind` window only; lowering lanes own that).
- No formal `totalCost`/level-(c) machine-work bound (argued unchanged by
  same block shape; OPEN per IR-VALIDIERUNG).
- No silicon/TSO/GX/ABI correspondence (stops at equal `eval` values and
  `gleitPasst` outcomes).
- No interprocedural avail (per-use recomputed `hEq`; dominance and
  no-redefinition are carried refused-when-false Bools).

## Notes on the task
- Nothing in the task statement looks wrong. One design decision worth
  recording: `hEq` is stated for the SPECIFIC environment `ρ` at the use
  (`copyZulassen cert = true → ρ.get y = ρ.get x`), not universally over
  all environments — the universal form is false in general (distinct slots
  may hold distinct values) and would make the witness unprovable. The
  conditional-on-admission shape mirrors the accepted const-fold lane.
- `_hz`/`_hEq` binder names in the zeuge follow the accepted `_hW`
  pattern (OptFoldConst): premises still instantiated jointly in the proof.
- Apparatus notes: the permission classifier twice rejected `bash grep`
  invocations (used the dedicated `grep` tool instead) and once rejected
  `bash python3 -c` (used `read`/`write`/`edit` instead). A full-file
  `write` was needed once to repair a one-word typo after several `edit`
  match failures caused by stale surrounding text; verified afterwards
  with `grep` + `lean-probe`.
- No diagnostic/gift/example/CLI numbers taken, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched. `git status` shows only the two owned paths.
