# MUSE-REPORT-241 — Lean: virtual region + commit subset + refinement

Lane 241 (TODO wave D, pure Lean). Starting point: `dokumente/PLAN-DYNAMISCH.md`
section 9 (lane 239's Lean sketch). `CSpeicher.lean` read, not edited.
`Zielsatz/Spec.lean` premise (c) read: fault cost is taken as DATA, never justified.

## What was built

New file `grammatik/Grammatik/ArenaDyn.lean` (no name collision; the plan fixes
this name in section 9), plus the one import line in `grammatik/Grammatik.lean`:

- `DynArena`: ceiling `M`, commit floor `hi`, committed prefix `c` with
  `hi <= c <= M`, `0 < M` (the declared region; virtual = `Fin M`, usable =
  `Fin c`, prefix property by construction).
- `dynGrow`: explicit commit; `some` (bumped prefix) iff `c + n <= M`, else
  `none` (refusal beyond the ceiling, never a runtime surprise).
- `dynGrow_monoton`: a successful grow never shrinks the prefix.
- `dynCommit_innerhalb`: every committed slot is reserved (`i < c -> i < M`).
- `dynGrow_ueber_M`: over-ceiling commit returns `none`.
- `growKosten n faultKosten = 1 + n * faultKosten`: the per-slot commit cost
  is a function argument read from the named hardware assumption (premise (c)
  latency entry), never proved here.
- `dynVerfein`: refinement, membership level — committed slots are static-max
  slots (`hi <= M` alongside).
- TARGET `region_verpflichtet`: ceiling/prefix obligation discharged on a run
  that really moved memory. No premise quantifies over program syntax; every
  premise is used by the proof (floor/ceiling -> `Mhi <= Mmax`, memory fact,
  positivity and reachability reported).
- `region_verpflichtet_zeuge`: joint instantiation on the reference fixture
  (`M = 64`, `hi = 8`, `c = 16`, run `MB` via `refB_erreicht`/`refB_schreibt`).
  NON-DEGENERATE: `refD` has the table `konto` that the leaf writes, and `MB`
  is reached with the memory-changing step (`konto[0]`: `0 -> 100`).

## Planted-defect check

Over-ceiling commit fails red: `planted_ueber_M : dynGrow arena64volle 1 = none`
(`max 64` arena, full, asked to grow — proved by `rfl`, failure line is the
statement). The unchecked variant `dynGrowFalsch` reaches `c = 65` past the
ceiling (`planted_defekt_sichtbar`, also `rfl`): without the `M` guard the
defect would be committable.

## Verification

- `./lean-probe grammatik/Grammatik/ArenaDyn.lean`: exit 0, 0 errors.
- `./lean-bau`: exit 0, 0 error lines, "Build completed successfully (275 jobs)".
- `#print axioms`: `region_verpflichtet` and `region_verpflichtet_zeuge` depend
  on exactly `[propext, Classical.choice, Quot.sound]` (standard three); helper
  lemmas on subsets or nothing. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No new diagnostic codes, no gift/example numbers. English only.

## Deviation note (rule conflict)

The wave preamble says "independent reviewer: do not change any existing file".
The lane task says "default: new files + `Grammatik.lean` imports only", and
rule 5 requires the import for new Lean work to build. The task wins: the only
existing-file change is the one added import line. No existing theorem touched.

## What remains open (see CUTS in the file)

Membership-level refinement only — no step-for-step simulation against the
static-max program, no transfer of the `ArenaZucker` theorems. No checker rules
(240/Rust), no emitter/runtime (242), no cost arm (243), no `Spec.lean` header
diff for the two (d) assumption texts (left for the reviewed diff the plan
requires; this lane changes no existing file beyond the import).
