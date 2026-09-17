# MUSE-REPORT-241 — Lean: virtual region + commit subset + refinement

Lane 241 (TODO wave D, pure Lean). Starting point: `dokumente/PLAN-DYNAMISCH.md`
section 9 (lane 239's Lean sketch). `CSpeicher.lean` read, not edited.
`Zielsatz/Spec.lean` premise (c) read: fault cost is taken as DATA, never justified.
Round 2 (after review round 1, findings F1–F3): see "Review response" below.

## What was built

New file `grammatik/Grammatik/ArenaDyn.lean` (no name collision; the plan fixes
this name in section 9), plus the one import line in `grammatik/Grammatik.lean`
and `import Grammatik.ArenaZucker` for the proved bridge:

- `DynArena`: ceiling `M`, commit floor `hi`, committed prefix `c` with
  `hi <= c <= M`, `0 < M` (the declared region; virtual = `Fin M`, usable =
  `Fin c`, prefix property by construction).
- `dynGrow`: explicit commit; `some` (bumped prefix) iff `c + n <= M`, else
  `none` (refusal beyond the ceiling, never a runtime surprise).
- `dynGrow_monoton`: a successful grow never shrinks the prefix.
- `dynCommit_innerhalb`: every committed slot is reserved (`i < c -> i < M`).
- `dynGrow_ueber_M`: over-ceiling commit returns `none`.
- `dynGrow_isSome`: success is exactly the bound.
- `arenaModell` + `dynGrow1_gdw_alloc`: one-slot commit agrees with
  `Arena.alloc` on `Kap ⟨hi, M⟩`, proved from the `alloc_erfolg` /
  `alloc_fehlschlag` pair — the `ArenaZucker` transfer target in miniature,
  and lane 244's simulation anchor.
- `growKosten n faultKosten = 1 + n * faultKosten`: the per-slot commit cost
  is a function argument read from the named hardware assumption (premise (c)
  latency entry), never proved here.
- `dynVerfein`: refinement, membership level — committed slots are static-max
  slots (`hi <= M` alongside).
- TARGET `region_verpflichtet`: from the reached memory-moving run, the link
  `hlink` (the run's written slot `0` is committed — the R-commit model half
  for the reference write) to the `DynArena`-level conclusion
  `(∀ i, i < c → i < M) ∧ 0 < M`. No conclusion conjunct repeats a premise;
  every premise is used (`hlink hreach hmem` feeds the second conjunct);
  no premise quantifies over syntax.
- `region_verpflichtet_zeuge`: joint instantiation over `DynArena` values
  `Aw0 = ⟨64, 8, 16⟩` and `Aw1 = ⟨64, 8, 24⟩` (not bare Nats), the successful
  grow `grow_gelingt : dynGrow Aw0 8 = some Aw1` (by `rfl`), the
  committed-prefix reads (`dynCommit_innerhalb` at every slot,
  `region_verpflichtet` for slot `0` tied to the run), and the reached run
  `MB` via `refB_erreicht`/`refB_schreibt`.
  NON-DEGENERATE: `refD` has the table `konto` that the leaf writes, and `MB`
  is reached with the memory-changing step (`konto[0]`: `0 → 100`).

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
  on exactly `[propext, Classical.choice, Quot.sound]` (standard three);
  `dynGrow1_gdw_alloc`/`dynVerfein`/`dynGrow_ueber_M` on subsets,
  `dynGrow_monoton`/`dynGrow_isSome` on `[propext]`,
  `planted_ueber_M`/`planted_defekt_sichtbar`/`grow_gelingt` on nothing.
  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No new diagnostic codes, no gift/example numbers. English only.

## Review response (round 1 findings F1–F3)

- F1 (conclusion restated premises): fixed. `region_verpflichtet` now takes a
  `DynArena A` (non-Prop, used) plus the run premises plus the link `hlink`
  (run → written slot `0` committed), and concludes
  `(∀ i, i < A.c → i < A.M) ∧ 0 < A.M` — both conjuncts derived via
  `dynCommit_innerhalb`, neither a premise. (No fixed TARGET string existed
  for this theorem — the task fixed only the `region_verpflichtet_zeuge` name
  and witness content — so the redesign follows the finding's concrete option.)
- F2 (witness Nats-only): fixed. The witness is over `DynArena` values `Aw0`
  (capped table `max 64`) and `Aw1`, with `grow_gelingt` (grown `16 → 24`),
  committed-prefix reads, and the `MB` run half unchanged.
- F3 (standalone model vs §9): option (b) — standalone kept, with the
  measurement reasoning below — plus a proved linkage anchor
  (`dynGrow1_gdw_alloc`) so the file is not silent about `Arena`/`ArenaZucker`.

## F3 measurement reasoning (why the Nat triple suffices)

Per-definition consumers (who reads what):

- `DynArena` fields `M`/`hi`/`c` → lane 242's descriptor (compile-time `M`
  beside the `committed` word initialised to `hi`) and lane 240's per-path
  `(count, committed)` checker state (this structure IS that state plus the
  ceiling).
- `dynGrow` → lane 240's transfer function for `grow A by n` (main path:
  capped bump; `else` branch: unchanged) and lane 242's
  `gabbro_arena_grow` success/failure shape.
- `dynGrow_ueber_M` + `planted_ueber_M` → the R-max model half (lane 240's
  refusal beyond `M`).
- `dynCommit_innerhalb` + `dynVerfein` → the R-commit model half (lane 240's
  alloc-under-committed check).
- `growKosten` → lane 243's cost arm (`1 + n * declared-per-slot`).
- `dynGrow_monoton` → the reset-keeps-commit fact of plan §3 (lane 243).
- `dynGrow_isSome` + `dynGrow1_gdw_alloc` + `arenaModell` → lane 244's
  simulation anchor (single-step commit = `Arena.alloc` on `Kap ⟨hi, M⟩`).

Cost of the missing simulation statement: without step-for-step simulation
against the `hi := M` static program, lanes 242/244 cannot cite transfer of
`arenaAlloc_unter_schranke` and the `Arena.lean` arithmetic; each dynamic use
site re-proves its membership fact instead. That cost is model-only (reviewed
Lean lines, no runtime bytes — the emitter never reads the proofs). The full
`DynForm`-over-`ArenaForm` form with the four §9 Block-level theorems and the
simulation is lane 244's scope; the measured blockers (new narrow-on-committed
sugar, ~40–80 lines of dependent plumbing per alloc lemma; the static-max
program shape) are booked in CUTS. The `ArenaZucker`-theorem transfer is
tracked in CUTS and in this section, not silently dropped.

## Deviation note (rule conflict)

The wave preamble says "independent reviewer: do not change any existing file".
The lane task says "default: new files + `Grammatik.lean` imports only", and
rule 5 requires the import for new Lean work to build. The task wins: the only
existing-file change is the one added import line. No existing theorem touched.

## What remains open (see CUTS in the file)

Membership-level refinement + one-step model agreement only — no `DynForm`
over `ArenaForm D`, no Block-level `dynGrow_commit`/`dynAlloc_unter_commit`/
`dynAlloc_ueber_commit` (`dynCommit_monoton` is done as `dynGrow_monoton`), no
step-for-step simulation, no `Spec.lean` header diff for the two (d) assumption
texts (left for the reviewed diff the plan requires). No checker rules (Rust),
no emitter/runtime, no cost arm.
