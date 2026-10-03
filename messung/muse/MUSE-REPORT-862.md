# MUSE-REPORT-862: CFG simplification rule lemma

## Task

Lane 862: optimiser rule — CFG simplification (DIRECT-COMPILER-DESIGN §7 row:
local premise "unreachable edge proof (decided const cond), exit edges preserved",
certificate "B block map", failure case "delete a `narrow`-else edge", phase E,
cost O(blocks)). Target: `OptCfgSimp_verbindung` + `OptCfgSimp_verbindung_zeuge`.

## What was done

New file `grammatik/Grammatik/X86/OptCfgSimp.lean` (~380 lines), wired into
`grammatik/Grammatik.lean` by one added import line. Only owned files touched
(`grammatik/Grammatik/X86/OptCfgSimp.lean`, `grammatik/Grammatik.lean`, this
report). No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

Read before writing: the DESIGN §7 row, OPTIMIZER.md §3.2 (S1 accepted-helper
status of `isWahrAll` in `InvariantenOpt.lean`), the real `Syntax`/`Semantik`
`execStmt`/`execBlock` fragment covered (`Stmt.ite`, `Block.pruefung`,
`Block.narrow`), `TableLayout.lean`, `CostSummary.lean`, and the
invariant/effect exports (`InvariantenOpt.lean`, `OptFoldConst.lean` as the
structural model for certificate + connection + joint witness).

### New definitions

- `CfgSimpCert` (structure, 3 Bool fields): `bedingtEntschieden` (decided
  constant condition, recomputed `isWahr` cited by the bridge premise),
  `austrittErhalten` (block map preserves every exit edge of the kept branch),
  `keinNarrowSonst` (deleted edge is no `narrow`-else, recomputed over the
  deleted syntax).
- `cfgZulassen` (admission Bool: conjunction of the three).
- `cfgSimpIte`, `cfgSimpPruef` (executable rewrites; return the kept branch /
  body verbatim).

### New theorems (all premises used; no `sorry`/`admit`/`axiom`/`native_decide`)

- Refusals: `cfgVerweigert_unentschieden`, `cfgVerweigert_austritt`,
  `cfgVerweigert_narrowSonst` (+ probes `probe_cfgZulassen_ok`,
  `probe_cfgZulassen_narrow`, `probe_cfgZulassen_unentschieden`).
- `cfgEntscheidung_wahr`: decided condition evaluates true over the arbitrary
  condition `c` (firing consults boolean truth only — never float rounding,
  never a guessed `ensures`); probe `probe_cfgEntscheidung` reuses the accepted
  `wCond` witness.
- `cfgSimpIte_istKept`, `cfgSimpPruef_istKept` (`rfl`: kept branch verbatim,
  hence exit edges preserved by construction).
- `narrowSonst_erreichbar`: an out-of-range value genuinely steps to `sonst`,
  so the `narrow`-else refusal is load-bearing, not decorative; there is
  deliberately NO theorem deleting a `narrow` else.
- `cfgIte_bleibt`, `cfgPruefung_bleibt`: outcome equality with the kept
  branch/body in the post-read world (value, fault, observations).
- `cfgFehler_logik_bleibt`, `cfgFehler_hardware_bleibt`: spelled-out fault
  preservation on both channels.
- `OptCfgSimp_verbindung` (TARGET): admitted rewrite preserves the outcome on
  both the `ite` and the `pruefung` shape; certificate = local rewrite record
  + `hZul` + `hBruecke` (decided bit IS the recomputed `isWahr`).
- `OptCfgSimp_verbindung_zeuge` (TARGET companion): all premises jointly
  instantiated on `refD` (`.wahr` condition, `nil` branches, `leave` else,
  all-true certificate) beside `refEin_schreibt`, the reached run
  `refB_erreicht` (`MB`), and the memory change `refB_schreibt`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptCfgSimp.lean`: 0 errors, 0 warnings.
- `./lean-bau`: exit 0, 0 error lines, "Build completed successfully (511 jobs)".
- `#print axioms` for every main theorem: each within
  `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` standard);
  several refusal/identity lemmas use only `[propext]`.

## What remains open (see CUTS in the file)

- Validator-side recomputation (exit-edge walk, dominators, avail/liveness per
  IR-VALIDIERUNG layer B) and the shared SCFG/block-map vocabulary (lane 287).
- Formal level-(c) machine-work/`CostSummary` transfer (lane 278); both sides
  share the same `passes` and the removed edge never fires.
- Whole-unit `FolgeG` and TSO/GX legs: nothing is added/removed (same `R`,
  identical `c.orte` read), but the legs themselves are OPEN.
- Per-access W/GX refinement, silicon/ABI/loader claims: OPEN.

## Task remarks

Nothing in the task appears wrong. One scoping note: the "exit edges
preserved" premise holds by verbatim construction in the equational proof
(only decidedness enters it); it gates FIRING via `hZul`, proved by the
refusal leg — this division is documented in the section-5 header rather
than forced into the equation, since a semantic exit premise would either be
unstatable generically or duplicate the conclusion.
