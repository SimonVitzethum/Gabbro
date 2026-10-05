# MUSE-REPORT-1156: exact review of candidate 1155 (pipeline loops + branch layout with budget)

CANDIDATE: 1155, pinned HEAD `6fd346a61402414ac8f6ca8463b06543f4521d0f`
(base `062b979a6271b7b3044ab06be3f3cde411a0d4f1`), per
`.tmp/review/SNAPSHOT.json`. Files in candidate: `MUSE-REPORT-1155.md`,
`grammatik/Grammatik.lean` (one appended import line),
`grammatik/Grammatik/X86/PipelineLoops.lean` (new, 544 lines).

## Method

Report-only exact review over the coordinator snapshot
(`.tmp/review/author-1155/`: `PATCH.diff` read in full, all 651 lines;
`MUSE-REPORT-1155.md`; `BUILD-EVIDENCE.json`; `OWNER-TASK.md` = lane 1155
task). Grepped the diff for `sorry|admit|native_decide|unsafe|axiom |intro
_|have _ :=|split_ifs|norm_num|ring_nf`: zero hits in added Lean code
(the only matches in the snapshot are the HARD-RULES preamble words inside
`OWNER-TASK.md` itself). `Grammatik.lean` diff is exactly one appended line
`import Grammatik.X86.PipelineLoops`; reserved optimiser files untouched.

## Checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in new code: PASS.
  File ends with CUTS block plus four `#print axioms` lines (legitimate).
- Axioms standard: PASS per build evidence —
  `schleife_korrekt_endlich`/`schleife_verweigert_schlechten_koerper`/`zw_zeuge`:
  `[propext, Quot.sound]`; `schleife_bytes`: `[propext, Classical.choice,
  Quot.sound]` (choice inherited from reused `relax_laufBytes`).
- Existing files untouched except the one import line: PASS.
- Accepted evaluator lifted, not copied: PASS. Reused unchanged:
  `LProg`/`stepL`/`laufL`/`laufL_add`, `relax`/`relax_ok`/`relaxLayoutOk`/
  `layoutOk_zeile`/`bild`/`alleWeit`, `laufBytesI`/`relax_laufBytes`,
  `kanonischI`/`faelltDurchI`, `retryLauf`/`foreverLauf`, `bedingung`.
  New definitions only: `schleifeProg`, `schleifeKompilieren`,
  `schleifeSchritte`, witness setup (`zwD`/`zwV`/`zwBis`/`zwSchritt`/
  `zwUeberlauf`/`zwKoerper`/`zwAdr`/`zwS0`/`zwSigma0`/`zwSigma1`/`zwRep`).
  No second source interpreter, no new IR, no new hardware model.
- Refusals really refuse: PASS. `schleife_verweigert_schlechten_koerper`
  (non-canonical/non-fall-through body row fails even the all-wide layout,
  so `relax` = `none` at every fuel) with poison probes
  `schleife_verweigert_ret` and `schleife_verweigert_sprung`, both closed
  by computation (`decide`/`simp`+`rfl`).
- Witness non-degenerate: PASS. `zw_zeuge` instantiates ALL premises of
  `schleife_korrekt_endlich` jointly (`zw_lese`, `zw_stabil`, `zw_bed`,
  `zw_weiter`, `zw_ende`, `zw_kein_ueberlauf`) on one table of two rows
  with `schreibt = true`; the 1-round source run writes slot row 0
  (memory-changing) and the 8-step labelled round stores a word to 8192
  and reloads it (`read64 ... = some 1` in `zwRep`). Single-core scope
  inherited from `ISARelax`, so no two-core requirement applies.
- Silicon facts: PASS vacuously. No new encodings, flag effects, fault
  classes or ordering claims; all target instructions are existing
  canonical pilot forms (`.pilot (.movImm64/.addReg64/.store64/.load64/
  .cmpReg64 ...)`), addresses via existing `natAdresse`, flags via
  existing `sub64`. Nothing new to check against the SDM extracts.
- CUTS honest, no over-claim: PASS. States pilot-ISA-only, one core, model
  memory, no time, no TSO; no finite budget for unbounded loops
  (`ewig_ein_schritt` is one-step unfolding only); per-round body
  correspondence `hWeiter` is an explicitly named premise proved per body
  by its producer (witness proves it for the concrete body by `rfl`
  computation); bodies with control flow refused, never guessed. No
  hardware-correspondence or W/GX claim; the byte corollary
  (`schleife_bytes`) is explicitly `relax_laufBytes` applied at the schema
  (fetched-bytes execution under `WX`/`CodeAt` premises).
- No contract quantification away, no semantics without memory change, no
  premise discarded with `intro _`/`have _ :=`: PASS.

NOTE (not REPAIR): in `schleife_korrekt_endlich`, `hBed` (condition/flag
agreement) is only nominally used — `have hb := hBed ...` is derived in
both induction branches but `hb` is never referenced afterwards; the proof
cases on `he : (bis σ ρ).2` directly and delegates step behaviour to
`hWeiter`/`hEnde`. The premise is present in the proof term and supported
by the witness (`zw_bed`), the theorem as stated is true, and nothing is
weakened — but `hBed` is semantically redundant. Suggested cleanup for a
follow-up: either use `hb` or drop `hBed` with justification. No
unsupported desired-correctness premise: every load-bearing premise is
proved for the witness body.

Task reading: the lane-1155 task asks for `while`/bounded-`for` lowering
with an `execBlock`-level correspondence; the candidate covers the bounded
form `Stmt.retry` (`retryLauf`, which `execStmt` calls for `.retry`) and
states the finite-run correspondence at that level, with the byte leg via
the accepted `relax_laufBytes`. That scoping is declared, not hidden.

## Build

`./lean-bau` independently re-run in this review clone on 2026-10-05:
`Build completed successfully (612 jobs).` — green. Note: this clone
contains master without the candidate file, so this run validates the
base tree, not the candidate itself; candidate-green evidence is the
author's `BUILD-EVIDENCE.json` final entry (`Build completed
successfully (608 jobs).` with all four `#print axioms` lines above,
plus a full `lean-probe` trail from red to `== 0 error(s)`).

## Open / follow-ups (candidate's, agreed)

Per-round correspondence for arbitrary straight-line bodies via the
`Pipeline.lean` lowering lemmas (bridge lemma not written); unbounded
loops have no finite budget; pilot ISA / one core / model memory / no TSO
inherited.

## VERDICT: ACCEPT
