# MUSE-REPORT-1253: Start-anchored bridged run for the GX refinement

## What was done

New file `grammatik/Grammatik/X86/TsoGxStart.lean` (plus one import line
in `grammatik/Grammatik.lean`), proving the entry/call prefix leg that the
three bridged fragment kinds (`TsoRunInduction`: no-read store, committed
read, forwarded read) do not cover: the fragment head is reached from
`RufStartG` by entry/call prefix execution, on the accepted
non-degenerate witness program `eP` (`haupt` calls `setze`, which writes
table `konto`).

New definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `startAnker : RufMaschineG eD` — the G start machine of the witness program.
- `startAnker_refl` — the anchor reaches itself in zero steps.
- `startAnker_gleich` — the anchor unfolds to `RufStartG eP eSp eInit` (`rfl`).
- `startCall_erreichbar` — entry/call prefix step 1 via accepted `w_rufEnde`:
  the call of `setze` from `haupt` fires on the start machine.
- `fragmentKopf_erreichbar` — fragment-head prefix via accepted `w_blatt`
  (`execStmt_assignSlot` writing `konto[0] = 5`): a machine two steps from
  the start.
- `startBrueckenArten` — kind enumeration via accepted
  `fragArt_abgedeckt_oder_drain` (store / loadCommit / loadFwd / drain).
- `startFragment_zeuge` — joint non-degenerate witness via accepted
  `ziel_ort_einfaden_zeuge` plus the `rfl` write fact: reached run from
  `RufStartG`, start world at `konto[0] = 0`, `setze` writes `konto`, logged
  `pruefe` entry world at `konto[0] = 5` (observable memory change).

Nothing existing was edited except the one import line. No new machine, no
new executor, no silicon claim; accepted lemmas are reused unchanged.

## Verification

- `./lean-probe grammatik/Grammatik/X86/TsoGxStart.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
  Axioms: standard (`propext, Classical.choice, Quot.sound`; `startAnker_gleich`
  only `propext`, `startBrueckenArten` none).
- `./lean-bau`: `Build completed successfully (644 jobs).`
  (`✔ [643/644] Built Grammatik (1.4s)`, `TsoGxStart` built at `[642/644]`.)

## What remains open

- No cross-declaration refinement simulation is claimed: joining the `eP`
  prefix run with a `witD` `BrueckenLauf` needs a cross-declaration lowering
  certificate (OPEN, stated in CUTS).
- No byte-level entry/call linkage: `PipelineEntry.prolog_lauf` and
  `StackExecution.geholt_verschachtelt_wiederhergestellt` live on the byte
  machine; the prefix here is source-level (OPEN with the pipeline owners,
  stated in CUTS).

## Task issue (believed wrong)

- The task names lane 1215's `TsoGxRefine.lean` as the follow-up target.
  That file does not exist anywhere on this master (no `TsoGx*` module;
  `TsoRunInduction` is the closest accepted refinement-adjacent module).
  There is therefore no accepted refinement statement to compose with.
  The prefix leg the task describes as missing is delivered above; the
  composition itself waits on the refinement statement.
- The task says to reuse `PipelineEntry.lean`/`StackExecution.lean` for the
  prefix. Those prove byte-machine entry/call execution (`Zustand`,
  `laufBytes`), while `RufStartG` reachability is source-level
  (`RufSchrittG`). The prefix here reuses the source-level entry/call
  lemmas (`w_rufEnde`, `w_blatt`) instead; the byte-to-source entry
  connection is recorded as OPEN rather than faked.
