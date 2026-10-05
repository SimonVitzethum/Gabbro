# MUSE-REPORT-1155: Pipeline loops and branch layout with budget

## What was done

NEW FILE `grammatik/Grammatik/X86/PipelineLoops.lean` (~545 lines) plus one
import line in `grammatik/Grammatik.lean`. Bounded source loops
(`Stmt.retry`, which is what `retryLauf` in `Semantik.lean` runs and what
`execStmt` calls for `.retry`) are lowered to one labelled schema and
validated through the EXISTING relaxation/layout checks; finite source runs
transfer their iteration budget to a stated target step budget, and the
labelled run is connected to fetched byte runs through the EXISTING
`relax_laufBytes`. No new IR, no second interpreter, no existing file
edited except the import line.

### Definitions

- `schleifeProg (koerper : List Instr) (c : Bedingung) : LProg` — head
  `jcc c` to the end label, body as `op` rows, back `jmp 0`.
- `schleifeKompilieren (treibstoff) (koerper) (c) : Option (List Byte)` —
  `relax` the schema, take `bild`; `none` is refusal.
- `schleifeSchritte (runden m) : Nat := runden * (m + 2) + 1` — one round
  costs head + `m` body rows + back jump; the final exit check costs one.
- Witness setup: `zwD`/`zwV` (one table, two rows, `int 0 1000`, written by
  the step), `zwBis` (done iff row 0 holds 1, world unchanged),
  `zwSchritt` (writes 1 into row 0 — the memory-changing step),
  `zwUeberlauf` (always loudly `.logik .schleife`), `zwKoerper` (six
  fall-through rows: counter inc, store to 8192, reload, compare),
  `zwAdr`, `zwS0`, `zwSigma0`, `zwSigma1`, `zwRep`.

### Theorems

- `schleifeProg_laenge/_kopf/_rueck/_mitte` — schema layout facts.
- `schleife_relax_ok` — whatever the fuel, the relaxed layout validates
  (direct reuse of `relax_ok`).
- `schleife_verweigert_schlechten_koerper` — REFUSAL: a non-canonical or
  non-fall-through body row (`ret`, jumps, calls) fails even the all-wide
  layout, so `relax` answers `none` at every fuel. Poison probes
  `schleife_verweigert_ret`, `schleife_verweigert_sprung`.
- `schleifeSchritte_succ/_add`, `laufL_stop` — budget arithmetic and the
  stopped labelled run.
- `wiederhol_steht`, `wiederhol_schritt` — the real `retryLauf` unfolded.
- `ewig_ein_schritt` — finite-prefix claim for `forever` (one step; NO
  finite budget for all runs is claimed).
- `schleife_korrekt_endlich` — THE LOOP THEOREM: with per-round simulation
  (`hWeiter`), condition agreement (`hBed`), read stability (`hBisStabil`),
  read preservation (`hLese`), exit step (`hEnde`), loud overflow
  (`hUeberlauf`), a source run finishing `.ok` within `n` rounds IS the
  labelled run of `schleifeSchritte n m` steps to the end label, keeping
  `Rep`. Axioms: `propext, Quot.sound`.
- `schleife_bytes` — byte corollary (`relax_laufBytes` at the schema).
  Axioms: `propext, Classical.choice, Quot.sound` (inherited).
- Witness premises `zw_lese`, `zw_stabil`, `zw_bed`, `zw_kein_ueberlauf`,
  `zw_weiter` (8-step round by kernel computation), `zw_ende`, and the
  joint `zw_zeuge` instantiating ALL premises on the non-degenerate
  program (memory changes on both sides: source slot write, target word
  store with verified reload). Axioms: `propext, Quot.sound`.

## Last build result

`./lean-bau`: `Build completed successfully (608 jobs).` — whole project
green, including `Grammatik.X86.PipelineLoops` with the four `#print
axioms` lines above (all within the standard set).

## Open / not claimed

- Per-round body correspondence for ARBITRARY straight-line bodies is a
  premise (`hWeiter`), proved per body by its producer — the `Pipeline.lean`
  lowering lemmas are the intended supplier, the bridge lemma is not
  written here.
- Unbounded loops (`forever`, source `while` without bound): only
  one-step unfolding; no finite budget; infinite runs not validated.
- One core, model memory, no time, no TSO (inherited from `ISARelax`).

## Task feedback

Nothing in the task is wrong. Two adjustments made honestly and stated in
CUTS: (1) the exit premise concludes `Rep` itself rather than assuming
RIP-preservation (the exit step sets RIP, so a same-state equation would be
uninhabited); (2) re-read stability covers world and outcome, not just the
bool (the exit world is the re-read world). Both are documented premises,
not weakened conclusions.

Lane-1155 note: the session hit a Lean struct-instance parse quirk —
newline-separated `{ }` fields WITHOUT commas misparse when a field value
ends on the same line as a comma; the file uses the `Byteschritt.lean`
newline style (no commas), which parses.
