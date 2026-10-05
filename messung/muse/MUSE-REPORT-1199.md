# MUSE-REPORT-1199: loaded-image correctness for spill, call, table, float and work fragments

## What was done

New file `grammatik/Grammatik/X86/PipelineLoadedAll.lean` (plus the one
`import Grammatik.X86.PipelineLoadedAll` line at the end of
`grammatik/Grammatik.lean`). Each fragment family of lanes 1161, 1165,
1189, 1191, 1159 gets its `pipeline_correct_loaded`-shaped theorem over
the checked mapping: start state is the existing loader's state
(`PipelineImage.startZustand` over `ladung`), fetch runs through actual
memory, W^X sits in per-byte `CodeAt`, and the relocation leg reuses the
accepted `PipelineLink` patch frame plus re-decode. Block-level families
(spill, work, calls) share the one loaded-premise pattern (`imageOk` /
`weltOk` projected to `CodeAt` / `LayoutSep` / `WorldRep`); chunk-level
tables run from loaded memory with decided checks; floats honestly refuse
the byte image. No existing file was edited (except the import line), no
IR, no second interpreter, no reserved file touched.

New definitions/theorems (all in `Gabbro.Grammatik.X86.PipelineLoadedAll`):

- `fragmentBytesGeladen` — the one shared loaded-code predicate.
- Spill: `spill_correct_loaded` (via `spill_haelt_bedeutung`),
  `piSpillRahmen` (frame separation transported along `pi_layout_gleich`),
  `spill_correct_loaded_zeuge` (joint, rows 7 -> 35 / 9 -> 6).
- Calls: `ruf_correct_loaded` (via `einzelRuf_korrekt`), `cwBild`
  (built callee image), `cw_validate_pi`, `cw_imageOk`, `cw_weltOk`,
  `cw_rufExec_pi` (all by computation), `ruf_correct_loaded_zeuge`
  (joint, row 7 -> 35, frame saves change memory, arg reloads).
- Tables: `tabellen_correct_loaded` (via `tabellen_schreiben_laufBytes`
  with `tabWorldRep`), `zeBildCode/Daten/Datei/Bild` (minimal
  two-section image), `zeBild_codeAtB/codeAt/okB/weltB/rip`,
  `tabellen_correct_loaded_zeuge` (joint, byte 7 -> 42).
- Work: `arbeit_correct_loaded` (via `pipeline_arbeit_korrekt`),
  `arbeit_correct_loaded_zeuge` (joint, priced witness program).
- Floats: `float_seq_geladen` (via `pipelineFloat_seq` plus the loaded
  memory equation), `float_loaded_verweigert` (failed validator leg
  refuses step and run), `float_seq_geladen_zeuge` (joint, divide plus
  stored infinity changing memory, both probes).
- Relocation: `reloc_redecode_geladen` (the accepted `verknuepft_korrekt`
  on the witness link: displacement, fit, coverage, union, W^X, mapping,
  range, frame).
- Poison probes (one per refusal): `gift_spill_code`, `gift_ruf_rot`,
  `gift_tabelle_fremd`, `gift_float_profil`, `gift_float_laenge`,
  `gift_link_range`, `gift_arbeit_mul`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/PipelineLoadedAll.lean`:
`== 0 error(s)`. `./lean-bau`: `exit 0`, `Build completed successfully
(627 jobs)`, `Built Grammatik`. (One `./lean-bau` run failed first with a
toolchain file-IO error,
`failed to read file '.../Init/Data/Array/Count.olean.private'`, on no
source change; the immediate incremental retry was fully green, so this
is recorded as transient apparatus noise, not a finding.)

`#print axioms` for every main theorem lies inside
`propext, Classical.choice, Quot.sound` (many need only a subset).

## What remains open (inherited cuts, not weakened)

- No byte-fetch connection for floats: `laufFp` runs constructed
  `FpDecodiert`, never decoder bytes (lane 1161's cut).
- Single-assignment callee bodies, no optimiser certificates in calls;
  no block-level table reads; no TSO/GX bridge; named time only;
  no silicon correspondence. All documented in the file's CUTS.

## Task feedback (plainly)

- "Generic over the fragment where possible": block-level families
  share the projection pattern, but chunk-level families (tables,
  floats) need per-family state shapes, so five statements remain.
  A single functor over all five would restate premises (rule 4a).
- Float "loaded-image correctness" as posed is not statable honestly:
  `FpBefehl` has no pilot byte encoding, so there is no byte run to
  relate. I proved sequence-over-loaded-memory plus refusal instead;
  claiming more would be a desired-correctness premise.
- The tree-wide lowercase `vertrag` binder relies on autoImplicit
  unification (there is no such lowercase definition; `Syntax.lean`
  itself uses it). Mixed usage in this file (capital in two theorems,
  lowercase elsewhere) all elaborates; a tree-wide cleanup is
  coordinator business, not this lane.
