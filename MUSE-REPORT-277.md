# MUSE-REPORT-277: Generic source and user-duty bridge

*Lane 277, branch `muse/277`, model `opencode-go/muse-spark-1.3-contributor`.
Isolation gate passed: `/home/simon/Dokumente/gabbro-muse/a277`, top-level
matches, branch `muse/277`. No delegation, no other model calls.*

## What was done

Wrote the owned deliverable `dokumente/x86/QUELLBRUECKE.md` (docs-only
audit, no Lean/Rust edits). Read before acting: `AGENTS.md`,
`dokumente/x86/WELLE-A.md`, `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`
(§§0–5 plus the C record §§6–7), `grammatik/Grammatik/X86/Typen.lean`,
`bruecke/Bruecke/Quelle.lean`, `bruecke/Bruecke/Pflichten.lean`,
`bruecke/Bruecke/Pruefung.lean`, `bruecke/Bruecke.lean`,
`grammatik/Grammatik/Schlusssatz.lean` (pipeline, `Kette`,
`schlusssatz`), `grammatik/Grammatik/Zielsatz/Spec.lean` (premises
(a)–(d), `PrueferX`, `NutzerPflichtA`, `GabbroZiel`, `Einheit`),
`grammatik/Grammatik/Parser/UebersetzeAllg.lean` (declOf),
`grammatik/Grammatik/Zertifikate.lean` + `Zertifikat/REGISTER.txt`
shape, `dokumente/OFFEN.md` (O13–O14, O23, O25, O28–O29, O31, O37,
O39–O40), and signature-level greps over `KorrespondenzAllg.lean`
(`korrOk`, `korrOk_fnCorr`) and the `bruecke/` simulation/checker files.

## Exact names of new definitions/theorems

None. Docs-only lane: no Lean file added, no definition or theorem
introduced, no existing file touched. The document cites existing
interfaces only: `uebersetzeAllg`, `declOf`, `lowerAllg`, `elabU`,
`pre108`, `uebersetzeAllg_von_zeichen`, `uOf`, `einheitAllg`
(`S := leer`, `Q := axWahr`, `startsAllg`, `nullSp`), `nullB`,
`stimmigB`/`stimmig_of`, `rangB`/`rangAuto`/`rang_of`, `Pflichten`,
`zuBody`, `preExpr`, `postU`, `meetsU`, `hyps`, `calleesOf`,
`nutzer_aus_quelle`, `nutzerA_aus_quelle`, `bruecke_nutzer`,
`PrueferX`/`AkzeptiertSpecX`, `NutzerPflichtA`, `HardwareAnnahmen`,
`Laufzeit`, `GabbroZiel`/`GabbroZielSC`/`GabbroZielVerbund`,
`EmitLay`/`KCert`/`korrOk`/`korrOk_fnCorr`, `Kette`/`schlusssatz`,
`ketteAllg`/`emitLayLeer`/`aufzFn`/`aufzLock`/`aufzTraegerLeer`.

## Last full check outcome

No build run: docs-only task with no Lean/Rust changes, per the wave
rule ("A docs-only task needs file/claim checks, not a gratuitous
cargo/Lean run"). Baseline untouched — `git status` shows only the two
new files (`dokumente/x86/QUELLBRUECKE.md`, this report). No Lean
umbrella import added (no new Lean file exists to import).

## What remains open

- All of §3/§4 of the deliverable: tables/layouts, statics/globals,
  shared-atomic rely in a bridged unit, arenas/dynamic regions,
  recursion-depth machine bound, gate/syscall/foreign-body x86
  correspondence, linking validation, fragment-coverage sieve,
  entries/handlers/cores, floats/time/progress, optimisation
  certificates.
- The phase-B schema (`schluss_x86`) is a proposal: `X86BildLayout`,
  `valX86`, and `X86Verfeinerung` do not exist yet and belong to lanes
  272/273/274/276/278 plus the validator/refinement adapters of §7.
- Per-program trust-path violations named in §5 (notably the
  `Cert104` per-name section in `corrlean.rs`) are booked for removal
  by the owners, not by this lane.

## Anything in the task believed wrong

Nothing wrong. Two notes for the coordinator: (1) the task's "Read
bruecke/Bruecke/{Quelle,Bruecke}.lean" — there is no `Bruecke.lean`
under `bruecke/Bruecke/`; the umbrella is `bruecke/Bruecke.lean`, which
was read instead. (2) The HARD-RULES §13 inhabitation gate and §5 new-file
rule do not apply: no theorem was added and the task names no new Lean
file, so no `_zeuge` is owed by this lane; the schema's witness
obligation is stated as a requirement on future target theorems.
