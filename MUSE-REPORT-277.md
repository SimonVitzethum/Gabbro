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

## Review repair (2026-10-01)

The coordinator required four corrections before adopting the closing
architecture; all are applied in `QUELLBRUECKE.md`, owned files only:

1. No independent refinement premise in the delivered theorem. The
   schema now has three named parts: generic `valX86_sound`
   (`valX86 E bild = true → X86Verfeinerung E bild`, to be proved),
   internal composition lemma `schluss_x86_aus_verfeinerung` (takes
   `hR`, labelled INTERNAL, not the delivered claim), and delivered
   `schluss_x86` (takes only `hV`, derives `hR` via `valX86_sound`).
2. Full unit identity, not `E.P = P`. The schema takes
   `hE : E = einheitAllg u P hn` (every field fixed by `src`); beyond
   the fragment the rule is compute-or-prove-identity field by field,
   with `valX86 E bild` binding the full unit. §1.2 cites where the
   current frontend pins `S`/`Q`/starts/`sp0` to fragment defaults
   (`einheitAllg`: `leer`/`axWahr`/`startsAllg`/`nullSp`,
   `gestartet := []`) and books full-source unit coverage as open.
3. Loader / layout / silicon split. Loaded-image mapping goes through
   checked loader logic and `Laufzeit` (user/binding logic); layout
   correctness is a decided computation; hardware premises cover only
   silicon execution of validated bytes plus named timing bounds. OS /
   runtime implementations are never hardware assumptions. Applied in
   §§2, 4, 6, 7.
4. Guarantee preservation stated explicitly. §4 obligations list every
   transferred goal leg; §8 says the schema theorems are unimplemented
   proposals and no weakening is admitted for coverage.

## What remains open

- All of §3/§4 of the deliverable: tables/layouts, statics/globals,
  shared-atomic rely in a bridged unit, arenas/dynamic regions,
  recursion-depth machine bound, gate/syscall/foreign-body x86
  correspondence, linking validation, fragment-coverage sieve,
  entries/handlers/cores, floats/time/progress, optimisation
  certificates; plus full-source unit computation (§§1.2, 4) and the
  generic `valX86_sound` proof itself.
- The phase-B schema (`schluss_x86`, `valX86_sound`,
  `schluss_x86_aus_verfeinerung`) is a proposal: none of the three is
  claimed proved; `valX86` and `X86Verfeinerung` do not exist yet and
  belong to lanes 272/273/274/276/278 plus the validator/refinement
  adapters of §7.
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
