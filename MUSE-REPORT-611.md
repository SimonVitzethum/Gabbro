# MUSE-REPORT-611: Independent closure review of candidate 599

Lane 611, clone `/home/simon/Dokumente/gabbro-muse/a611`, branch `muse/611`.
Owns only this file. Reviewed the exact snapshot in `.tmp/review/SNAPSHOT.json`
(HEAD `d26b8a608fffab7e4d784175865502e661102c97`, base `0044c2585bdd2ebad67d8d7bd5c3a4db11b171eb`,
files `MUSE-REPORT-599.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/ExpressionLowering.lean`) via
`.tmp/review/author-599/` (`PATCH.diff`, `BUILD-EVIDENCE.json`, owner task, both Lean files).

CANDIDATE: 599 d26b8a608fffab7e4d784175865502e661102c97

VERDICT: ACCEPT

## What was checked

1. Read the full candidate file (1208 lines) and owner task; compared every
   claim against actual definitions and theorems.
2. Banned-pattern grep over the candidate file: no `sorry`, `admit`,
   `axiom`, `native_decide`, `unsafe`, `intro _`, `have _ :=` (exit 1, zero hits;
   the one "admit" in build evidence is the English word "admits" in a comment).
3. Reproduced the build in my own clone by transiently placing the exact
   snapshot file plus its one import line, then reverted both:
   `./lean-probe grammatik/Grammatik/X86/ExpressionLowering.lean` ->
   `== 0 error(s)`, exit 0, with the identical standard axiom lines as the
   author evidence (`intWort_add/sub/sint`: propext + Quot.sound;
   all `senkung_*`/`senkAtom_korrekt`: propext + Classical.choice + Quot.sound;
   `istAtom/istFrag_von_*`: propext; all `zeuge_bytes_*`: propext + Quot.sound).
   `./lean-bau` -> `Build completed successfully (448 jobs)` on my newer tree.
   `git status` clean afterwards; nothing but this report is committed.
4. Name-collision check: `lauf_einzeln` already exists in
   `grammatik/Grammatik/X86/ParallelMoves.lean:98` with a different signature.
   The candidate renamed its helper to `lauf_einzeln_gleich`; no other name in
   the file collides with my tree. The author's evidence shows the collision
   was hit once mid-work and repaired by the rename.
5. Premise usage: every theorem's premises appear in its proof term or goal
   (`EnvRepr`/`Frisch`/range premises feed the value, memory, register, `rsp`
   and overflow conclusions; refusal theorems are `rfl` over `none`).
   No conclusion restates a premise; no contract parameter is quantified away;
   memory claims go through `lauf`/`laufBytes`, never a second interpreter.
6. Witnesses: `ZeugeD` writes its single table (`schreibt = true`);
   `zeuge_lauf_aendert_speicher` exhibits a fetched-byte run whose fourth step
   (store through `rbx`) changes cell 8192 from zero. Every theorem with an
   `Expr` premise has a joint `_zeuge` (`senkFrag_add/sub`,
   `senkAtom_korrekt_var`, `senkAtom_korrekt`, `senkung_add/sub/korrekt`,
   `senkung_ohne_ueberlauf_add/sub`, `istAtom/istFrag_von_*`), each carrying
   both the table fact and the memory-changing run. `Var`-only premises
   (`senkFrag_var`) need no `_zeuge` and have one anyway.
7. Refusals planted and proved: `senkFrag_verweigert_mul`,
   `senkFrag_verweigert_tief`, plus the forged-opcode fetched refusal
   `zeuge_byte_faelschung_verweigert` (all `decide`/`rfl` over real bytes).
8. Scope: only the new file plus one umbrella import line; no checker, Spec,
   goal, or optimiser-file edits; no new IR or interpreter; no OS assumptions.
   The fragment boundary (literals, variables, one ADD/SUB level over atoms)
   is honest and its CUTS block states exactly what is not proved (deeper
   nesting, other operators, generic whole-fragment flags, TSO bridge,
   whole-binary theorem, silicon).

## Finding (accepted, does not block)

`MUSE-REPORT-599.md` in the snapshot ends mid-sentence: its line 44 stops at
"`zeuge_senkung` (low" and line 45 is a pasted tool-truncation marker. The
Lean CUTS block and `BUILD-EVIDENCE.json` carry the missing substance
(axioms, green `lean-bau` at entry 49, banned-pattern check), and I
re-verified all of it independently, so this is a report-completeness defect,
not a proof defect. Minimal repair if wanted: author appends the build-result
line, open work, and interfaces to the report file. Bounded accepted scope:
the Lean candidate as pinned above; the truncated report tail is excluded from
acceptance and remediated by this report.

## Interfaces and next tasks (proposed ownership, not started)

- Producer: `senkFrag`/`senkAtom` + `senkung_korrekt` lower checked source
  expressions to `Befehl` lists any block-lowering lane can sequence with
  `lauf_anhang`. Consumer next: statement-level lowering (store of a lowered
  expression, sequence of blocks) reusing `EnvRepr`/`Frisch` per block.
- `Frisch` currently forbids all aliasing; block lowering with liveness may
  relax it to interference (noted in CUTS). Independent follow-up lane.
- The per-access target-to-W/GX simulation remains with its lanes (573-574);
  this candidate's sequential `lauf`/`laufBytes` runs compose with, not
  replace, that work.

## Last build result

`./lean-bau` with the candidate applied: `Build completed successfully
(448 jobs)`. After revert: `git status` clean; this report is the only change.
