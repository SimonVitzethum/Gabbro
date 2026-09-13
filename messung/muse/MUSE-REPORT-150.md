# MUSE-REPORT-150 (lane 150: axiom/register fixture + the three remaining certificates)

## What was built

Two new files, imported at the end of `grammatik/Grammatik.lean`.
They close the lane-146 remainder exactly as that report prescribed
("a fixture lane (axioms + registers in the reference declaration,
`decReg` on the declaration) before their nullary fragments can be
certified with witnesses").

### `grammatik/Grammatik/ReferenzAR.lean` (~415 lines): fixture with axioms and registers

- `ARReg` (`w`/`r`, `deriving DecidableEq`), `ARAx` (`ruf0`/`ruf1`,
  `deriving DecidableEq`), `arSigMain` (no params, no result, holds the
  lock, writes).
- `arD : Deklaration`: one table `konto` (2 slots, `.int 0 100`, guarded
  by the single lock `m`, `braucht`), one function `main` (`()`), two
  nullary axioms with a real frame (`aschreibt _ _ = true` for both;
  `aerg .ruf0 = none` for `Stmt.axiomCall`, `aerg .ruf1 = some (.int 0 10)`
  for `Block.bindAxiom`), two registers (`rtyp` `.int 0 255`,
  `rklasse .w = .rw`, `rklasse .r = .r`, `spiegel .w = some .r`).
- `arDecReg : DecidableEq arD.Reg` as a **separate instance** (proved via
  `show DecidableEq ARReg`; plain `inferInstance` fails because instance
  resolution does not unfold the `arD.Reg` projection). No shared file
  edited, as tasked.
- Frames: `arHw0`/`arHw1`/`arHd0`/`arHd1` as **defs** (both sides are
  constantly `true`, so the carrier hypothesis has no content to use --
  the evidence is carried, not deduced; stating them as theorems would
  leave a named unused premise), `arHg0`/`arHg1`/`arHgd0`/`arHgd1` as
  theorems (`nomatch` uses its scrutinee), `arDarf`, `arStart`, `arEnde`,
  `arSchreibt`.
- Program `arP` (`main`: `ruf0(); return`), oracle `arO` (every axiom
  stores cap `100` at `konto[0]`; `ruf1` answers raw `7`), memory
  `arSp0` (all `0`), declared axiom ensures `arQ` (stated without the
  `AxEns` abbrev, so no `AxiomVertrag` import: `ruf1` answers the new
  slot value, `ruf0` promises `true`).
- F-machine run on thread 1: `arSchrittA` (`nimmt`), `arSchrittB`
  (`blatt` firing `arAxStmtAt`; the axiom has no result so
  `einpassenErg` always fits and the oracle's answer world carries the
  write; `neu = []` since `storeSlot` records no trace event),
  `arB_erreicht` (reached from `RufStartF`), `arMB_slot` (slot is `100`,
  via `storeSlot_hit`), `arB_schreibt` (slot `0 -> 100`), joint
  `arB_schreibt_zeuge`. NON-DEGENERATE: `main` writes `konto` by contract
  and by axiom frame; step B changes memory.

### `grammatik/Grammatik/ZeugnisStmt3.lean` (~395 lines): certificates + soundness + witnesses

In the style of `ZeugnisStmt2.lean` (plain-data certificates, recomputed
validity with `Decidable` instances, structural soundness, one lemma per
constructor, `decide`-closed acceptance and rejection):

- `CertStmt3 D V`: `axiomCall` (axiom + carried `Λc` + the four frame
  proofs, the `callInd`/`RufPasst`-as-proof precedent) and `transition`
  (both registers + `maske`/`bits`).
- `certStmt3Gueltig` (holdings equation, `aparams = []`, `aerg = none` /
  writable class, mirror equation, readable class), `decStmt3Gueltig` +
  `instDecStmt3` (the mirror equation is where the carried
  `[DecidableEq D.Reg]` instance is needed), checkers `certStmt3Ok`,
  `certSeq3Ok`, `certEnd3Ok`.
- `CertSeq3 D V`: `lift` (reuses `CertSeq`), `cons3` (new statements in
  blocks), `bindAxiom` (nullary axiom + pinned `.int lo hi` result, the
  `bindCall` precedent, four frames carried); `certSeq3Gueltig`,
  `decSeq3Gueltig` + `instDecSeq3`.
- `CertEnd3 D V`: `liftE` + `cons3E`; `certEnd3Gueltig`,
  `decEnd3Gueltig` + `instDecEnd3`.
- Soundness (every premise used, no `sorry`/`axiom`/`admit`):
  `axiomCall_sound`, `transition_sound`, joint `stmt3_sound`,
  joint structural `seq3_sound`, single-constructor corollary
  `bindAxiom_sound`, `end3_sound`, top `zeugnisStmt3_sound`
  (valid body print implies `∃ _ : Endblock …, True`).
- Witnesses (rule 13, all on `arD` + the `arMB` run, checkers closed by
  `decide`): `axiomCall_sound_zeuge` (nullary `ruf0` + frames),
  `bindAxiom_sound_zeuge` (`ruf1` binding `.int 0 10`),
  `transition_sound_zeuge` (`w`-from-`r`), `zeugnisStmt3_sound_zeuge`
  (`ruf0(); return` body).
- Two rejection probes (`¬ …Gueltig …` by `decide`): `ruf1` as
  `axiomCall` (forged no-result), `transition .r .w` (forged mirror and
  class).
- `#print axioms` for all 11: only `[propext, Classical.choice,
  Quot.sound]` -- the project's standard base, no extra axioms.

## Last build

- `./lean-bau` → `== 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (114 jobs)`).
- Two linter warnings remain in `ZeugnisStmt3.lean:42` (`l`/`Γ` not
  referenced in `certStmt3Gueltig` -- neither arm constrains the
  language/typing context, correctly so for these two shapes).
- No Rust work (no checker/emitter surface touched); no text-guardian
  documents moved. No codes, gifts or examples used (none reserved).

## What remains open

- Calls WITH arguments (axiom or indirect): same boundary as
  `ZeugnisStmt2.lean` (the `CertBlock5`/`Block5Args` precedent, not
  re-proved here).
- `arO` is NOT `GutO` (stores without `axiomSpur` trace events; booked
  in-file in CUTS). No run step or certificate needs `GutO`.
- No PC-machine run on `arD` (one F run is the witness every lemma
  builds on); `arQ` is the declared-ensures shape only, without the
  `KoerperGutA` obligation theory.

## Task feedback

Nothing in the task was weakened. One reading note: "one axiom with a
real frame and ensures" cannot cover both `axiomCall` (needs
`aerg = none`) and `bindAxiom` (needs `aerg = some`) with a single
axiom, so the fixture carries two (`ruf0`/`ruf1`, both with a real
write frame) plus a declared ensures `arQ` -- every reading of
"frame and ensures" is thereby instantiated.
