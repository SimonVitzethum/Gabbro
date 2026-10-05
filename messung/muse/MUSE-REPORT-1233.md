# MUSE-REPORT-1233 — Pipeline work bounds for branches and loops

Lane 1233 (branch `muse/1233`, clone `/home/simon/Dokumente/gabbro-muse/a1233`).
Follow-up of lane 1165 (`PipelineWork.lean`). All work is in the owned files only:
NEW `grammatik/Grammatik/X86/PipelineWorkBranches.lean` plus one import line
appended to `grammatik/Grammatik.lean`. No existing file touched otherwise.
Rust out of scope (no Rust changes).

## What was done

Branch bounds over the accepted `iteCode` shape (`Pipeline.lean`), reused unchanged:

- `iteSchranke` (def): worst-case retired instructions of an if/else —
  compare code, one taken jump, the LONGER branch, one end jump.
- `iteCode_laenge`: static whole-list length of `iteCode`
  (`code + 1 + pt + 1 + pe`).
- `itePfad_schranke`: either dynamic path (taken / fall-through) is at most
  the worst case. Proved with explicit `Nat.le_max_*` lemmas: this toolchain's
  `omega` treats `Nat.max` as opaque.

Validator with derived (never assumed) coverage:

- `pruefeZweig` (def): decided check `prog.length ≤ src * 6` — recomputed
  from the lowered list.
- `deckung_von_laenge`: length fit implies `Deckung pipeSummary src`.
- `pruefeZweig_korrekt`: accepted list is covered.
- `deckung_ite`: branch specialization (static length counts both branches;
  the retired path is only smaller).
- `iteSchranke_pd` (`= 12`, `rfl`), `deckung_ite_pd` (witness ite static 17
  covered at source budget 3, `by decide`).

Main correctness, in the style of `pipeline_arbeit_korrekt`:

- `zweig_arbeit_korrekt`: for a lowered block whose list the validator
  accepts, the fetched-byte run from the loaded image reaches the state
  corresponding to the REAL `execBlock` outcome (`senkBlock_korrektC` reused
  as a black box — no second interpreter), AND `targetWork prog ≤ k` AND
  `tt ≤ B * k` through the validator-derived coverage plus the named
  per-form hardware costs (`budgetAusfuehrung_transfer`).

Loops over the accepted `PipelineLoops.lean` lowering, reused unchanged:

- `schleife_budget_transfer`: `n' ≤ n` implies
  `schleifeSchritte n' m ≤ schleifeSchritte n m` — a source iteration budget
  covers every run finishing inside it (explicit `Nat.mul_le_mul_right`;
  `omega` cannot do the nonlinear step).
- `schleife_schritte_pd` (`= 9`, `rfl`): one round over a six-row body.
- `senkBlock_verweigert_retry`: generic over EVERY bound `n` (PipeBlock.lean
  proves the bound-5 instance; this is the general statement over the same
  catch-all arm, cited in the docstring) — unbounded loops stay refused.
- `senkBlock_verweigert_forever`: `forever` has no `senkBlock` lowering.

Poison probes (all firing by computation):

- `gift_zweig_knapp` (17-instruction ite lowering refused at budget 2),
  `gift_zweig_ok` (accepted at budget 3 — positive probe),
  `gift_retry_sieben` (bound 7; PipeBlock pins bound 5),
  `gift_forever`.

Joint witnesses, all with the accepted non-degenerate package
(`PipePaket`/`pipePaket_hold`: one table its contract writes, source slots
`7 -> 35` / `9 -> 6`, fetched-byte run observably changing memory):

- `senkBlock_verweigert_retry_zeuge`, `senkBlock_verweigert_forever_zeuge`.
- `zweig_arbeit_korrekt_zeuge`: the widened `pdSrc`/`pdProg` program at
  `x = 30` (then-branch, rows `7 -> 65` and `9 -> 130` through actual
  `execBlock`, both memory-changing), validator at source budget 6,
  named time through `profilZeuge` with per-step bound 3 (14-arm
  `Befehl` case analysis in the style of `hb_pwProg`; the cost
  itself by `rfl`-evaluation), image facts via `kompiliert_geladen` /
  `imageOk_*`, lowering pinned by `validate_sound` + generic
  `decodeAll_encodeAll`.

## Check results

- `./lean-probe grammatik/Grammatik/X86/PipelineWorkBranches.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (last run): `Build completed successfully (641 jobs).`
  (Two earlier `lean-bau` runs failed with `failed to read file` on
  dependency oleans that EXIST (`Init/Data/Option/Lemmas.olean`,
  `X86/ISA.olean`) — transient apparatus/IO contention, cleared on retry;
  no proof content changed between the failing and the green run.)
- `python3 instrumente/pruefe-kein-sorry.py --rev muse/1233 --diff master`:
  `0 violations`.
- `#print axioms` for all 21 constants: each is a subset of
  `[propext, Classical.choice, Quot.sound]` (most use fewer; both defs and
  the `decide`/`rfl` witnesses use none). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere in the new file.

## What remains open (also in the file's CUTS)

- `Deckung` counts the STATIC whole-list length (both branches); the
  dynamic-path bound is arithmetic only, not connected to a taken-path
  `lauf` prefix.
- Loop work stops at the accepted labelled-step budget: per-round body
  correspondence and the labelled-to-bytes leg stay with `PipelineLoops`
  (`schleife_korrekt_endlich`, `schleife_bytes`); no
  retired-instruction-per-labelled-step claim here.
- Entry/image admission beyond `Pipeline.CodeAt`, no TSO/concurrency
  claim, named timing stays a hardware assumption.

## Notes for the merger / things in the task I read differently

- Name resolution (all handled, documented in CUTS): `Block` is
  `_root_`-qualified (the bare name resolves to `ISARelax`'s `Block`
  through this file's own namespace path — no `open`/`hiding` fixes
  that); `CodeAt` is `Pipeline`-qualified (`ISAExecution` defines
  another); `layoutVon`/`kompiliert_geladen`/`imageOk_*` need
  `open PipelineImage` (my first version missed it).
- `Vertrag` spelled capital here while the tree writes `vertrag D` in
  binders: both elaborate to the same type (my `V : Vertrag D`
  unifies everywhere `Stmt`/`Block`/`senkBlock` expect it — the whole
  file is green because of it, not in spite of it).
- Honestly weaker than the task sentence in one place: "worst-case
  retired-instruction bounds for if/else" — the retired-path part is
  proved (`itePfad_schranke`), but the coverage that feeds the transfer
  still counts both branches statically. I state this openly rather
  than claiming a dynamic work count I did not prove.
