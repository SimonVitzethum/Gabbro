# MUSE-REPORT-1177: Source-computed units and duties feeding the pipeline

Lane 1177, clone `/home/simon/Dokumente/gabbro-muse/a1177`, branch `muse/1177`.
Owned files only: `grammatik/Grammatik/X86/PipelineUnit.lean` (new, ~1755 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was done

The pipeline takes the program as Lean data (a `Block`). This lane connects it
to the source-computed unit and its duties, generically (no per-program rule,
no second interpreter, no SSA IR):

- **Projection** `rumpfBlock`: `Endblock` straight-line `assignSlot` chains
  (exactly the T3 body language without calls) become the pipeline `Block`;
  tails map to `.nil`; everything else (calls, `ite`, binders, locks,
  loops) is refused (`none`). `rumpfEnde` projects the tail.
- **Bridge**: `rumpfBlock_total` (a projected block always runs `.ok`
  through the real `execBlock`) and `rumpfBruecke` (the full body run is the
  tail run at the reached world), both by fuel induction reusing the accepted
  `execStmt_assignSlot`.
- **Closing check** `einheitSchluss` (decided `Bool` per function):
  projection, return tail, `validate`, `imageOk`, `weltOk`,
  `prologImageOk`, `eintrittZulassung`, and the entry duty (`requires` at
  the actual arguments), with `einheitSchluss_verbindung`, full leg
  unpacking (`einheitSchluss_legs`), seven leg projections and seven
  `ohne_*` refusal theorems.
- **Correctness** `einheit_correct_entry` in the style of
  `pipeline_correct_entry`: from the closed check plus a source body run
  reaching `.zurueck`, the fetched run from the admitted entry reaches the
  code end with world/environment represented, stops, keeps the stack word,
  links the reached prefix world to the source return, and carries the
  entry duty. Composes bridge + totality + `pipeline_correct_entry`.
- **Call-site duties** `einheit_ruf_req` / `einheit_ruf_ens` reusing the
  accepted `ContractSites` producers (`callSite_vorOk`,
  `rufAt_ok_gibt_ens`) plus totality for the callee prefix run.
- **T3 whole-unit check** `t3Stand` / `t3EinheitOk` / `t3Grund` over the
  generic lowering (`UProg`, `lowerFnAt`): per-function decided verdicts,
  covering (`t3Einheit_gedeckt` over `List.finRange`, the same coverage
  `lowerAllg` uses) and refusal (`t3Stand_verweigert`,
  `t3Einheit_verweigert` via `all_verweigert_aux`) theorems. Evaluated on
  the real elaborated unit `uExp108` (`t3_uExp108`, by `decide`).
- **Witnesses** on one non-degenerate program (one table some function
  writes; reached run changes slot `7 → 42` and target bytes): joint
  `_zeuge` for `rumpfBlock_total`, `rumpfBruecke`, `einheitSchluss_legs`,
  `einheit_correct_entry` (with byte-level read-back 42),
  `einheit_ruf_req`, `einheit_ruf_ens`.
- **Poison probes** for every refusal leg: `gift_ruf`, `gift_ite`,
  `gift_bind`, `gift_ende_ruf`, `gift_endrueck`, `gift_bytes_falsch`,
  `gift_bild_falsch`, `gift_welt_falsch`, `gift_prolog_falsch`,
  `gift_eintritt_falsch`, `gift_requires_falsch`.

## Check results

- `./lean-probe grammatik/Grammatik/X86/PipelineUnit.lean`: `== 0 error(s)`.
- `./lean-bau`: `Build completed successfully (608 jobs).`
- `#print axioms` for every theorem: only `propext`, `Classical.choice`,
  `Quot.sound` (the goal-allowed set); many are `[propext]` alone.
- Two cosmetic linter warnings remain (`unusedVariables` on two `∃`
  statement binders in `einheit_correct_entry_zeuge`, a reference-tracking
  quirk after the determinism rewrite; not errors).

## What remains open / is weaker than the task ask

1. **No `pipeline_refuses`-style byte theorem.** Deliberate and documented
   in CUTS: a projected prefix always runs `.ok`, so no source `.grund`
   ever reaches a refusal exit from a projected body; that theorem shape is
   vacuous for this fragment. Refusals are static and decided instead.
   Closing a byte-level refusal would need exit stubs for trailing grunds,
   which do not exist at unit level.
2. **`ite`-carrying bodies are refused at unit level** (they stay lowerable
   at block level through the pipeline directly).
3. **Post-run `ensures` of the entry function is user logic**, not derived;
   `ensures` is carried only at call results.
4. `retGrund` tails are uninhabited at `gruende = 0` (witness decl); the
   `istRueck` leg refuses them generically.

## On the task text

Nothing in the task is wrong, but one ask overreaches for this fragment:
"a refusal theorem ... (`pipeline_refuses_*)" presumes failing source runs
inside the lowered code, while the only lowerable unit prefixes (straight
`assignSlot` chains) cannot fail. The delivered static refusal coverage is
the honest form; the gap is recorded in CUTS, not hidden.

Co-Authored-By: muse-agent-1177 <muse-agent-1177@noreply.invalid>
