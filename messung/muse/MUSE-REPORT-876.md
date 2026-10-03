# MUSE-REPORT-876: Optimiser rule — flags peephole rule

## Task
Lane 876: flag-aware peephole rule lemma from the register with
flag-liveness; `x - x` to `0` dropping invalid flags; FMA fusion
refuse. Target: `OptPeepholeFlags_verbindung` + joint companion
`OptPeepholeFlags_verbindung_zeuge` (non-degenerate, memory-changing
reached run).

## What was done
New file `grammatik/Grammatik/X86/OptPeepholeFlags.lean` (owned),
one import line appended to `grammatik/Grammatik.lean` (owned).
No other files touched. No diagnostic/gift/example/CLI numbers,
no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits,
no friend-reserved optimiser files.

The rule is stated over the reused canonical vocabulary (`Typen`,
`Syntax`, `Semantik`, `Gleitkomma`, `KostenG`, `X86.Typen`,
`X86.Wort`, `ReferenzB`) — no accepted single IR exists in this
clone, so the covered fragment is the real `Syntax`/`Semantik`
`eval`/`execEnd` window, exactly like sibling lane file
`OptFoldConst.lean`. Generic over arbitrary values (`x : Int`).

Exact certificate shape: `FlagPeepholeCert` (`flagTot`,
`ganzzahlig`, `keinFMA` — recomputed liveness citation, integer-type
citation, fusion-shape citation) gating `subSelbstUmschreiben`
(the local rewrite record: `.sub (.lit x) (.lit x)` to
`.lit (x - x)` where admitted, identity otherwise).

## New definitions/theorems
- `FlagPeepholeCert`, `peepholeZulassen`
- Refusals: `peepholeVerweigert_lebenig`, `peepholeVerweigert_float`,
  `peepholeVerweigert_fma`; probes `probe_peepholeZulassen_ok`,
  `probe_peepholeZulassen_lebenig`, `probe_peepholeZulassen_float`,
  `probe_peepholeZulassen_fma`
- Value: `subSelbst_wert`, `subSelbst_null`, `probe_subSelbst`
- Width/IEEE: `subSelbst_wort`, `probe_subSelbst_wort`,
  `subSelbst_float_kein_null` (NaN − NaN = NaN ≠ 0 pin)
- Rewrite: `subSelbstUmschreiben`,
  `umschreibenVerweigert_identitaet` (refusal = identity, never warning)
- Observation/budget pins: `subSelbst_orte_original`,
  `subSelbst_orte_neu` (both sides read nothing — no concurrency
  observation change), `subSelbst_kosten` (literal costs ≤ removed sub)
- TARGET: `OptPeepholeFlags_verbindung` (value + `execEnd` outcome +
  `x - x = 0` + word image, at an arbitrary `Endblock.bind`
  continuation, covering contracts/call-logs/concurrency/budget
  downstream at once)
- ZEUGE: `OptPeepholeFlags_verbindung_zeuge` (`5 - 5` to `0` on
  `refD`, admitted cert, `leave` continuation, jointly with
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`)

Axioms: every printed theorem depends only on a subset of
`[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel`
standard); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Every premise of every theorem is used by its proof.

## Last build result
`./lean-probe grammatik/Grammatik/X86/OptPeepholeFlags.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `Build completed successfully (511 jobs)`; whole
`grammatik/` green, including the new module import.

## What remains open (see CUTS in the file)
- No target-machine liveness fixpoint: `flagTot` is a
  validator-recomputed citation, not derived here.
- No general same-expression `.sub e e` rewrite: with
  memory-reading operands the two sides take different `lese` read
  traces, so raw `execEnd` equality does not hold there. Only the
  literal-operand site is connected.
- No float value lemma beyond the refusal; no fused op in the model,
  so FMA refusal is certificate-level only.
- No machine-level work-bound inequality; no silicon/TSO-GX claim.

## Task feedback (nothing believed wrong)
The task's "generic rule lemma over arbitrary values" is satisfied
as genericity over arbitrary `x : Int` with the literal-operand
shape by construction (same reading as the `OptFoldConst`
sibling). The `lese`-trace boundary above is a genuine finding that
constrains the rule to this shape; it is recorded in CUTS, and the
rule as stated is not weaker than asked within that shape.
