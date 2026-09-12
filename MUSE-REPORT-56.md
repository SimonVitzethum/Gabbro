# MUSE-REPORT-56

Lane 56, own-state projection (attempt D of 2). New file
`grammatik/Grammatik/EigenZustandD.lean` (2039 lines), imported at the end of
`grammatik/Grammatik.lean`. No existing file touched except the import line.

## What was asked

Prove the fixed target `eigenzustand_nur_eigene_schritteD` (a foreign step by
`h != g` keeps every slot of `t` when no `h != g` program text names `t`)
with no premise quantified over contracts or statements, or report the
statement form that falsifies it with a concrete counterexample.

## What I found

The target AS STATED is FALSE. The falsifying constructor is
`Stmt.axiomCall`, proved as `EZD.AxGegen.axiomCall_ohne_ereignis_falsch`:
a `GutO` oracle that writes `t` records NO event with carrier `Sum.inl t`
(`GutO` forces `(O.wirkt ..).1.spur = sigma.spur`), so the leaf rule's `hcar`
is vacuous for it, `hNurG` can hold (empty/carrier-free program texts), yet
slots of `t` change. Concrete data: one-table/one-axiom declaration `D2`,
oracle `O2` flipping the slot (`O2gut` proves `GutO`), statement `axCall`;
`axFeuert` (slot flips) and `axNeu_kein_schrieb` (recorded list empty) supply
the two halves. This is the finding the task asks for.

## What I proved instead (rule 12, separately named)

`EZD.eigenzustand_nur_eigene_schritteD_rep`: the target plus one explicit open
remainder premise `hNoAx` (no declared oracle write to `t` fires at this
step). `hNoAx` quantifies only over this step's own firing data (statement
indices, environment, outcome world, recorded list, atom) -- nothing over all
contracts/statements. The report explains why it is needed (above) and that
the repaired theorem is STRONGER than the target in all other respects
(identical conclusion, one added assumption).

Route, bottom-up, all in the new file:
- `neu_of_suffix`, `neu_head`: outcome spur to recorded list.
- `schreibBytes_spur_suffix`, `schreibBytes_has_write`,
  `schreibBytes_slots_other`: the byte fold.
- `ereignisSchreibt` (write-flag projection).
- Write-event lemmas: `assignSlot_neu`, `assignDurch_neu`, `uebergang_neu`
  (failed guard yields no world), `schreibBytes_neu` (needs `0 < n`; `n = 0`
  keeps slots -- positivity split, no new-prefix invariant needed).
- Oracle frame: `axiomCall_slots_frame` (via `axiomAntwort_gut`'s `Rahmen` leg).
- Slot preservation per non-recording leaf: `assignGlob_slots_fest`,
  `publish_slots_fest`, `assignVar_slots_fest`, `regSchreib_slots_fest`,
  `ret_slots_fest`, `transition_slots_fest`, `advances_slots_fest`,
  `retires_slots_fest`, `retGrund_slots_fest`, `leave_slots_fest`,
  `next_slots_fest`, `call_slots_fest`/`callInd_slots_fest` (through `keinRuf`
  both yield no world -- vacuous), other-table forms
  (`assignSlot_andere_fest`, `assignDurch_andere_fest`, `uebergang_andere_fest`,
  `schreibBytes_andere_fest`), `schreibBytes_null_fest`,
  `axiomCall_nichtschreibt_fest` (needs `D.aschreibt a t = false`).
- `blattSlots_dispatch`: all 27 `Stmt` arms -- recorded write, slots kept,
  or declared oracle write (third disjunct names the axiom data and the firing).
- `pcSchritt_fremd_fest`: leaf via dispatch plus `hcar` against `hNurG`;
  take/release keep `M.speicher` by construction (`rfl`).
- Repaired target consumes `PCReach` by induction (both branches close through
  the step lemma; every premise is used).

Witness (rule 13): `eigenzustand_nur_eigene_schritteD_rep_zeuge` instantiates
ALL premises jointly on a non-degenerate program: `BG.D1` (one table, owner
contract writes it), two-step run -- owner write `false -> true` (memory
changes, `wSchreibtWechsel`) then foreign `assignVar` (slots preserved,
`wStep2` with carrier-free atom). `hNurG` by `wNurG`, `hNoAx` by `wNoAx`
(`D1.Ax` empty), reachability by the two-step derivation. Note: no `_zeuge`
exists for the EXACT target name (its premises are jointly contradictory at
`axiomCall` -- that IS the finding); the joint witness is proved for the
repaired theorem.

## Verification

- `./lean-probe grammatik/Grammatik/EigenZustandD.lean`: 0 errors.
- `./lean-bau` last line: `Build completed successfully (37 jobs).`
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed
  premise, no `intro _`/`have _ :=` discards (checked by grep).
- `#print axioms` for the five main theorems: all depend only on
  `[propext, Classical.choice, Quot.sound]`.

## What remains open

- Discharging `hNoAx` for programs whose axioms DO write `t`: needs a
  per-axiom event axiom or a program-text coverage argument (`progAus`
  atoms carry `stmtTraeger`, which covers declared axiom writes) -- not
  attempted here since the task fixes an arbitrary `prog`.
- The sibling lane attempts the same target in `EigenZustandC.lean`;
  duplication/merge strategy is the folder owner's call.
- Two Lean-environment notes for future lanes: the `set` tactic is
  unavailable in this toolchain (avoid it); a bare `nomatch g` inside a
  structure instance swallows following fields -- parenthesize it.
