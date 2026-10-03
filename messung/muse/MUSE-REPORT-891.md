# MUSE-REPORT-891: Optimiser rule — CMOV selection rule

## What was done

Implemented the DESIGN §3A tile "SETcc/CMOVcc where MEASURED suitable,
never by default" with the §7 flags-peephole premises ("rule in
register, flag-liveness") as a layer-A local rule lemma over
arbitrary values, in the new file
`grammatik/Grammatik/X86/OptCmovSel.lean` (plus the one import line in
`grammatik/Grammatik.lean`). No accepted IR exists yet (IR287 still
uncommitted), so the rule is proved over the real `Syntax`/`Semantik`
`exec`/`execStmt`/`execEnd` fragment, reusing `X86.ControlFlow`
(`cmovAnwenden`) and `X86.ConditionalMove` (taken/untaken value
equations, witnesses). Read before writing: `ConditionalMove`,
`ControlFlow`, `CostSummary`, `TableLayout`, `InstructionSelection`,
`BranchLayout`, `OPTIMIZER.md` §§3.10–3.11 hard gates, and
`DIRECT-COMPILER-DESIGN.md` §§3A/7/7A.

## New definitions and theorems (all in `Gabbro.Grammatik.X86`)

- `CmovSelCert` (6 Bool side conditions: `unvorhersehbar`,
  `billig`, `fehlerfrei`, `nurRegister`, `flagsFrisch`,
  `gleicheRundung`), `cmovSelZulassen` (admission conjunction;
  default stays branch).
- Refusals: `cmovSelVerweigert_speicher` (memory source — the
  load-bearing refusal: the unselected side may still fault),
  `cmovSelVerweigert_fehler`, `cmovSelVerweigert_vorhersehbar`,
  `cmovSelVerweigert_teuer`, `cmovSelVerweigert_flags`,
  `cmovSelVerweigert_rundung`; probes `probe_cmovSelZulassen_ok`,
  `probe_cmovSelZulassen_speicher`.
- Values: `selWert`, `selWert_genommen`, `selWert_nicht`,
  `cmovWaehlt_genommen`, `cmovWaehlt_nicht` (target select word is
  the taken arm word), `selWortLiest` (width-exact word readback),
  `selGleit_behaelt` (`gleitPasst` outcome preserved — IEEE: the
  select moves the exact pattern, adds no rounding).
- Certificate: `CmovSelBeleg` (`stelle`, `bedingungStelle`,
  `zulassung`, `biasBeleg`, `kostenBeleg` — local rewrite record
  plus recomputed analysis citations), `belegOk`, probes
  `probe_belegOk`, `probe_belegVerweigert_speicher`.
- Blocks: `branchEnd` (ite over two literal arms, leave-terminated),
  `selectEnd` (chosen literal bound, leave-terminated),
  `cmovWahlBlock` (select where admitted else branch),
  `cmovWahl_waehlt` (admitted choice IS the select).
- Helpers: `lese_leer` (empty read changes no world, by `rfl`),
  `lit_orte_leer` (literal reads no place, by `rfl`).
- TARGET `OptCmovSel_verbindung`: under admission (`hz`),
  validator-placed arm values (`hbed`, `hsrc`, `hdst`, `hlink`),
  run condition `b` over no places (`hc`, `hc0`), proves jointly:
  (1) select word = taken arm word; (2) `execEnd` outcome equality
  branch vs admitted choice (same constructor/worlds/envs — hence
  contracts at their place, call logs, shared accesses and
  same-shape budget accounting unchanged); (3) word readback;
  (4) `gleitPasst` preservation; (5) memory/flag frame (reused
  `cmovAnwenden_speicher`, `cmovAnwenden_flags`).
- Witnesses: `cmovWahl_waehlt_zeuge` and
  `OptCmovSel_verbindung_zeuge`, both joint on `refD`
  (`refEin_schreibt`) beside the memory-changing reached run `MB`
  (`refB_erreicht`, `refB_schreibt`); source condition `.wahr`,
  target state `witTrue` (taken arm `20` in `rbx`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptCmovSel.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Built Grammatik (511 jobs)`.
- Axioms: every new theorem depends at most on
  `[propext, Classical.choice, Quot.sound]` — the standard
  `gabbro_ziel` set. No `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`. No new diagnostic/gift/example/CLI numbers, no
  MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.

## What remains open (see CUTS)

No `Befehl` constructor / `Codec` row / bytes (CMOVcc has no pilot
encoding); no silicon correspondence; no TSO/GX bridge, ABI/loader
or timing claims; budget is same-shape source accounting (lane-860
pattern), formal level-(c) work bound stays with IR-VALIDIERUNG;
source-to-register placement premises are discharged per site by
the lowering lane.

## Notes and blemishes

- Commit `2898542a` carries the message "certificate: local rewrite
  record plus analysis citations" but contains the branch/select
  blocks (stale message file reused; `bf86065e` has the same
  message correctly). `git commit --amend` is denied by the lane
  permission gate, so the message stands; content of every commit
  is as described here.
- Technical: `if b then x else y` elaborates the condition as
  `b = true`, so post-`cases` goals need `if_pos rfl` /
  `if_neg (by decide)` rather than bare `rfl`.
- Task feedback: the DESIGN §7 table has no explicit CMOV-selection
  row; the premises implemented come from §3A (unpredictable AND
  cheap AND fault-free unselected side, register-only first) plus
  the §7 flags-peephole row (rule in register, flag-liveness).
  `TableLayout`/`CostSummary`/invariant exports were read but not
  imported: at layer A the lemma needs only value/outcome facts;
  cost summaries and duty bindings enter per site at layer C,
  which is the lowering/validator lane's part (stated as premises
  `hlink`/`hW`, not re-decided here).
