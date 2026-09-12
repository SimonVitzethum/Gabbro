# MUSE-REPORT-81 -- lane 81: the CSL resource invariant, main theorem proved

Branch: `muse/81`. New file: `grammatik/Grammatik/CSLInvariante.lean`
(wired via `import Grammatik.CSLInvariante` at the end of
`grammatik/Grammatik.lean`). No existing file, theorem, or definition
modified or weakened.

## What was done

Proved the lane-54-cut main theorem on the lane-74-repaired model, in
three committed steps (skeleton, leaf lemma, main theorem), then the
rule-13 witness.

1. `blatt_erhaelt_slots` -- the leaf lemma extended to `axiomCall`.
   Lane 54's `blatt_slots_t_gleich` (CSLInvarianteC.lean) derives
   same-carrier impossibility from event goodness via the
   `execEreignis_aus_blatt_ohne_axiomCall` characterization, which is why
   `axiomCall` was fatal there. This file takes a shorter route that needs
   no events and no goodness at all: every direct table write
   (`assignSlot`, `assignDurch`, `schreibBytes`, `uebergang`) carries its
   guard `hL : darf D t Λ` on the constructor, so a same-carrier write by
   a thread not holding `L` contradicts `hfrei` through `HeldGenau`;
   foreign-carrier writes go through the store frame lemmas imported from
   `CSLInvarianteC` (`storeSlot_fremd_traeger`,
   `schreibBytes_fremd_traeger`, `storeGlob_slots_gleich`,
   `lese_slots_gleich`). The `axiomCall` case (new): a slot difference
   forces `D.aschreibt a t = true` through the oracle frame -- `hO`
   accessed as `.1` (Rahmen) only, per the lane-80 instruction -- and the
   new `hd` premise turns that into `darf`, hence held, contradiction.
   All other leaves never touch table slots (mirrored `execStmt`
   equations). Eleven compounds die at `hleaf`.
2. `csl_ressourceninvariante` -- the TARGET, stated verbatim (rule 12;
   see check below). Induction over `PCReach` with the conclusion itself
   as invariant: `start` by `hStart`; `take` pushes `L`-freedom back
   (taker's trace only gains, others keep theirs via `genUpdate_self` /
   `genUpdate_noteq`); `rel` either pushes back or, when the releaser
   itself held `L`, applies `hRelease` directly (no erase reasoning: its
   premises are exactly `hreachM`, the reconstructed step, `hg0`, and
   `hfree' f`); `leaf` splits on whether the stepping thread holds `L`
   (holder: `blatt_brav` preserves `haelt`, so `offen` is unchanged,
   contradiction; non-holder: IH plus `blatt_erhaelt_slots` moved across
   by `hLokal`).
3. `csl_ressourceninvariante_zeuge` -- rule-13 companion on `refD`:
   `t = konto`, `L` its lock, `inv = refInv81` ("the two slots agree").
   Proves all five target premises jointly (`refO_gut`,
   `refInv81_guard`, `refInv81_lokal`, `refInv81_start`,
   `refInv81_release`), exhibits the target's own conclusion at those
   values, shows the invariant is not trivially true (`badSp81`:
   slot 0 = 100, slot 1 = 0), shows a function writes the table
   (`refEin_schreibt ()`), and shows a reached memory-changing run
   (`refB_pc_erreicht`, `refB_pc_schreibt`: `take` then the writing
   leaf). On `refB_prog` no held-to-free transition exists per step
   (`take` contradicts its own `hself` at `Unit`; `leaf` preserves held
   locks; `rel` atoms never occur), so `hRelease` is vacuous there.

## Exact names of new definitions/theorems (`Gabbro.Grammatik`)

- `refInv81` (def): witness invariant, slots 0/1 of `konto` agree.
- `blatt_erhaelt_slots`: leaf slot preservation including `axiomCall`.
- `csl_ressourceninvariante`: the TARGET main theorem.
- Witness helpers: `refB_prog_kein_rel`, `refInv81_guard`,
  `refInv81_lokal`, `refInv81_start`, `refInv81_release`, `badSp81`,
  `badSp81_neg`.
- `csl_ressourceninvariante_zeuge`: rule-13 joint witness.

`#print axioms` for all four main items:
`[propext, Classical.choice, Quot.sound]` -- no `sorryAx`, no `sorry`.

## Rule-12 check

The TARGET statement was copied binder-for-binder
(`P O passes hO prog sp t L inv hGuard hLokal hStart hRelease`,
conclusion `∀ M pc, PCReach … → (∀ g, …) → inv M.speicher`). No premise
added, conclusion not weakened. The leaf lemma and witness helpers are
separately named theorems, as required.

## Last `./lean-bau` result line

`Build completed successfully (51 jobs).`
(`== 0 error line(s) in the COMPLETE output`.)
`./lean-probe grammatik/Grammatik/CSLInvariante.lean` first line:
`== 0 error(s) in the COMPLETE output`.
One linter warning remains (see below); the only other warning in the
log is the pre-existing `Geist.lean` one.

## What remains open

1. The `hreach` hypothesis of `refInv81_release` is unused (linter
   warning, build stays green). It is logically redundant, not
   accidentally so: every held-to-free step-transition is already
   impossible per step on `refB_prog`, reachability adds nothing. I kept
   the name (rather than `_`) so the warning documents the finding.
   Merged precedent for unused joint witness hypotheses: `hNoAx0` in
   `EigenZustandD.lean`. If the merge gate counts this as a rule-3
   violation, the honest repair is induction on `hreach` (it is consumed
   as the induction target); I judged that pure ceremony and did not do
   it -- say so if you disagree.
2. `Block.bindAxiom` still carries no guard premises (lane-74 F3):
   the same CSL hole persists one level up in `Block`. The leaf lemma
   here covers `Stmt.axiomCall` only, because only leaf statements fire
   in `PCSchritt.leaf`. A `bindAxiom` analogue of `hd`/`hgd` is a
   follow-up lane.
3. `GutO` use kept to the frame clause (`.1`) plus whole-`GutO`
   pass-through to `blatt_brav` (no clause destructuring), per the
   lane-80 instruction.

## What in the task I believe is wrong

Nothing material. Two notes: (a) The task's suggested invariant
"slot 0 of konto ≤ 100" is trivially true for every memory (the field
type is `.int 0 100`), so I used "slot 0 = slot 1" instead, with a
falsifying memory exhibited -- exactly the alternative the task
anticipated. (b) The route sketch ("case on take / release / leaf, and
on whether the stepping thread holds L") is accurate for `leaf`, but
the `rel` case does not need the holder split on `L' = L`: `hRelease`
applies directly whenever the releaser held `L`, regardless of which
lock is released.
