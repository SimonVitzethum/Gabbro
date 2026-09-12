# MUSE-REPORT-15: Q-contracts degenerate -- the finding as theorems

Lane 15, branch `muse/15`. New file `grammatik/Grammatik/QLeer.lean`
(+ `import Grammatik.QLeer` at the end of `grammatik/Grammatik.lean`).

## What I did

Instantiated the Q-contract degeneration on a concrete one-function
declaration `qD` (no tables/globals/locks/marks/invariants/axioms/registers;
`Fn := Unit`, `qfn := ()`): parameter `k : int in 0 .. 5`
(`.int 0 5`), result `int in 1 .. 6` (so `k + 1` always fits range):

* `qRequires : Expr qD [.int 0 5] [] .bool` -- `requires k != 0`
  (`.nicht (.eq (.var .hier) (.lit 0))`).
* `qEnsures : Expr qD [.int 1 6, .int 0 5] [] .bool` --
  `ensures result = k + 1`
  (`.eq (.var .hier) (.add (.var (.dort .hier)) (.lit 1))`).
* `qP : Programm qD` with those two contracts and the honest body
  `qRumpf` (returns `k + 1`).

Theorems (all three task claims confirmed, none refuted):

1. `qRequires_nowhere (sig : World qD) : ¬ QRequires qP qfn sig` --
   falsifying witness `rhoK0` (`k = 0`); the world is arbitrary, `rfl`
   computes `wahr? ... = false`.
2. `qEnsures_nowhere (sig : World qD) : ¬ QEnsures qP qfn sig` --
   falsifying pair `(vK6, rhoK0)` = `(result 6, k = 0)`. Note: the body
   returns `k + 1` honestly, yet the Q is false -- it demands the
   postcondition at EVERY return value, including wrong ones. The
   Q-predicates never look at the body.
3. `qSeedAll_unmoeglich_req` / `qSeedAll_unmoeglich_ens` --
   the `hSeedAll` premise of `ziel_nutzer_last_aus_pc_Q` (head validity of
   both Q-contracts) yields `False` for any run with a member thread `g`
   with `J.code g = qfn` (premises `hg`, `hcode`, `sp`, `hSeedAll` -- all
   used). Two separate theorems, one per leg, so each proof uses the
   premise it derives from.

Rule-3 hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no
premise of type `Prop` itself; axiom print shows only the ambient
`[propext, Classical.choice, Quot.sound]` the whole project shares.
Conclusions are `¬ Q ... sig` / `False`, not renamed premises; the
contracts hold at no world rather than being vacuous invariants; semantics
is not invoked beyond `eval` on a literal. File ends with the `CUTS:`
block and four `#print axioms`.

Build caution: my first draft had `geteilt_bewacht := fun t h => by simp at h`,
which pulls `sorryAx` into the declaration; changed to `fun t => t.elim`
(matching `Satz.leer`) -- clean after that.

## New definitions/theorems

`qSig`, `qD`, `qfn`, `qRequires`, `qEnsures`, `qRumpf`, `qP`, `rhoK0`,
`vK6`, `qRequires_nowhere`, `qEnsures_nowhere`,
`qSeedAll_unmoeglich_req`, `qSeedAll_unmoeglich_ens`
(all in `Gabbro.Grammatik`).

## Last `./lean-bau` result

`Build completed successfully (30 jobs).` (QLeer built as job 28/30;
its four `#print axioms` lines each report
`depends on axioms: [propext, Classical.choice, Quot.sound]`.)

## What remains open

* Vacuous scope: if no member thread runs `qfn`, `hSeedAll` is trivially
  suppliable. Scoped out by design (it says nothing about the program).
* No end-to-end application to `ziel_nutzer_last_aus_pc_Q` itself -- that
  needs the full run-side wiring (section 13 remainder), out of lane.
* No `.wahr`-contract statement: vacuous contracts have true Qs; the
  degeneration needs a proper parameter/result.
* Repair direction (not attempted): instantiate `Pre`/`Post` at call shape
  (`exists rho`, entry world, actual return value) instead of
  `forall`-over-everything -- that is a design change for another lane.

## Anything in the task I believe is wrong

Nothing: all three claims held as stated. One scoping note -- claim (3)
as worded ("the premise `hSeedAll` ... cannot be supplied for such a
program") is true only for runs that actually call the function; the empty
members case supplies it vacuously. The two theorems carry that scope
explicitly (`hg`, `hcode`).
