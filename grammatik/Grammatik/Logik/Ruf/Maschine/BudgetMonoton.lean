/-
  File:      Grammatik/Logik/Ruf/Maschine/BudgetMonoton.lean
  Subject:   THE BUDGET IS MONOTONE: a run of machine G with the `forever` budget `p` is, step for step, a run
             with every larger budget `p + j`, on the machines whose `ewig` counters are `j` higher.

  Machine G gives every `forever` instance the budget `passes` when it is entered (`dannForever` writes
  `.ewig a passes …`) and counts it down per pass (`ewigWeiter`); at `0` the loop stops with the named budget
  stop. The budget is the ONLY thing `passes` decides in a step: a leaf, `leave` and `next` run the same at
  every budget (`execStmt_blatt_passes`). So shifting every counter by `j` (`RufMaschineG.plus`) maps each step
  at budget `p` to a step at budget `p + j` (`rufSchrittG_plus`), and every run (`rufErreichbarG_plus`, over GX
  `rufErreichbarGX_plus`, the thread machine `fadenErreichbarX_plus`). The start machine has no counter
  (`rufStartG_plus`).

  Reading: the family of budgets is increasing, and a finite run of the program -- any prefix of an unbounded
  run -- is a run at every budget above the number of its passes. A stop on budget is never final: from the
  shifted machine one budget higher the stopped loop takes its next pass (`ewig_budget_unecht`).
-/
module

public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton.Teil1
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton.Teil2
