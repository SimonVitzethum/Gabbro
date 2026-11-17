module

public import Grammatik.Zielsatz.Kern.PoolCertificate

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.PoolSnapshot

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer
open Invarianten.Frag.Symbolic Vertraege.Pruefer.Symbolic

abbrev symbols : SymEnv zD Nat (zD.params zEin) := .nil
def bounded : symbols.Bounded 0 := trivial
def futureBounded : symbols.Bounded 1 := symbols.bounded_mono bounded (by decide)
def region : Snapshot.Region zD 1 := ⟨0, [.slot () () 0], by decide⟩
def policy := (requiresPolicy zPC (entryContext symbols bounded)).refine (by decide : 0 ≤ 1)
  (entryContext symbols futureBounded (some region)) (fun _ _ present => present.1)
def invariants : InvariantFormula zPC (zD.invs.filter (schuldet zEin)) :=
  (invariantFormula zPC []).toOption.get (by rfl)

def compiled := ending policy (lockFormula zS zPoolSources) {} none 128
  (zPC.rumpf zEin) symbols futureBounded (contractGoals zPC zEin symbols futureBounded invariants (some region))

theorem compiled_present : compiled.toOption.isSome = true := by with_unfolding_all rfl

def certificate := compiled.toOption.get compiled_present

theorem compiled_result : compiled = .ok certificate := by
  cases checked : compiled with
  | error cause => have present := compiled_present; rw [checked] at present; cases present
  | ok value => simp only [certificate, checked, Except.toOption, Option.get_some]

def formula : LProp (Key zD Nat) := .all (.inr 1) (.imp
  (.eq (.var (.inr 1)) (.konst 100)) (.and (.le (.var (.inr 0)) (.var (.inr 1))) .tru))

theorem formula_shape : certificate.formula = formula := by with_unfolding_all rfl

def requirement := (Invarianten.Frag.Symbolic.translate (zPC.requires zEin) symbols).toOption.get (by rfl)
def matrix := entryVC symbols requirement.payload (snapshotGuard (some region) certificate.formula)

theorem prepared_true : (Snapshot.prepared matrix).val = .tru := by
  unfold matrix
  rw [formula_shape]
  with_unfolding_all rfl

attribute [local irreducible] entryVC certificate checkEnvironmentAt
attribute [local implicit_reducible] entryContext

theorem environment_checked :
    (checkEnvironment zPC zS symbols bounded (requiresPolicy zPC (entryContext symbols bounded))
      zPoolSources {} none invariants).toOption.isSome = true := by
  apply environment_snapshot_success zPC zS symbols bounded (requiresPolicy zPC _)
    zPoolSources {} none invariants [.slot () () 0] (by rfl)
  apply environment_at_success zPC zS symbols futureBounded (some region) policy zPoolSources {} none invariants
    requirement (by rfl) certificate compiled_result
  change (Snapshot.decide matrix 1000000 _).toOption.isSome = true
  exact Snapshot.decide_of_prepared_true _ _ _ prepared_true

theorem writer_checked : (checkFunction zPC zS zPoolSources {} none zEin).toOption.isSome = true := by
  apply function_success
  · rfl
  · decide
  · apply execution_success zPC zS zPoolSources {} none zEin (by rfl) invariants (by rfl)
      ((parameters (D := zD) 128 0 (zD.params zEin)).toOption.get (by rfl)) (by rfl)
    · change 1 ≤ 16384; decide
    · rintro ⟨selected, member⟩
      cases selected
      exact environment_checked

end Gabbro.Grammatik.Zielsatz.PoolSnapshot
