module

public import Grammatik.Zielsatz.Kern.PoolCertificate

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.PoolSnapshot

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer
open Invarianten.Frag.Symbolic Vertraege.Pruefer.Symbolic

local instance : DecidableEq zD.Ax := inferInstanceAs (DecidableEq Empty)

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
  with_unfolding_all
    apply function_success
    · rfl
    · decide
    · apply execution_success zPC zS zPoolSources {} none zEin (by rfl) invariants (by rfl)
        ((parameters (D := zD) 128 0 (zD.params zEin)).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · change 1 ≤ 16384; decide
      · rintro ⟨selected, member⟩
        cases selected
        exact environment_checked

abbrev readerSymbols : SymEnv zD Nat (zD.params zLies) := .nil
def readerBounded : readerSymbols.Bounded 0 := trivial
def readerInvariants : InvariantFormula zPC (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula zPC []).toOption.get (by rfl)
def readerCompiled := ending (requiresPolicy zPC (entryContext readerSymbols readerBounded))
  (lockFormula zS zPoolSources) {} none 128 (zPC.rumpf zLies) readerSymbols readerBounded
  (contractGoals zPC zLies readerSymbols readerBounded readerInvariants)
theorem readerCompiled_present : readerCompiled.toOption.isSome = true := by with_unfolding_all rfl
def readerCertificate := readerCompiled.toOption.get readerCompiled_present
theorem readerCompiled_result : readerCompiled = .ok readerCertificate := by with_unfolding_all rfl

theorem reader_checked : (checkFunction zPC zS zPoolSources {} none zLies).toOption.isSome = true := by
  with_unfolding_all
    apply function_success
    · rfl
    · decide
    · apply execution_success zPC zS zPoolSources {} none zLies (by rfl) readerInvariants (by rfl)
        ((parameters (D := zD) 128 0 (zD.params zLies)).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · change 1 ≤ 16384; decide
      · rintro ⟨selected, member⟩
        cases selected
        apply environment_success_of_valid zPC zS readerSymbols readerBounded (requiresPolicy zPC _)
          zPoolSources {} none readerInvariants (by rfl)
          ((Invarianten.Frag.Symbolic.translate (zPC.requires zLies) readerSymbols).toOption.get (by rfl))
          (by rfl) readerCertificate readerCompiled_result
        intro values
        with_unfolding_all
          change ((0 ≤ values (.inl (.slot () () 0)) ∧ values (.inl (.slot () () 0)) ≤ 100) ∧ True) →
            True → True → ∀ value : Int,
            ((0 ≤ value ∧ value ≤ 100) ∧ value = values (.inl (.slot () () 0))) →
            (value = values (.inl (.slot () () 0)) ∧ True)
        exact fun _ _ _ _ guarded => ⟨guarded.2, trivial⟩

abbrev wrapSymbols : SymEnv zD Nat (zD.params zWrap) := .nil
def wrapBounded : wrapSymbols.Bounded 0 := trivial
def wrapInvariants : InvariantFormula zPC (zD.invs.filter (schuldet zWrap)) :=
  (invariantFormula zPC []).toOption.get (by rfl)
def wrapCompiled := ending (requiresPolicy zPC (entryContext wrapSymbols wrapBounded))
  (lockFormula zS zPoolSources) {} none 128 (zPC.rumpf zWrap) wrapSymbols wrapBounded
  (contractGoals zPC zWrap wrapSymbols wrapBounded wrapInvariants)
theorem wrapCompiled_present : wrapCompiled.toOption.isSome = true := by with_unfolding_all rfl
def wrapCertificate := wrapCompiled.toOption.get wrapCompiled_present
theorem wrapCompiled_result : wrapCompiled = .ok wrapCertificate := by with_unfolding_all rfl

theorem wrapPrepared : (Snapshot.prepared (entryVC wrapSymbols .tru wrapCertificate.formula)).val = .tru := by
  with_unfolding_all rfl

theorem wrap_checked : (checkFunction zPC zS zPoolSources {} none zWrap).toOption.isSome = true := by
  with_unfolding_all
    apply function_success
    · rfl
    · decide
    · apply execution_success zPC zS zPoolSources {} none zWrap (by rfl) wrapInvariants (by rfl)
        ((parameters (D := zD) 128 0 (zD.params zWrap)).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · with_unfolding_all decide
      · rintro ⟨selected, member⟩
        cases selected
        apply environment_success_of_valid zPC zS wrapSymbols wrapBounded (requiresPolicy zPC _)
          zPoolSources {} none wrapInvariants (by rfl)
          ((Invarianten.Frag.Symbolic.translate (zPC.requires zWrap) wrapSymbols).toOption.get (by rfl))
          (by rfl) wrapCertificate wrapCompiled_result
        change ∀ values, (entryVC wrapSymbols .tru wrapCertificate.formula).denote values
        exact Snapshot.prepared_sound _ (by rw [wrapPrepared]; trivial)

/-- The original probe keeps every old-slot contract and its guarded read/write. -/
theorem contracts_checked : KontrakteGeprueftB zPC zS zFs zPoolSources = true := by
  apply contracts_success
  intro f
  cases f with
  | ein => exact writer_checked
  | lies => exact reader_checked
  | wrap => exact wrap_checked
  | haupt => decide

theorem vc_checked : Invarianten.Pruefer.invariantVCB zPC zS zFs zPoolSources {} (fun _ => none) [()] = true :=
  Bool.and_eq_true_iff.mpr ⟨by decide, contracts_checked⟩

theorem accepted : Akzeptiert zPC zS zFs [()] [.inl ()] [zHaupt] (sources := zPoolSources) = true :=
  Bool.and_eq_true_iff.mpr ⟨by decide, vc_checked⟩

end Gabbro.Grammatik.Zielsatz.PoolSnapshot
