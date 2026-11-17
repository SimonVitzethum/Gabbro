module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Logik.Invarianten.VC.Witness


@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.LoopWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC
open Invarianten.VC.Witness

/-- Each actual pass increments len while len < cap. The signature really
    writes len, so preserving len <= cap is a nonempty owed return duty. -/
def body (count : Nat) : Endblock declaration contract false [] [] :=
  .cons (.retry count (.not guard)
    (.cons (.assignGlob false (.eng (.add lengthValue (.lit 1)) 0 10 lengthValue)
      rfl (access false)) .nil) .nil)
    (.ret .empty (List.Perm.refl _))

def loopProgram (count : Nat) : Programm declaration :=
  { program with rumpf := fun _ => body count }

def hints : LoopHints declaration := fun _ => some invariant

open Invarianten.Frag.Symbolic Vertraege.Pruefer.Symbolic SelectionWitness

abbrev selectedCount (enabled : Bool) : Nat := if enabled then 100 else 2
abbrev selectedProgram (enabled : Bool) := loopProgram (selectedCount enabled)
abbrev selectedHints (enabled : Bool) : LoopHints declaration := if enabled then hints else fun _ => none
abbrev loopBudget : VCBudget := { expansion := 4 }
abbrev symbols : SymEnv declaration Nat (declaration.params ()) := .nil

theorem symbols_bounded : symbols.Bounded 0 := trivial

def obligations (enabled : Bool) :
    InvariantFormula (selectedProgram enabled) (declaration.invs.filter (schuldet ())) :=
  (invariantFormula (selectedProgram enabled) (declaration.invs.filter (schuldet ()))).toOption.get (by rfl)

def selectedHint (enabled : Bool) := (loopHint (selectedHints enabled) ()).toOption.get (by cases enabled <;> rfl)

theorem selectedHint_result (enabled : Bool) : loopHint (selectedHints enabled) () = .ok (selectedHint enabled) := by
  cases enabled <;> rfl

def compiled (enabled : Bool) := Vertraege.Pruefer.ending (requiresPolicy (selectedProgram enabled) (entryContext symbols symbols_bounded))
  (S := SperrInv.leer declaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none))
  loopBudget (selectedHint enabled) 128 ((selectedProgram enabled).rumpf ()) symbols symbols_bounded
  (contractGoals (selectedProgram enabled) () symbols symbols_bounded (obligations enabled))

theorem compiled_present (enabled : Bool) : (compiled enabled).toOption.isSome = true := by
  cases enabled <;> with_unfolding_all rfl

def certificate (enabled : Bool) := (compiled enabled).toOption.get (compiled_present enabled)

theorem compiled_result (enabled : Bool) : compiled enabled = .ok (certificate enabled) := by
  have present := compiled_present enabled
  cases result : compiled enabled with
  | error cause => rw [result] at present; cases present
  | ok value => simp only [certificate, result, Except.toOption, Option.get_some]

def requirement (enabled : Bool) :=
  (Invarianten.Frag.Symbolic.translate ((selectedProgram enabled).requires ()) symbols).toOption.get (by rfl)

abbrev lengthTerm : LTerm (Key declaration Nat) := .var (.inl (.glob false))
abbrev capacityTerm : LTerm (Key declaration Nat) := .var (.inl (.glob true))
def invariantFormula : LProp (Key declaration Nat) :=
  .lt (.sub (.sub lengthTerm capacityTerm) (.konst 1)) (.konst 0)
def exitFormula : LProp (Key declaration Nat) := .and .tru invariantFormula

def branchFormula (continued : LProp (Key declaration Nat)) : LProp (Key declaration Nat) :=
  .and (.imp (.not (.lt lengthTerm capacityTerm)) exitFormula)
    (.imp (.not (.not (.lt lengthTerm capacityTerm))) continued)

def stepFormula (next : Nat) (post : LProp (Key declaration Nat)) : LProp (Key declaration Nat) :=
  let value : LTerm (Key declaration Nat) := .var (.inr next)
  let source : LTerm (Key declaration Nat) := .add lengthTerm (.konst 1)
  let range : LProp (Key declaration Nat) := .and (.le (.konst 0) source) (.le source (.konst 10))
  .all (.inr next) (.imp
    (.and (.and (.le (.konst 0) value) (.le value (.konst 10)))
      (.and (.imp range (.eq value source)) (.imp (.not range) (.eq value lengthTerm))))
    (.all (.inr (next + 1)) (.imp (.eq (.var (.inr (next + 1))) value)
      (renameProp (swapKey (.inl (.glob false)) (.inr (next + 1))) post))))

def unrolledFormula : Nat → Nat → LProp (Key declaration Nat)
  | 0, _ => branchFormula exitFormula
  | count + 1, next => branchFormula (stepFormula next (unrolledFormula count (next + 1)))

def typedFormula : LProp (Key declaration Nat) :=
  .and (.and (.le (.konst 0) lengthTerm) (.le lengthTerm (.konst 10)))
    (.and (.and (.le (.konst 0) capacityTerm) (.le capacityTerm (.konst 10))) .tru)

def hintedFormula : LProp (Key declaration Nat) :=
  .and invariantFormula (.all (.inl (.glob false)) (.all (.inl (.glob true))
    (.imp typedFormula (.and (.imp .tru (.imp invariantFormula
      (branchFormula (.and (stepFormula 0 invariantFormula) exitFormula)))) .tru))))

theorem unrolled_shape : (certificate false).formula = unrolledFormula 2 0 := by
  with_unfolding_all rfl

theorem hinted_shape : (certificate true).formula = hintedFormula := by
  with_unfolding_all rfl

def typedPair (length capacity : Int) : Prop :=
  (0 ≤ length ∧ length ≤ 10) ∧ ((0 ≤ capacity ∧ capacity ≤ 10) ∧ True)

def exitVC (length capacity : Int) : Prop := True ∧ length - capacity - 1 < 0

def stepVC (length : Int) (post : Int → Prop) : Prop :=
  ∀ value : Int,
    ((0 ≤ value ∧ value ≤ 10) ∧
      (((0 ≤ length + 1 ∧ length + 1 ≤ 10) → value = length + 1) ∧
        (¬ (0 ≤ length + 1 ∧ length + 1 ≤ 10) → value = length))) →
    ∀ stored : Int, stored = value → post stored

def branchVC (length capacity : Int) (continued : Prop) : Prop :=
  (¬ length < capacity → exitVC length capacity) ∧ (¬ ¬ length < capacity → continued)

def unrolledVC : Nat → Int → Int → Prop
  | 0, length, capacity => branchVC length capacity (exitVC length capacity)
  | count + 1, length, capacity =>
      branchVC length capacity (stepVC length (fun stored => unrolledVC count stored capacity))

theorem step_valid (length capacity : Int) (typed : typedPair length capacity)
    (unfinished : ¬ ¬ length < capacity) (post : Int → Prop)
    (continued : ∀ stored, typedPair stored capacity → stored ≤ capacity → post stored) :
    stepVC length post := by
  intro value selected stored same
  have inside : 0 ≤ length + 1 ∧ length + 1 ≤ 10 := by
    dsimp only [typedPair] at typed
    omega
  have defined := selected.2.1 inside
  apply continued stored
  · exact ⟨by omega, typed.2⟩
  · omega

theorem unrolled_valid (count : Nat) (length capacity : Int)
    (typed : typedPair length capacity) (initial : length ≤ capacity) :
    unrolledVC count length capacity := by
  induction count generalizing length with
  | zero => exact ⟨fun _ => ⟨trivial, by omega⟩, fun _ => ⟨trivial, by omega⟩⟩
  | succ count ih =>
      exact ⟨fun _ => ⟨trivial, by omega⟩,
        fun unfinished => step_valid length capacity typed unfinished _ (ih ·)⟩

theorem compiled_valid (enabled : Bool) (values : Assignment (Key declaration Nat)) :
    (entryVC symbols (requirement enabled).payload (certificate enabled).formula).denote values := by
  cases enabled with
  | false =>
      unfold entryVC
      rw [unrolled_shape]
      with_unfolding_all
        change typedPair (values (.inl (.glob false))) (values (.inl (.glob true))) → True →
          values (.inl (.glob false)) ≤ values (.inl (.glob true)) →
          unrolledVC 2 (values (.inl (.glob false))) (values (.inl (.glob true)))
      exact fun typed _ initial => unrolled_valid 2 _ _ typed initial
  | true =>
      unfold entryVC
      rw [hinted_shape]
      with_unfolding_all
        change typedPair (values (.inl (.glob false))) (values (.inl (.glob true))) → True →
          values (.inl (.glob false)) ≤ values (.inl (.glob true)) →
          (values (.inl (.glob false)) - values (.inl (.glob true)) - 1 < 0 ∧
            ∀ length capacity : Int, typedPair length capacity →
              ((True → length - capacity - 1 < 0 →
                branchVC length capacity
                  (stepVC length (fun stored => stored - capacity - 1 < 0) ∧ exitVC length capacity)) ∧ True))
      intro _ _ initial
      refine ⟨by omega, ?_⟩
      intro length capacity typed
      refine ⟨fun _ invariant => ⟨fun _ => ⟨trivial, invariant⟩, ?_⟩, trivial⟩
      intro unfinished
      exact ⟨step_valid length capacity typed unfinished _ (fun _ _ preserved => by omega),
        trivial, invariant⟩

attribute [local irreducible] entryVC certificate

theorem function_checked (enabled : Bool) :
    (checkFunction (selectedProgram enabled) (SperrInv.leer declaration) (fun _ => none)
      loopBudget (selectedHint enabled) ()).toOption.isSome = true := by
  with_unfolding_all
    apply function_success
    · rfl
    · cases enabled <;> with_unfolding_all rfl
    · apply execution_success (selectedProgram enabled) (SperrInv.leer declaration) (fun _ => none)
        loopBudget (selectedHint enabled) () (by rfl) (obligations enabled) (by rfl)
        ((parameters (D := declaration) 4 0 []).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · cases enabled
        · change 4 ≤ 16384; decide
        · change 102 ≤ 16384; decide
      · rintro ⟨locals, member⟩
        cases locals
        exact environment_success_of_valid (D := declaration) (f := ()) (next := 0)
          (selectedProgram enabled) (SperrInv.leer declaration) symbols symbols_bounded (requiresPolicy (selectedProgram enabled) _)
          (fun _ => none) loopBudget (selectedHint enabled) (obligations enabled) (by rfl)
          (requirement enabled) (by rfl) (certificate enabled) (compiled_result enabled) (compiled_valid enabled)

theorem contracts_checked (enabled : Bool) :
    KontrakteGeprueftB (selectedProgram enabled) (SperrInv.leer declaration) [()]
      (fun _ => none) loopBudget (selectedHints enabled) = true := by
  obtain ⟨checks, checked⟩ := collect_success [()] (ContractDuties (selectedProgram enabled) (SperrInv.leer declaration))
    (fun f => do
      let hint ← loopHint (selectedHints enabled) f
      checkFunction (selectedProgram enabled) (SperrInv.leer declaration) (fun _ => none) loopBudget hint f) (by
        intro f
        cases f
        rw [selectedHint_result enabled]
        dsimp only [bind, Except.bind]
        exact success_of_isSome _ (function_checked enabled))
  unfold KontrakteGeprueftB checkContracts
  rw [checked]
  rfl

/-- This proof exercises the new contract compiler, including the owed
    invariant, rather than only deciding a handwritten arithmetic formula. -/
theorem unrolling_accepted_zeuge :
    KontrakteGeprueftB (loopProgram 2) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } = true :=
  contracts_checked false

theorem checked_hint_accepted_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } hints = true :=
  contracts_checked true

/-- The same large loop is refused when no hint is available. -/
theorem absent_hint_refused_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } = false := by
  decide +kernel

/-- A false hint fails its entry VC. -/
theorem false_hint_refused_zeuge :
    KontrakteGeprueftB (loopProgram 100) (SperrInv.leer declaration) [()]
      (fun _ => none) { expansion := 4 } (fun _ => some .fls) = false := by
  decide +kernel

end Gabbro.Grammatik.Vertraege.Pruefer.LoopWitness
