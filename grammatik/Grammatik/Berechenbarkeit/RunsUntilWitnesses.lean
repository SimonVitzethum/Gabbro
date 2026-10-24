/-
  File:      Grammatik/Berechenbarkeit/RunsUntilWitnesses.lean
  Subject:   Real typed Gabbro witnesses of conditional termination and its limits.

  A guard initially false becomes true after an actual variable assignment. A second
  witness writes the shared reference table under its declared lock and exits on the
  next read. Negative probes keep unsatisfied guards and budget exhaustion distinct
  from successful termination. No oracle performs any computation for these programs.
-/
import Grammatik.Berechenbarkeit.RunsUntil
import Grammatik.Zielsatz.Eigenschaften.BudgetZeuge
import Grammatik.Korpus.Referenz.ReferenzB

namespace Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses

open Gabbro.Grammatik Gabbro.Grammatik.Terminierung
open Gabbro.Grammatik.Zielsatz.BudgetZeuge

abbrev BoolV : Vertrag bD := vertragVon bD ()

/-- The body changes the actual environment from false to true. -/
def boolBody : Block bD BoolV true [.bool] [] [] :=
  .cons (.assignVar .here Expr.tru) .nil

def boolLoop : Stmt bD BoolV false [.bool] [] [] :=
  runsUntil () Expr.tru (.var .here) boolBody

def boolStart : Env bD [.bool] := .cons false .nil
def boolEnd : Env bD [.bool] := .cons true .nil

/-- Guard false, one real assignment, guard true: two guard checks, one body pass. -/
theorem assignment_zeuge (σ : World bD) :
    execStmt bO 2 keinRuf boolLoop σ boolStart = .ok σ boolEnd := rfl

/-- One unit of fuel does NOT suffice, although it performs the assignment. -/
theorem insufficient_budget_zeuge (σ : World bD) :
    execStmt bO 1 keinRuf boolLoop σ boolStart = .hardware (.fortschritt ()) := rfl

/-- Normal completion is stable for every larger budget, by the generic theorem. -/
theorem larger_budget_zeuge (σ : World bD) (p : Nat) :
    execStmt bO (p + 2) keinRuf boolLoop σ boolStart = .ok σ boolEnd := by
  obtain ⟨n, hn, ht⟩ := (runsUntil_iff bO 2 keinRuf () Expr.tru (.var .here) boolBody
    σ boolStart σ boolEnd).mp (assignment_zeuge σ)
  exact ht.run () (p := p + 2) (by omega)

theorem rank_zeuge (σ : World bD) :
    ∃ σ' ρ', execStmt bO 2 keinRuf boolLoop σ boolStart = .ok σ' ρ' := by
  apply runsUntil_of_rank bO 2 keinRuf () Expr.tru (.var .here) boolBody
    (fun _ ρ => if wahr? (ρ.get (.here : Var [.bool] .bool)) = true then 0 else 1)
    ?_ ?_ σ boolStart (by decide)
  · intro σ ρ; rfl
  · intro σ ρ
    dsimp only
    intro hc
    cases ρ with
    | cons b ρ =>
      cases ρ
      cases b with
      | false => exact ⟨σ, boolEnd, Or.inl rfl, by decide⟩
      | true => cases hc

/-- A permanently false guard, with a real assignment in its body. -/
def falseLoop : Stmt bD BoolV false [.bool] [] [] :=
  runsUntil () Expr.tru Expr.fls boolBody

theorem false_guard_budget (σ : World bD) : ∀ p ρ,
    execStmt bO p keinRuf falseLoop σ ρ = .hardware (.fortschritt ())
  | 0, _ => rfl
  | p + 1, .cons _ .nil => false_guard_budget σ p boolEnd

/-- No amount of fuel makes a false guard into a normal return. -/
theorem false_guard_never_zeuge (σ : World bD) :
    ¬ ∃ p σ' ρ', execStmt bO p keinRuf falseLoop σ boolStart = .ok σ' ρ' := by
  rintro ⟨p, σ', ρ', h⟩
  rw [false_guard_budget σ p boolStart] at h
  cases h

/-- The complete function, with a bound local variable and its proper return. -/
def boolFunction (condition : Expr bD [.bool] [] .bool) :
    Endblock bD BoolV false [] [] :=
  .bind Expr.fls (.cons (runsUntil () Expr.tru condition boolBody) (.ret .empty (List.Perm.refl _)))

def boolProgram (condition : Expr bD [.bool] [] .bool) : Programm bD :=
  { bP with rumpf := fun _ => boolFunction condition }

/-- Both terminating and nonterminating guarded loops have the conditional class. -/
theorem conditional_classes_zeuge :
    klasse (boolProgram (.var .here)) [()] (fun _ => false) () = .bedingt ∧
    klasse (boolProgram Expr.fls) [()] (fun _ => false) () = .bedingt := by decide

abbrev Held : List (Res refD) := [.held ()]
abbrev MemoryV : Vertrag refD := vertragVon refD refEin

def memoryCondition : Expr refD (refD.params refEin) Held .bool :=
  .eq (.slot () () refIdxEin refDarf) refHundert

def memoryBody : Block refD MemoryV true (refD.params refEin) Held Held :=
  .cons (.assignSlot () () refIdxEin refHundert (refEin_schreibt ()) refDarf) .nil

def memoryLoop : Stmt refD MemoryV false (refD.params refEin) Held Held :=
  runsUntil () Expr.tru memoryCondition memoryBody

def memoryStart : World refD := refSp0.welt [.nimmt () []]

/-- A nondegenerate memory witness: a real table cell changes from 0 to 100, and the
    logical guard observes that write on the next pass. -/
theorem memory_zeuge : ∃ σ',
    execStmt refO 2 keinRuf memoryLoop memoryStart refRho7 = .ok σ' refRho7 ∧
    (memoryStart.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 100 := by
  refine ⟨_, rfl, rfl, rfl⟩

/-- The generic exit theorem applies to the writing witness, not just to a toy step function. -/
theorem memory_guard_zeuge : ∃ σ',
    execStmt refO 2 keinRuf memoryLoop memoryStart refRho7 = .ok σ' refRho7 ∧
      wahr? (eval σ' memoryCondition σ' refRho7) = true := by
  obtain ⟨σ', hs, _, _⟩ := memory_zeuge
  refine ⟨σ', hs, runsUntil_post refO 2 keinRuf () Expr.tru memoryCondition memoryBody ?_ hs⟩
  intro σ ρ σ1 ρ1 h
  cases h

end Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses
