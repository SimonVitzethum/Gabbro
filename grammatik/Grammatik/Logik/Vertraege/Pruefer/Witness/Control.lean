module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Fixtures
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

/-- Both arms return x+1; only the success arm receives the narrowed local. -/
def narrowedIncrement : Programm declaration :=
  { increment with
    rumpf := fun _ =>
      .narrow (.var .here) 0 5
        (.ret (.val (.add (.var .here) (.lit 1))) (List.Perm.refl _))
        (.ret (.val (.widen (by decide) (by decide)
          (.add (.var .here) (.lit 1)))) (List.Perm.refl _)) }

def scopedIncrement : Programm declaration :=
  { increment with
    rumpf := fun _ =>
      .retScoped (.val (.add (.var .here) (.lit 1)))
        { scopes := [], genau := List.Perm.refl _ } }

theorem narrowedIncrement_zeuge :
    KontrakteGeprueftB narrowedIncrement (SperrInv.leer declaration) [()] = true := by
  decide +kernel

theorem scopedIncrement_zeuge :
    KontrakteGeprueftB scopedIncrement (SperrInv.leer declaration) [()] = true := by
  decide +kernel

theorem localGlobalAccess (name : declaration.Glob) : gdarf declaration name [] :=
  fun _ member => (List.not_mem_nil member).elim

/-- The newly admitted conditional shape contains a real memory observation
    and two different integer results; it is not literal truth. -/
def conditionalPost : Expr declaration [] [] .bool :=
  .eq (.eng (.add (.glob false (localGlobalAccess false)) (.lit 1))
      0 10 (.glob false (localGlobalAccess false))) (.lit 3)

theorem currentOnly_zeuge : (currentOnly conditionalPost).toOption.isSome = true := by
  decide +kernel

/-- A retry mutates a real local on every pass and takes its overflow arm.
    Its totality proof covers all bounds, not the seven sampled passes. -/
def retryStep (next : World declaration) (locals : Env declaration [.int 0 10]) :
    Ausgang contract true [.int 0 10] :=
  .ok next (locals.set .here ⟨3, by decide, by decide⟩)

def retryTest (next : World declaration) (_ : Env declaration [.int 0 10]) := (next, false)

def retryOverflow (next : World declaration) (locals : Env declaration [.int 0 10]) :
    Ausgang contract false [.int 0 10] := .ok next locals

theorem retry_safe_zeuge :
    Basic.StatementResult (retryLauf retryStep retryTest retryOverflow
      7 world arguments) :=
  Basic.retry_safe retryStep retryTest retryOverflow
    (fun _ _ => trivial) (fun _ _ => trivial) 7 world arguments

/-- Two successive 11-way bindings exceed a 100-specialization budget.
    Saturation stops at 101, without constructing either continuation family. -/
theorem specialization_product_zeuge :
    argumentSpecializations 100 [.int 0 10, .int 0 10] = 101 := by decide

/-- One branch returns its input; only the other reaches the twenty-case
    continuation. The early return is not multiplied by that continuation. -/
def conditionalReturn : Stmt declaration contract false [.int 1 11] [] [] :=
  .ite .tru (.cons (.ret (.val (.var .here)) (List.Perm.refl _)) .nil) .nil

theorem continuation_cost_zeuge : statementSpecializations 100 20 conditionalReturn = 21 := rfl

def writerContract : Vertrag declaration := { contract with schreibt := fun _ => true }

def storedSeven : Stmt declaration writerContract false [.int 0 10] [] [] :=
  .assignSlot () () (.widen (by decide) (by decide) (.lit 0))
    (.widen (by decide) (by decide) (.lit 7)) rfl
    (fun _ member => (List.not_mem_nil member).elim)

def storeGoals : Goals declaration writerContract [.int 0 10] where
  normal := fun _ => .ok (lower (.eq (.var (.slot () () 0)) (.konst 7)))
  escape := fun _ => .ok .tru
  again := fun _ => .ok .tru
  returned := fun _ => .ok .tru
  reason := .tru

def storeCondition :=
  (leafCondition (S := SperrInv.leer declaration) (requiresPolicy increment)
    128 storedSeven arguments storeGoals).toOption.get (by decide +kernel)

/-- The actual store WP proves the subsequent cell-equals-seven obligation
    for every entry assignment, including entries where that cell was not 7. -/
theorem stored_seven_zeuge :
    decideB (close (writerMatrix .tru .tru storeCondition.formula))
      (close_closed (writerMatrix .tru .tru storeCondition.formula)) = true := by
  decide +kernel

def wideArguments : Env declaration [.int 0 (2 ^ 64 - 1)] :=
  .cons ⟨7, by decide, by decide⟩ .nil

/-- Returning a decoded 64-bit local compiles with a one-case budget; its
    declared interval is never materialized or split into result branches. -/
theorem return_local_without_enumeration_zeuge :
    (returnCondition (program := increment) (S := SperrInv.leer declaration) (Λ := [])
      1 (.val (.var .here)) wideArguments (fun _ => .ok .tru)).toOption.isSome = true ∧
    (returnCondition (program := increment) (S := SperrInv.leer declaration) (Λ := [])
      1 (.val (.widen (by decide) (by decide) (.var .here)) :
        ErgExpr declaration [.int 0 (2 ^ 64 - 1)] [] (some (.int 0 (2 ^ 65 - 1))))
      wideArguments (fun _ => .ok .tru)).toOption.isSome = true := by
  constructor <;> rfl

end Gabbro.Grammatik.Vertraege.Pruefer.Witness

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
