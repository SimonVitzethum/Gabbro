module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Fixtures
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

-- Force equation generation here, before a frontend witness first needs cbv.
#print equations Basic.statement
#print equations Basic.block
#print equations Basic.ending

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

/-- Integer parameters occupy one symbolic template each, without a product. -/
theorem specialization_product_zeuge :
    argumentSpecializations 100 [.int 0 10, .int 0 10] = 1 := by decide

/-- One branch returns its input; only the other reaches the twenty-case
    continuation. The early return is not multiplied by that continuation. -/
def conditionalReturn : Stmt declaration contract false [.int 1 11] [] [] :=
  .ite .tru (.cons (.ret (.val (.var .here)) (List.Perm.refl _)) .nil) .nil

theorem continuation_cost_zeuge :
    statementSpecializations increment false 128 100 20 conditionalReturn = 21 := rfl

/-- Wide constants use one fallback continuation instead of enumerating their type. -/
theorem wide_selection_cost_zeuge :
    selectionSpecializations 128 100
      (D := declaration) (Γ := []) (Λ := [])
      (.add (.widen (by decide) (by decide) (.lit 2) : Expr declaration [] [] (.int 0 1000000))
        (.lit 3)) = 1 := rfl

def writerContract : Vertrag declaration := { contract with schreibt := fun _ => true }

def storedSeven : Stmt declaration writerContract false [.int 0 10] [] [] :=
  .assignSlot () () (.widen (by decide) (by decide) (.lit 0))
    (.widen (by decide) (by decide) (.lit 7)) rfl
    (fun _ member => (List.not_mem_nil member).elim)

/-- A full-width parameter and a memory-dependent initializer. The explicit
    narrowing fallback remains part of the model's actual return value. -/
def u32Declaration : Deklaration :=
  { declaration with
    sigNr := fun _ =>
      { params := [.int 0 (2 ^ 32 - 1)], erg := some (.int 0 (2 ^ 32 - 1)), gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun _ => false
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible }

def u32Program : Programm u32Declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret (.val
    (.eng (.add (.var .here) (.glob false (fun _ member => (List.not_mem_nil member).elim)))
      0 (2 ^ 32 - 1) (.var .here))) (List.Perm.refl _)

def u32Invariants : InvariantFormula u32Program (u32Declaration.invs.filter (schuldet ())) :=
  (invariantFormula u32Program []).toOption.get (by rfl)

end Gabbro.Grammatik.Vertraege.Pruefer.Witness

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
