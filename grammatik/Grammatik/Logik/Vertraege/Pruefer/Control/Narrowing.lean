module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Flow

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

def integerTerm? : SymValue D Nat (.int lo hi) → Option (LTerm Nat)
  | .known value => some (.konst value.n)
  | .integer term => some term
  | .unobserved => none

theorem integerTerm?_bounded (symbol : SymValue D Nat (.int lo hi)) (bounded : symbol.Bounded next)
    (found : integerTerm? symbol = some term) : ∀ key ∈ VC.termKeys term, key < next := by
  cases symbol with
  | known value => cases found; intro key impossible; cases impossible
  | integer term => cases found; exact bounded
  | unobserved => cases found

theorem integerTerm?_realizes (symbol : SymValue D Nat (.int lo hi)) (valuation : Assignment Nat)
    (world : World D) (actual : Zahl lo hi) (realized : symbol.Realizes valuation world actual)
    (found : integerTerm? symbol = some term) : term.denote valuation = actual.n := by
  cases symbol with
  | known value => cases found; change value = actual at realized; rw [← realized]; rfl
  | integer term => cases found; exact realized
  | unobserved => cases found

def narrowingCondition {context : Context A next} (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (expression : Expr D Γ Λ (.int lo hi)) (low high : Int)
    (success : Env D Γ → Zahl low high → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (failure : Env D Γ → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : SelectCompiler context symbols (.int low high) success)
    (compileFailure : Except Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual → failure actual item runtime world))) :
    Except Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      symbols.Realizes valuation world actual →
      let value := eval world expression world actual
      if fits : low ≤ value.n ∧ value.n ≤ high then success actual ⟨value.n, fits.1, fits.2⟩ item runtime world
      else failure actual item runtime world)) := do
  let failed ← compileFailure
  selectValue symbols bounded expression
    (fun actual value item runtime world =>
      if fits : low ≤ value.n ∧ value.n ≤ high then success actual ⟨value.n, fits.1, fits.2⟩ item runtime world
      else failure actual item runtime world)
    (fun more larger symbol valueBounded =>
      match found : integerTerm? symbol with
      | none => .error (.unsupported "narrowing needs an observed integer value")
      | some integral => do
        let narrowed : SymValue D Nat (.int low high) := .integer integral
        let yes ← compile more larger narrowed (integerTerm?_bounded symbol valueBounded found)
        let no := failed.weaken larger
        let term := renameTerm Sum.inr integral
        let guard : LProp (Key D Nat) := .and (.le (.konst low) term) (.le term (.konst high))
        return {
          formula := .and (.imp guard yes.formula) (.imp (.not guard) no.formula)
          sound := fun valuation item present runtime world valid actual realized value selected => by
            have number := integerTerm?_realizes symbol valuation world value selected found
            have termValue : term.denote (values valuation world) = value.n := by
              rw [renameTerm_denote]
              exact number
            have condition : guard.denote (values valuation world) ↔ low ≤ value.n ∧ value.n ≤ high := by
              change (low ≤ term.denote _ ∧ term.denote _ ≤ high) ↔ _
              rw [termValue]
            by_cases fits : low ≤ value.n ∧ value.n ≤ high
            · simp only [dif_pos fits]
              exact yes.sound valuation item present runtime world (valid.1 (condition.mpr fits)) actual realized
                ⟨value.n, fits.1, fits.2⟩ number
            · simp only [dif_neg fits]
              exact no.sound valuation item present runtime world (valid.2 (fun present => fits (condition.mp present))) actual realized })

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
