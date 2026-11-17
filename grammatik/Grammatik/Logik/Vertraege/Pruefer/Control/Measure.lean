module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Entry
public import Grammatik.Logik.Terminierung.Mass

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D}

/-- Symbolic natural tuples retain their actual evaluation, including toNat. -/
def measureTerms (symbols : SymEnv D Nat Γ)
    (terms : List (Σ hi : Int, {e : Expr D Γ Λ (.int 0 hi) // e.orte = []})) :
    Except Frag.Refusal { encoded : List (LTerm (Key D Nat)) //
      ∀ valuation world actual, symbols.Realizes valuation world actual →
        encoded.map (fun term => term.denote (values valuation world)) =
          terms.map (fun term : Σ hi : Int, {e : Expr D Γ Λ (.int 0 hi) // e.orte = []} =>
            (((eval world term.2.1 world actual : Zahl 0 term.1).n.toNat : Nat) : Int)) } :=
  match terms with
  | [] => .ok ⟨[], fun _ _ _ _ => rfl⟩
  | term :: terms => do
      let head ← Invarianten.Frag.Symbolic.translate term.2.1 symbols
      let tail ← measureTerms symbols terms
      return ⟨head.payload :: tail.val, fun valuation world actual realized => by
        have same : head.payload.denote (values valuation world) = (eval world term.2.1 world actual).n :=
          head.correct valuation world actual realized
        exact congr (congrArg List.cons
          (same.trans (Int.toNat_of_nonneg (eval world term.2.1 world actual).lo_le).symm))
          (tail.property valuation world actual realized)⟩

def lexFormula : List (LTerm α) → List (LTerm α) → LProp α
  | left :: lefts, right :: rights => .or (.lt left right) (.and (.eq left right) (lexFormula lefts rights))
  | _, _ => .fls

theorem lexFormula_denote [DecidableEq α] (left right : List (LTerm α)) (valuation : Assignment α)
    (actual expected : List Nat)
    (lefts : left.map (fun term => term.denote valuation) = actual.map (fun n : Nat => (n : Int)))
    (rights : right.map (fun term => term.denote valuation) = expected.map (fun n : Nat => (n : Int))) :
    (lexFormula left right).denote valuation ↔ lexLt actual expected = true := by
  induction left generalizing actual right expected with
  | nil => cases actual <;> cases right <;> cases expected <;> simp_all [lexFormula, lexLt, LProp.denote]
  | cons head tail ih =>
      cases actual with
      | nil => cases lefts
      | cons value rest =>
          cases right with
          | nil => cases expected <;> simp_all [lexFormula, lexLt, LProp.denote]
          | cons other others =>
              cases expected with
              | nil => cases rights
              | cons next remaining =>
                  obtain ⟨h, t⟩ := List.cons.inj lefts
                  obtain ⟨o, r⟩ := List.cons.inj rights
                  simp only [lexFormula, LProp.denote, lexLt, Bool.or_eq_true, Bool.and_eq_true,
                    decide_eq_true_eq, beq_iff_eq, h, o, ih _ _ _ t r]
                  constructor <;> intro valid <;> rcases valid with less | ⟨same, later⟩
                  · exact Or.inl (by omega)
                  · exact Or.inr ⟨by omega, later⟩
                  · exact Or.inl (by omega)
                  · exact Or.inr ⟨by omega, later⟩

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
