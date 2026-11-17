module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

variable {D : Deklaration}

/-- A defining relation for a selected scalar, retaining narrowing and
    conditional arms. Unsupported leaves conservatively contribute truth. -/
def evaluationRelation (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ)
    (target : LTerm (Key D Nat)) :
    { formula : LProp (Key D Nat) // ∀ valuation world actual,
      symbols.Realizes valuation world actual →
      target.denote (values valuation world) = Frag.scalarValue τ (eval world expression world actual) →
      formula.denote (values valuation world) } :=
  match expression with
  | .eng body low high fallback =>
      match translate body symbols with
      | .error _ => ⟨.tru, fun _ _ _ _ _ => trivial⟩
      | .ok source =>
          let other := evaluationRelation fallback symbols target
          let guard : LProp (Key D Nat) :=
            .and (.le (.konst low) source.payload) (.le source.payload (.konst high))
          ⟨.and (.imp guard (.eq target source.payload)) (.imp (.not guard) other.val),
            fun valuation world actual realized same => by
              have correct : guard.denote (values valuation world) ↔
                  low ≤ (eval world body world actual).n ∧ (eval world body world actual).n ≤ high := by
                change (low ≤ source.payload.denote _ ∧ source.payload.denote _ ≤ high) ↔ _
                rw [source.correct valuation world actual realized]
              constructor
              · intro selected
                have fits := correct.mp selected
                have evaluated : eval world (.eng body low high fallback) world actual =
                    (⟨(eval world body world actual).n, fits.1, fits.2⟩ : Zahl low high) := dif_pos fits
                exact same.trans ((congrArg Zahl.n evaluated).trans
                  (source.correct valuation world actual realized).symm)
              · intro absent
                have fits : ¬ (low ≤ (eval world body world actual).n ∧
                    (eval world body world actual).n ≤ high) := fun fits => absent (correct.mpr fits)
                have evaluated : eval world (.eng body low high fallback) world actual =
                    eval world fallback world actual := dif_neg fits
                exact other.property valuation world actual realized (same.trans (congrArg Zahl.n evaluated))⟩
  | .wenn test yes no =>
      match translate test symbols with
      | .error _ => ⟨.tru, fun _ _ _ _ _ => trivial⟩
      | .ok guard =>
          let positive := evaluationRelation yes symbols target
          let negative := evaluationRelation no symbols target
          ⟨.and (.imp guard.payload positive.val) (.imp (.not guard.payload) negative.val),
            fun valuation world actual realized same => by
              cases tested : eval world test world actual with
              | true =>
                  constructor
                  · intro _
                    apply positive.property valuation world actual realized
                    simpa only [eval, tested, wahr?, ↓reduceIte] using same
                  · intro absent
                    exact False.elim (absent ((guard.bool_iff valuation world actual realized).mp tested))
              | false =>
                  constructor
                  · intro selected
                    have impossible := (guard.bool_iff valuation world actual realized).mpr selected
                    rw [tested] at impossible
                    cases impossible
                  · intro _
                    apply negative.property valuation world actual realized
                    simpa only [eval, tested, wahr?, Bool.false_eq_true, ↓reduceIte] using same⟩
  | expression =>
      match τ, expression with
      | .int _ _, expression =>
          match translate expression symbols with
          | .error _ => ⟨.tru, fun _ _ _ _ _ => trivial⟩
          | .ok source => ⟨.eq target source.payload, fun valuation world actual realized same =>
              same.trans (source.correct valuation world actual realized).symm⟩
      | _, _ => ⟨.tru, fun _ _ _ _ _ => trivial⟩
termination_by structural expression

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
