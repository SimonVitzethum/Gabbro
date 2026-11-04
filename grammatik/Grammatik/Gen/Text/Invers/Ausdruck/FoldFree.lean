module

public import Grammatik.Gen.Text.Delab.Teil1
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
variable {z : Spez}

/-- Every successful expression spelling is outside the fold-expansion traversal. -/
theorem delabE_foldFree {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} {kopf : Option Nat}
    (e : Expr z.deklaration Γ Λ τ) {s : SExpr} (hd : delabE z kopf e = .ok s) :
    needsFoldExpansion s = false := by
  cases e with
  | lit m =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    unfold zahlE
    split <;> simp only [needsFoldExpansion]
  | tru | fls | glob .. | fnref .. | oldG .. | why .. | none .. =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [needsFoldExpansion, needsFoldExpansionList]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    split <;> simp only [needsFoldExpansion]
  | widen _ _ e => exact delabE_foldFree e hd
  | add a b | sub a b | mul a b | div _ _ a b | rem _ _ a b
  | sdiv _ a b | srem _ a b | band _ _ a b | bor _ _ _ _ _ a b
  | bxor _ _ _ _ _ a b | shl _ _ _ _ _ a b | shr _ _ _ _ _ a b
  | lt a b | le a b | eq a b | and a b | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sa =>
      cases hb : delabE z kopf b with
      | error _ => simp only [ha, hb, bind, Except.bind, reduceCtorEq] at hd
      | ok sb =>
        simp only [ha, hb, bind, Except.bind, Except.ok.injEq] at hd; subst hd
        simp only [needsFoldExpansion, delabE_foldFree a ha, delabE_foldFree b hb, Bool.or_self]
  | slot t f i _ =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi, bind, Except.bind, reduceCtorEq] at hd
    | ok si =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      simp only [needsFoldExpansion, delabE_foldFree i hi, Bool.or_self]
  | neg a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sa =>
      have hf := delabE_foldFree a ha
      simp only [ha, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      cases sa <;> simp only [needsFoldExpansion] at hf ⊢ <;> exact hf
  | not a | some a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sa =>
      simp only [ha, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      simp only [needsFoldExpansion, needsFoldExpansionList, delabE_foldFree a ha, Bool.or_self]
  | oldS t f i _ =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi, bind, Except.bind, reduceCtorEq] at hd
    | ok si =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      simp only [needsFoldExpansion]
  | istSome a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sa =>
      cases sa <;> simp only [ha, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
      all_goals subst hd; simp only [needsFoldExpansion, isFold]
  | forallSlots t body _ | existsSlots t body _ =>
    simp only [delabE] at hd
    cases hb : delabE z kopf body with
    | error _ => simp only [hb, bind, Except.bind, reduceCtorEq] at hd
    | ok sb =>
      simp only [hb, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      simp only [needsFoldExpansion, isFold]
  | _ => simp only [delabE, reduceCtorEq] at hd
termination_by sizeOf e
decreasing_by all_goals (simp_wf <;> omega)

theorem delabA_foldFree {Γ : Ctx} {Λ : List (Res z.deklaration)} {τs : List Ty}
    (args : Args z.deklaration Γ Λ τs) {ss : List SExpr} (hd : delabA z args = .ok ss) :
    needsFoldExpansionList ss = false := by
  cases args with
  | nil => simp only [delabA, Except.ok.injEq] at hd; subst hd; rfl
  | cons e rest =>
    simp only [delabA] at hd
    cases he : delabE z none e with
    | error _ => simp only [he, bind, Except.bind, reduceCtorEq] at hd
    | ok se =>
      cases hr : delabA z rest with
      | error _ => simp only [he, hr, bind, Except.bind, reduceCtorEq] at hd
      | ok sr =>
        simp only [he, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
        simp only [needsFoldExpansionList, delabE_foldFree e he, delabA_foldFree rest hr, Bool.or_self]
termination_by sizeOf args
decreasing_by all_goals (simp_wf <;> omega)

theorem delabR_foldFree {Γ : Ctx} {Λ : List (Res z.deklaration)} {o : Option Ty}
    (e : ErgExpr z.deklaration Γ Λ o) {s : Option SExpr} (hd : delabR z e = .ok s) :
    ∀ value, s = some value → needsFoldExpansion value = false := by
  cases e with
  | empty => simp only [delabR, Except.ok.injEq] at hd; subst hd; intro _ h; cases h
  | val e =>
    cases he : delabE z none e with
    | error _ => simp only [delabR, he, bind, Except.bind, reduceCtorEq] at hd
    | ok se =>
      simp only [delabR, he, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      intro value h
      cases h
      exact delabE_foldFree e he

end Gabbro.Grammatik.Gen.Text
