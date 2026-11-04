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

/-- A printed ending carries no fold work, also after a recursive end-block prefix. -/
theorem delabEnd_foldFree {V : Vertrag z.deklaration} {l : Bool} {Γ : Ctx}
    {Λ : List (Res z.deklaration)} (e : Endblock z.deklaration V l Γ Λ)
    {output : List SAnw × Option SEnde} (hd : delabEnd z V e = .ok output) (ctx : UCtx) :
    expandFoldEnd ctx output.2 = .ok ([], ctx, output.2) := by
  cases e with
  | ret value _ =>
    simp only [delabEnd] at hd
    cases hv : delabR z value with
    | error _ => simp only [hv, bind, Except.bind, reduceCtorEq] at hd
    | ok result =>
      simp only [hv, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      cases result with
      | none => rfl
      | some source =>
        simp only [expandFoldEnd, expandFoldValue_no_work ctx ctx.names.length source
          (delabR_foldFree value hv source rfl), foldCheckResult, List.isEmpty_nil,
          ↓reduceIte, bind, Except.bind, pure, Except.pure]
  | retWhy .. => simp only [delabEnd, Except.ok.injEq] at hd; subst hd; rfl
  | cons statement rest =>
    simp only [delabEnd] at hd
    cases hs : delabS z V statement with
    | error _ => simp only [hs, bind, Except.bind, reduceCtorEq] at hd
    | ok ss =>
      cases hr : delabEnd z V rest with
      | error _ => simp only [hs, hr, bind, Except.bind, reduceCtorEq] at hd
      | ok result =>
        obtain ⟨rs, ending⟩ := result
        simp only [hs, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
        exact delabEnd_foldFree rest hr ctx
  | bind value rest =>
    simp only [delabEnd] at hd
    cases hv : delabE z none value with
    | error _ => simp only [hv, bind, Except.bind, reduceCtorEq] at hd
    | ok source =>
      cases hr : delabEnd z V rest with
      | error _ => simp only [hv, hr, bind, Except.bind, reduceCtorEq] at hd
      | ok result =>
        obtain ⟨rs, ending⟩ := result
        simp only [hv, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
        exact delabEnd_foldFree rest hr ctx
  | bindCall _ args _ _ _ rest =>
    simp only [delabEnd] at hd
    cases ha : delabA z args with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sources =>
      cases hr : delabEnd z V rest with
      | error _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
      | ok result =>
        obtain ⟨rs, ending⟩ := result
        simp only [ha, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
        exact delabEnd_foldFree rest hr ctx
  | bindCallElse _ args _ _ _ err rest =>
    simp only [delabEnd] at hd
    cases ha : delabA z args with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sources =>
      cases he : delabEnd z V err with
      | error _ => simp only [ha, he, bind, Except.bind, reduceCtorEq] at hd
      | ok errorResult =>
        obtain ⟨es, errorEnding⟩ := errorResult
        cases hr : delabEnd z V rest with
        | error _ => simp only [ha, he, hr, bind, Except.bind, reduceCtorEq] at hd
        | ok result =>
          obtain ⟨rs, ending⟩ := result
          simp only [ha, he, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          exact delabEnd_foldFree rest hr ctx
  | regRead _ _ rest | awaits _ _ _ _ _ rest =>
    simp only [delabEnd] at hd
    cases hr : delabEnd z V rest with
    | error _ => simp only [hr, bind, Except.bind, reduceCtorEq] at hd
    | ok result =>
      obtain ⟨rs, ending⟩ := result
      simp only [hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
      exact delabEnd_foldFree rest hr ctx
  | bindCallInd pointer args _ _ _ rest =>
    simp only [delabEnd] at hd
    cases ha : delabA z args with
    | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
    | ok sources =>
      cases hr : delabEnd z V rest with
      | error _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
      | ok result =>
        obtain ⟨rs, ending⟩ := result
        cases pointer with
        | fnref .. | var .. =>
          simp only [ha, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          exact delabEnd_foldFree rest hr ctx
        | _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
  | _ => simp only [delabEnd, reduceCtorEq] at hd
termination_by sizeOf e
decreasing_by all_goals (simp_wf <;> omega)

end Gabbro.Grammatik.Gen.Text
