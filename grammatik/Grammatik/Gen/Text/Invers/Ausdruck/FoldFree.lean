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
  have go : ∀ n, ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} {kopf : Option Nat}
      (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ s,
      delabE z kopf e = .ok s → needsFoldExpansion s = false := by
    intro n
    induction n with
    | zero => intro _ _ _ _ _ hn; omega
    | succ n ih =>
      intro Γ Λ τ kopf e hn s hd
      cases e with
      | lit m =>
        simp only [delabE, Except.ok.injEq] at hd; subst hd
        unfold zahlE
        split <;> simp only [needsFoldExpansion]
      | tru | fls | glob _ _ | fnref _ _ _ | oldG _ _ | why _ _ | none _ =>
        simp only [delabE, Except.ok.injEq] at hd; subst hd
        simp only [needsFoldExpansion, needsFoldExpansionList]
      | var x =>
        simp only [delabE, Except.ok.injEq] at hd; subst hd
        split <;> simp only [needsFoldExpansion]
      | widen _ _ e =>
        simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn
        exact ih e (by omega) s hd
      | add a b | sub a b | mul a b | div _ _ a b | rem _ _ a b
      | sdiv _ a b | srem _ a b | band _ _ a b | bor _ _ _ _ _ a b
      | bxor _ _ _ _ _ a b | shl _ _ _ _ _ a b | shr _ _ _ _ _ a b
      | lt a b | le a b | eq a b | and a b | or a b =>
        simp only [Expr.add.sizeOf_spec, Expr.sub.sizeOf_spec, Expr.mul.sizeOf_spec,
          Expr.div.sizeOf_spec, Expr.rem.sizeOf_spec, Expr.sdiv.sizeOf_spec, Expr.srem.sizeOf_spec,
          Expr.band.sizeOf_spec, Expr.bor.sizeOf_spec, Expr.bxor.sizeOf_spec, Expr.shl.sizeOf_spec,
          Expr.shr.sizeOf_spec, Expr.lt.sizeOf_spec, Expr.le.sizeOf_spec, Expr.eq.sizeOf_spec,
          Expr.and.sizeOf_spec, Expr.or.sizeOf_spec] at hn
        simp only [delabE] at hd
        cases ha : delabE z kopf a with
        | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
        | ok sa =>
          cases hb : delabE z kopf b with
          | error _ => simp only [ha, hb, bind, Except.bind, reduceCtorEq] at hd
          | ok sb =>
            simp only [ha, hb, bind, Except.bind, Except.ok.injEq] at hd; subst hd
            simp only [needsFoldExpansion, ih a (by omega) _ ha, ih b (by omega) _ hb, Bool.or_self]
      | slot t f i _ =>
        simp only [Expr.slot.sizeOf_spec] at hn
        simp only [delabE] at hd
        cases hi : delabE z kopf i with
        | error _ => simp only [hi, bind, Except.bind, reduceCtorEq] at hd
        | ok si =>
          simp only [hi, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          simp only [needsFoldExpansion, ih i (by omega) _ hi, Bool.or_self]
      | neg a =>
        simp only [Expr.neg.sizeOf_spec] at hn
        simp only [delabE] at hd
        cases ha : delabE z kopf a with
        | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
        | ok sa =>
          have hf := ih a (by omega) _ ha
          simp only [ha, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          cases sa <;> simp only [needsFoldExpansion] at hf ⊢ <;> exact hf
      | not a | some a =>
        simp only [Expr.not.sizeOf_spec, Expr.some.sizeOf_spec] at hn
        simp only [delabE] at hd
        cases ha : delabE z kopf a with
        | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
        | ok sa =>
          simp only [ha, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          simp only [needsFoldExpansion, needsFoldExpansionList, ih a (by omega) _ ha, Bool.or_self]
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
          all_goals
            subst hd
            simp only [needsFoldExpansion, isFold]
      | forallSlots t body _ | existsSlots t body _ =>
        simp only [delabE] at hd
        cases hb : delabE z kopf body with
        | error _ => simp only [hb, bind, Except.bind, reduceCtorEq] at hd
        | ok sb =>
          simp only [hb, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          simp only [needsFoldExpansion, isFold]
      | _ => simp only [delabE, reduceCtorEq] at hd
  exact go (sizeOf e + 1) e (by omega) s hd

theorem delabA_foldFree {Γ : Ctx} {Λ : List (Res z.deklaration)} {τs : List Ty}
    (args : Args z.deklaration Γ Λ τs) {ss : List SExpr} (hd : delabA z args = .ok ss) :
    needsFoldExpansionList ss = false := by
  have go : ∀ types, ∀ (values : Args z.deklaration Γ Λ types) sources,
      delabA z values = .ok sources → needsFoldExpansionList sources = false := by
    intro types
    induction types with
    | nil =>
      intro values sources h
      cases values
      simp only [delabA, Except.ok.injEq] at h; subst h; rfl
    | cons ty types ih =>
      intro values sources h
      cases values with
      | cons e rest =>
        simp only [delabA] at h
        cases he : delabE z none e with
        | error _ => simp only [he, bind, Except.bind, reduceCtorEq] at h
        | ok se =>
          cases hr : delabA z rest with
          | error _ => simp only [he, hr, bind, Except.bind, reduceCtorEq] at h
          | ok sr =>
            simp only [he, hr, bind, Except.bind, Except.ok.injEq] at h; subst h
            simp only [needsFoldExpansionList, delabE_foldFree e he, ih rest sr hr, Bool.or_self]
  exact go τs args ss hd

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
  have go : ∀ n, ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)}
      (e : Endblock z.deklaration V l Γ Λ), sizeOf e < n →
      ∀ (result : List SAnw × Option SEnde) (ctx : UCtx),
      delabEnd z V e = .ok result → expandFoldEnd ctx result.2 = .ok ([], ctx, result.2) := by
    intro n
    induction n with
    | zero => intro _ _ _ _ hn; omega
    | succ n ih =>
      intro l Γ Λ e hn output ctx hd
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
      | retWhy _ _ =>
        simp only [delabEnd, Except.ok.injEq] at hd
        subst hd
        rfl
      | cons statement rest =>
        simp only [Endblock.cons.sizeOf_spec] at hn
        simp only [delabEnd] at hd
        cases hs : delabS z V statement with
        | error _ => simp only [hs, bind, Except.bind, reduceCtorEq] at hd
        | ok ss =>
          cases hr : delabEnd z V rest with
          | error _ => simp only [hs, hr, bind, Except.bind, reduceCtorEq] at hd
          | ok result =>
            obtain ⟨rs, ending⟩ := result
            simp only [hs, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
            exact ih rest (by omega) _ ctx hr
      | bind value rest =>
        simp only [Endblock.bind.sizeOf_spec] at hn
        simp only [delabEnd] at hd
        cases hv : delabE z none value with
        | error _ => simp only [hv, bind, Except.bind, reduceCtorEq] at hd
        | ok source =>
          cases hr : delabEnd z V rest with
          | error _ => simp only [hv, hr, bind, Except.bind, reduceCtorEq] at hd
          | ok result =>
            obtain ⟨rs, ending⟩ := result
            simp only [hv, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
            exact ih rest (by omega) _ ctx hr
      | bindCall _ args _ _ _ rest =>
        simp only [Endblock.bindCall.sizeOf_spec] at hn
        simp only [delabEnd] at hd
        cases ha : delabA z args with
        | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
        | ok sources =>
          cases hr : delabEnd z V rest with
          | error _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
          | ok result =>
            obtain ⟨rs, ending⟩ := result
            simp only [ha, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
            exact ih rest (by omega) _ ctx hr
      | bindCallElse _ args _ _ _ err rest =>
        simp only [Endblock.bindCallElse.sizeOf_spec] at hn
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
              exact ih rest (by omega) _ ctx hr
      | regRead _ _ rest | awaits _ _ _ _ _ rest =>
        simp only [Endblock.regRead.sizeOf_spec, Endblock.awaits.sizeOf_spec] at hn
        simp only [delabEnd] at hd
        cases hr : delabEnd z V rest with
        | error _ => simp only [hr, bind, Except.bind, reduceCtorEq] at hd
        | ok result =>
          obtain ⟨rs, ending⟩ := result
          simp only [hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
          exact ih rest (by omega) _ ctx hr
      | bindCallInd pointer args _ _ _ rest =>
        simp only [Endblock.bindCallInd.sizeOf_spec] at hn
        simp only [delabEnd] at hd
        cases ha : delabA z args with
        | error _ => simp only [ha, bind, Except.bind, reduceCtorEq] at hd
        | ok sources =>
          cases hr : delabEnd z V rest with
          | error _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
          | ok result =>
            obtain ⟨rs, ending⟩ := result
            cases pointer with
            | fnref _ _ _ | var _ =>
              simp only [ha, hr, bind, Except.bind, Except.ok.injEq] at hd; subst hd
              exact ih rest (by omega) _ ctx hr
            | _ => simp only [ha, hr, bind, Except.bind, reduceCtorEq] at hd
      | _ => simp only [delabEnd, reduceCtorEq] at hd
  exact go (sizeOf e + 1) e (by omega) output ctx hd

end Gabbro.Grammatik.Gen.Text
