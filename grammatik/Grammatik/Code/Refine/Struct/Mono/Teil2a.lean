module

public import Grammatik.Code.Refine.Struct.Mono.Teil2

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}

theorem lowerNutz_mono (lay : Layout D) (cenv : List Reg) (W L i : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Gabbro.Grammatik.Ty}
      (nutz : Gabbro.Grammatik.NutzlastExpr D Γ Λ c) (r : Nat) (c0 : LR),
      lowerNutz lay cenv W L i nutz r = some c0 → r ≤ c0.2.2
  | _, _, _, .empty, r, c0, h => by
      simp only [lowerNutz, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | _, _, _, .val (τ := .int lo hi) e, r, c0, h => by
      simp only [lowerNutz] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hn : numCode lo hi W L i oe r1 with ⟨cn, on, r2⟩
      have m2 := numCode_mono (lo := lo) (hi := hi) (W := W) (L := L) (i := i) (oe := oe) (r := r1)
      rw [hn] at m2 h
      simp only [Option.some.injEq] at h
      subst h
      simp only at m1 m2 ⊢
      omega

end
end Gabbro.Code.Lower
