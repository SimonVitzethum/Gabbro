module

public import Grammatik.Code.Lower.Stmt
public import Grammatik.Code.Refine.Struct.Mono.Teil2
public import Grammatik.Code.Refine.Struct.Mono.Teil2a

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}

theorem lowerArgs_mono (lay : Layout D) (cenv : List Reg) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List GTy} (args : Args D Γ Λ τs) (r : Nat)
      (c : List Instr × List Opd × Nat), lowerArgs lay cenv args r = some c → r ≤ c.2.2
  | _, _, _, .nil, r, c, h => by
      simp only [lowerArgs, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | _, _, _, .cons e rest, r, c, h => by
      simp only [lowerArgs] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hr : lowerArgs lay cenv rest r1 with _ | ⟨cr, os, r2⟩
      · simp only [hr, reduceCtorEq] at h
      have m2 := lowerArgs_mono lay cenv rest r1 _ hr
      simp only [hr, Option.some.injEq] at h
      subst h
      simp only at m1 m2 ⊢
      omega

end Gabbro.Code.Lower
