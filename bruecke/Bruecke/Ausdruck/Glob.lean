module

public import Bruecke.Kodierung.Glob
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values

@[expose] public section

/-! # Scalar and Boolean static-read simulation -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The static analogue of `lowTabRead_sim`. There is no index expression or parameter
    lookup, so neither `fn`, `sh` nor `LRel` is needed. Guard possession is already a
    premise of a successful `lowGlobSide`, just as it is for `lowTabRead`. -/
theorem lowGlobRead_sim {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {g : String} {ls : LowSide u Γ Λ} (h : lowGlobSide u Γ Λ g = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hG : GRel u σ w) :
    Gabbro.Body.eval ⟨w, β⟩ (.global g) =
      some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  have resolved : ∃ (i : Fin u.globs.length), globIdx u.globs g = .ok i ∧
      (globAt u i).ty = .int ls.range.1 ls.range.2 ∧
      ∃ hd : ∀ guard ∈ (declOf u).gbraucht i, Res.von (declOf u) guard ∈ Λ,
        HEq ls.term (Expr.glob (D := declOf u) (Γ := Γ) i hd) := by
    unfold lowGlobSide at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hd
        split at h
        · rename_i lo hi' ht
          cases h
          refine ⟨i, hi, ht, hd, ?_⟩
          dsimp only
          exact mpr_heq _ _
        · cases h
        · cases h
      · cases h
  obtain ⟨i, hi, ht, hd, he⟩ := resolved
  have hty : (declOf u).gtyp i = .int ls.range.1 ls.range.2 := by
    show (globAt u i).ty.toTy = _
    rw [ht]
    rfl
  change some (w (.global g)) = _
  rw [grel_lies u hG g i hi ls.range.1 ls.range.2 ht]
  exact congrArg some (valOf_eval_heq hty.symm ls.term
    (Expr.glob (D := declOf u) i hd) he σ₀ σ ρ).symm

#print axioms lowGlobRead_sim

/-- The `bool` analogue of `lowGlobRead_sim`: a resolved `bool` static read is the Body global,
    whose value `GRel` relates to the G truth value. -/
theorem lowGlobBool_sim {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {g : String} {e : Expr (declOf u) Γ Λ .bool} (h : lowGlobBool u Γ Λ g = .ok e)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hG : GRel u σ w) :
    Gabbro.Body.eval ⟨w, β⟩ (.global g) = some (.bool (wahr? (eval σ₀ e σ ρ))) := by
  have resolved : ∃ (i : Fin u.globs.length), globIdx u.globs g = .ok i ∧
      (globAt u i).ty = .bool ∧
      ∃ hd : ∀ guard ∈ (declOf u).gbraucht i, Res.von (declOf u) guard ∈ Λ,
        HEq e (Expr.glob (D := declOf u) (Γ := Γ) i hd) := by
    unfold lowGlobBool at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hd
        split at h
        · rename_i ht
          cases h
          refine ⟨i, hi, ht, hd, ?_⟩
          dsimp only
          exact mpr_heq _ _
        · cases h
        · cases h
      · cases h
  obtain ⟨i, hi, ht, hd, he⟩ := resolved
  have hty : (declOf u).gtyp i = .bool := by
    show (globAt u i).ty.toTy = _
    rw [ht]
    rfl
  change some (w (.global g)) = _
  rw [grel_lies_bool u hG g i hi ht]
  exact congrArg some (valOf_eval_heq hty.symm e
    (Expr.glob (D := declOf u) i hd) he σ₀ σ ρ).symm

end Gabbro.Bruecke
