module
public import Bruecke.Ausdruck.Scalar
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- Fitting changes bounds, never the value read by the bridge. This also covers the
    exact-type transport used for a nominal record and the erased string representation. -/
theorem fitW_val {Γ : Ctx} {Λ : List (Res (declOf u))} {ty : Ty}
    (wv : LowWert u Γ Λ) {e : Expr (declOf u) Γ Λ ty}
    (h : fitW ty wv = .ok e) (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    valOf ty (eval σ₀ e σ ρ) = valOf wv.ty (eval σ₀ wv.term σ ρ) := by
  unfold fitW at h
  split at h
  · rename_i same
    rcases wv with ⟨actual, term⟩
    dsimp only at same
    subst actual
    cases h
    rfl
  · rcases wv with ⟨actual, term⟩
    cases actual <;> cases ty <;> simp only at h
    all_goals repeat' split at h
    all_goals first | (cases h; rfl) | (cases h; done)

/-- The scalar projection of a successful `zahlVon` is the original typed term. -/
theorem zahlVon_ok {Γ : Ctx} {Λ : List (Res (declOf u))}
    {wv : LowWert u Γ Λ} {ls : LowSide u Γ Λ}
    (h : zahlVon (.ok wv) = .ok ls) : wv = ls.wert := by
  rcases wv with ⟨ty, term⟩
  cases ty <;> simp only [zahlVon, LowWert.zahl] at h
  all_goals first | (cases h; rfl) | (cases h; done)

/-- Casts inserted after nominal schema lookup do not change the Body reading. -/
theorem valOf_cast_eval {Γ : Ctx} {Λ : List (Res (declOf u))} {a b : Ty}
    (same : a = b) (e : Expr (declOf u) Γ Λ a)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    valOf b (eval σ₀ (cast (congrArg (Expr (declOf u) Γ Λ) same) e) σ ρ) =
      valOf a (eval σ₀ e σ ρ) := by
  cases same
  rfl

/-- Exact type information emitted by the record reader comes from the actual parameter
    entry. The general value lookup is used for bools and products under every kind. -/
theorem lowParam_record_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {p : String} {ty : Ty} {wv : LowWert u Γ Λ}
    (ht : valueParamTy fn p = some ty)
    (h : lowWertE u Γ Λ fn er (.param p) = .ok wv)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (β : Gabbro.Body.Binding)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    β p = valOf wv.ty (eval σ₀ wv.term σ ρ) ∧ wv.ty = ty := by
  cases hj : paramPos fn.params p with
  | error err =>
      unfold valueParamTy at ht
      rw [paramPos_find_none _ _ _ hj] at ht
      cases ht
  | ok j =>
      unfold valueParamTy at ht
      rw [paramPos_find _ _ _ hj] at ht
      cases hq : fn.params[j]? with
      | none => simp [hq] at ht
      | some q =>
          rcases q with ⟨name, actual⟩
          cases actual <;> simp only [hq] at ht <;> try { cases ht; done }
          all_goals
            cases ht
            cases hk : fn.kinds[j]? with
            | none =>
                simp only [lowWertE, lowParamWert, hj, hk, hq] at h
                split at h
                · cases h
                · rename_i v hv
                  cases h
                  exact ⟨(hL p j hj).trans (nthVal_lowVar Γ _ _ v ρ hv), rfl⟩
            | some k =>
                cases k <;> simp only [lowWertE, lowParamWert, hj, hk, hq] at h
                all_goals
                  split at h
                  · cases h
                  · rename_i v hv
                    cases h
                    exact ⟨(hL p j hj).trans (nthVal_lowVar Γ _ _ v ρ hv), rfl⟩

end Gabbro.Bruecke
