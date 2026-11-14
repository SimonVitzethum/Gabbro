module
public import Bruecke.Anweisung.Lokal.Schreiben
@[expose] public section

/-!
# C4, part 2: the direct call and the trailing return in every scope

`lowCallArgOne_sim`, `lowCallArgsAux_sim`, `lowCall_sim` (`Anweisung/Teil1.lean`, `Teil2.lean`)
and `lowEnd_sim` (`Nachbedingung.lean`) for every scope `Γ`/`fn` with `UmfangB Γ fn ns`: an argument
or a returned value may read a local.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- A pointer name reads as `.absent` in a related binding, in every scope. -/
theorem lrel_ptrB {Γ : Ctx} {fn : UFn} {ρ : Env (declOf u) Γ} {β : Gabbro.Body.Binding}
    (hΓ : Γ = fn.params.map (·.2)) (hL : LRel fn 0 ρ β) (p : String) (j : Nat)
    (hj : paramPos fn.params p = .ok j) (cap : DataCapTy)
    (hτ : (fn.params[j]?).map (·.2) = some (.ptr cap)) : β p = .absent := by
  rw [hL p j hj, Nat.zero_add]
  exact nthVal_ptr ρ j cap (by rw [hΓ, List.getElem?_map]; exact hτ)

/-- **One call argument**, in every scope. -/
theorem lowCallArgOne_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {k : UParamArt} {τ : Ty} {a : UArg}
    {e : Expr (declOf u) Γ Λ τ} {eB : Gabbro.Body.Expr}
    (h : lowCallArgOneL u c Γ fn Λ k τ a = .ok e) (hb : argExpr u fn a = some eB)
    (hK : ArtSchlicht k = true) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    Gabbro.Body.eval s eB = some (valOf τ (eval σ₀ e σ ρ)) := by
  have hA := hU.art
  have hN := hU.pointer
  cases a with
  | var p =>
    simp only [argExpr, Option.some.injEq] at hb
    subst hb
    simp only [lowCallArgOneL, bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h
         simp only [Gabbro.Body.eval]
         rw [hL p _ ‹paramPos fn.params p = .ok _›, Nat.zero_add,
           nthVal_lowVar _ _ _ _ ρ (by assumption)] <;> rfl)
  | freshPtr tname w2 =>
    simp only [argExpr] at hb
    cases hq : ptrParam u fn tname with
    | none => rw [hq] at hb; cases hb
    | some p' =>
      rw [hq] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      have goal : Gabbro.Body.eval s (.name p') = some .absent := by
        unfold ptrParam at hq
        split at hq
        · rename_i q hfil
          simp only [Option.some.injEq] at hq
          subst hq
          have hmem := hfil ▸ List.mem_singleton_self q
          rw [List.mem_filter] at hmem
          obtain ⟨hqm, hqp⟩ := hmem
          obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hqm
          have hposPtr := hN jq q.1
          have hty : ∃ cap, q.2 = .ptr cap := by
            revert hqp
            cases q.2 <;> simp
          obtain ⟨cap, htq⟩ := hty
          have hpos := hposPtr cap (by rw [hjq, ← htq])
          have hab := lrel_ptrB hU.ctx hL q.1 jq hpos cap (by rw [hjq]; simp [htq])
          simp only [Gabbro.Body.eval, hab]
        · cases hq
      simp only [lowCallArgOneL, bind, Except.bind] at h
      repeat' split at h
      all_goals first | (cases h; exact goal) | cases h
  | val sd =>
    simp only [argExpr] at hb
    cases k with
    | ptr cap =>
      cases τ with
      | ptr target =>
        obtain ⟨space, ⟨read, write, owner⟩, ⟨num⟩⟩ := target
        cases owner <;> simp only [lowCallArgOneL] at h
        all_goals repeat' split at h
        all_goals cases h
      | _ => simp only [lowCallArgOneL] at h; cases h
    | index num =>
      cases τ with
      | int lo hi =>
        simp only [lowCallArgOneL] at h
        by_cases hlt : num < u.tabs.length
        · rw [dif_pos hlt] at h
          by_cases hLo : lo = 0
          · rw [dif_pos hLo] at h
            by_cases hHi : hi = (declOf u).count ⟨num, hlt⟩ - 1
            · rw [dif_pos hHi] at h
              cases hix : uIdxOfSide sd with
              | error error => rw [hix] at h; cases h
              | ok ix =>
                rw [hix] at h
                dsimp only at h
                cases hei : lowIdx u Γ Λ fn 0 ⟨num, hlt⟩ ix with
                | error error => erw [hei] at h; cases h
                | ok ei =>
                  erw [hei] at h
                  cases h
                  rw [uIdxOfSide_expr hix hb]
                  rw [lowIdx_sim hei σ₀ σ ρ s.world s.local' hL]
                  have hτ : Ty.int lo hi = Ty.index ((declOf u).count ⟨num, hlt⟩) := by rw [hLo, hHi]
                  rw [valOf_eval_heq hτ _ ei ((mpr_heq _ _).trans (mpr_heq _ _)) σ₀ σ ρ] <;> rfl
            · rw [dif_neg hHi] at h; cases h
          · rw [dif_neg hLo] at h; cases h
        · rw [dif_neg hlt] at h; cases h
      | _ => simp only [lowCallArgOneL] at h; cases h
    | int =>
      cases τ with
      | int lo hi =>
        simp only [lowCallArgOneL] at h
        cases he' : lowWertAt u Γ Λ fn lo hi sd with
        | error error => rw [he'] at h; cases h
        | ok value =>
          rw [he'] at h
          cases h
          exact lowWertAt_sim he' hb hA hT σ₀ σ ρ s.world s.local' hW hL
      | _ => simp only [lowCallArgOneL] at h; cases h
    | bool => cases τ <;> simp only [lowCallArgOneL] at h <;> cases h
    | wert =>
      cases τ <;> simp only [lowCallArgOneL] at h
      all_goals first
        | exact lowWertAtE_rec_sim (er := none) h hb hA hT σ₀ σ ρ s.world s.local' hW hL
        | cases h
    | opt num | why num | sum num => cases τ <;> simp only [lowCallArgOneL] at h <;> cases h
    | _ => simp only [ArtSchlicht, Bool.false_eq_true] at hK
  | bval b =>
    simp only [argExpr] at hb
    simp only [lowCallArgOneL] at h
    -- Reduce the dependent kind/type match before eliminating impossible successes.
    split at h
    all_goals first
      | exact lowEns_raw_sim h hb hA hT σ₀ σ ρ s hW hL
      | (repeat' split at h
         all_goals cases h)
  | oval _ | gval _ | fnref _ => simp only [argExpr, reduceCtorEq] at hb


/-- **The argument list**, in every scope. -/
theorem lowCallArgsAux_simB (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∀ (ks : List UParamArt) (ts : List Ty) (as : List UArg)
      (a : Args (declOf u) Γ Λ ts) (es : List Gabbro.Body.Expr),
      (∀ k ∈ ks, ArtSchlicht k = true) →
      lowCallArgsAuxL u c Γ fn Λ ks ts as = .ok a → argsExpr u fn as = some es →
      Gabbro.Body.evalAll s es = some (envVals (evalArgs σ₀ a σ ρ))
  | [], ts, as, a, es, _, h, hb => by
      simp only [lowCallArgsAuxL] at h
      split at h
      · cases h
        simp only [argsExpr, Option.some.injEq] at hb
        subst hb
        rfl
      · cases h
  | k :: ks, ts, as, a, es, hKs, h, hb => by
      simp only [lowCallArgsAuxL] at h
      split at h
      · rename_i t ts' x as'
        split at h
        · cases h
        · rename_i e he
          split at h
          · cases h
          · rename_i rest hrest
            cases h
            simp only [argsExpr] at hb
            split at hb
            · rename_i eB esB hx hxs
              simp only [Option.some.injEq] at hb
              subst hb
              have h1 := lowCallArgOne_simB c he hx (hKs k (List.mem_cons_self ..))
                hU hT σ₀ σ ρ s hW hL
              have h2 := lowCallArgsAux_simB c hU hT σ₀ σ ρ s hW hL ks ts' as' rest esB
                (fun k hk => hKs k (List.mem_cons_of_mem _ hk)) hrest hxs
              simp only [Gabbro.Body.evalAll, h1, h2] <;> rfl
            · cases hb
      · cases h

end Gabbro.Bruecke
