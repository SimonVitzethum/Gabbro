/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Narrow
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem blockNarrow_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {err : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (.int low' high' :: Γ) Λ Λ'} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err reserved) →
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest reserved) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.narrow e low' high' err rest) reserved := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, ← hlo0] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    obtain ⟨⟨hw, hl⟩, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, ⟨cx, tx⟩, hx, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execBlock]
    refine narrow_ok (reserved := reserved) (σ := σ.lese Λ e.orte) he (by omega) hw hl hh (by omega) hs hW hlo hlo0 hlo2 hpr ?_ ?_ hp hu hk hWa
    · intro hout m' pc' hp' hu' hk' hw'
      rw [dif_neg hout]
      exact Ret.toSim (ihErr (ex := exPlus ex (cr.length + 1)) cx tx hx (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ ρ hp' hlo2 hu' hk' hw' hpr)
    · intro hin m' pc' hp' hu' hk' hw'
      rw [dif_pos hin]
      exact Sim.schrumpf (ihRest (ex := ex) cr tr hr (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ _ hp' hlo (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
        hu' hk' hw' (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega))
  · cases h

theorem endNarrow_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {err : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Endblock D (vertragVon D f) l (.int low' high' :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err reserved) →
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest reserved) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.narrow e low' high' err rest) reserved := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo2 hu hk hWa hpr
  have protectedPrefix := functionFrame_prefix P f
  simp only [lowEnd, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    obtain ⟨⟨hw, hl⟩, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, ⟨cx, tx⟩, hx, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    apply Ret.ofSim (e := pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ reserved) low' high' ce cx cr).length))
    simp only [execEnd]
    refine narrow_ok (reserved := reserved) (σ := σ.lese Λ e.orte) he (by omega) hw hl hh (by omega) hs hW (by omega) hlo0 hlo2 hpr ?_ ?_ hp hu hk hWa
    · intro hout m' pc' hp' hu' hk' hw'
      rw [dif_neg hout]
      exact Ret.toSim (ihErr (ex := exPlus ex (cr.length + 1)) cx tx hx (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ ρ hp' hlo2 hu' hk' hw' hpr)
    · intro hin m' pc' hp' hu' hk' hw'
      rw [dif_pos hin]
      exact Ret.toSim (Ret.schrumpf (ihRest (ex := ex) cr tr hr (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ _ hp' (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
        hu' hk' hw' (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)))
  · cases h

theorem blockNarrowRequired_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {rest : Block D (vertragVon D f) l (.int low' high' :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest reserved) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.narrowRequired e low' high' rest) reserved := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, ← hlo0] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    obtain ⟨⟨hw, hl⟩, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execBlock]
    refine narrow_ok (reserved := reserved) (σ := σ.lese Λ e.orte) he (by omega) hw hl hh (by omega) hs hW hlo hlo0 hlo2 hpr ?_ ?_ hp hu hk hWa
    · intro hout m' pc' hp' hu' hk' hw'
      rw [dif_neg hout]
      exact stop_ok hp'.code hp'.far hp'.frame (by have := hW.ks; omega) hp'.small (by simp [logikCode])
    · intro hin m' pc' hp' hu' hk' hw'
      rw [dif_pos hin]
      exact Sim.schrumpf (ihRest (ex := ex) cr tr hr (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ _ hp' hlo (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
        hu' hk' hw' (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega))
  · cases h

theorem endNarrowRequired_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {rest : Endblock D (vertragVon D f) l (.int low' high' :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest reserved) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.narrowRequired e low' high' rest) reserved := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo2 hu hk hWa hpr
  have protectedPrefix := functionFrame_prefix P f
  simp only [lowEnd, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true] at hfit
    obtain ⟨⟨hw, hl⟩, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    apply Ret.ofSim (e := pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ reserved) low' high' ce (stopC 107 (frei Γ reserved)) cr).length))
    simp only [execEnd]
    refine narrow_ok (reserved := reserved) (σ := σ.lese Λ e.orte) he (by omega) hw hl hh (by omega) hs hW (by omega) hlo0 hlo2 hpr ?_ ?_ hp hu hk hWa
    · intro hout m' pc' hp' hu' hk' hw'
      rw [dif_neg hout]
      exact stop_ok hp'.code hp'.far hp'.frame (by have := hW.ks; omega) hp'.small (by simp [logikCode])
    · intro hin m' pc' hp' hu' hk' hw'
      rw [dif_pos hin]
      exact Ret.toSim (Ret.schrumpf (ihRest (ex := ex) cr tr hr (by omega) (by
        simp only [narrowC, List.length_append, List.length_singleton] at hs; omega) hW
        m' pc' _ _ hp' (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
        hu' hk' hw' (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)))
  · cases h

end Gabbro.Stage0.Senke
