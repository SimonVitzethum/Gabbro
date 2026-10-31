/- Literal rounding is performed in Lean; the IR only materialises the resulting bits. -/
import Stage0.Senke.Anweisung.Faelle.Binden
import Stage0.Senke.Ausdruck.Gleit.Wort
import Stage0.Senke.Ausdruck.Gleit.Test
import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem blockFloatLit_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {q low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatLit q low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, floatLiteralL] at h
  cases hv : gleitPasst low high (bruch q) with
  | none =>
    rw [hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execBlock, hv, Sim]
    change Stops ⟨pc, fp⟩ m 107
    exact stop_ok hp.code hp.far hp.frame (by have := hW.ks; omega) hp.small (by decide)
  | some v =>
    rw [hv] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hx : v.x = bruch q := by unfold gleitPasst at hv; split at hv <;> cases hv; rfl
    have hwf : Gleitkomma.wf Gleitkomma.f64 v.x := by
      rw [hx]; exact Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _
    have hb := Gleitkomma.zuBits_lt _ Gleitkomma.f64_dicht v.x hwf
    change Gleitkomma.zuBits Gleitkomma.f64 v.x < 65536 ^ 4 at hb
    let cw := konstWL 4 (Gleitkomma.zuBits Gleitkomma.f64 (bruch q)) (frei Γ)
    have ht := konstWL_top 4 (Gleitkomma.zuBits Gleitkomma.f64 (bruch q)) (frei Γ)
    have hks := hW.ks
    have htop : frei Γ + 2 ≤ max cw.2 tr := by simp only [cw, konstWL, bin2]; omega
    change max cw.2 tr + cap ≤ Ks at hK
    simp only [execBlock, hv]
    refine bindValue_ok (L := L) (τ := .fl low high) (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp hu hk hWa
    · intro m pc hp
      exact (konstWL_ok 4 _ (by simpa only [hx] using hb) (by omega) hp).mono
        fun w hen => ⟨hwf, by simpa only [hx] using hen⟩
    · intro m pc hp hu hk hw
      exact ihRest (ex := ex) cr tr hr (by omega)
        (by simp only [List.length_append] at hs; omega) hW m pc σ _ hp hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu hk hw
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)

theorem blockFloatOfLit_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Int} {low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatOf (.lit n) low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  have hx : gleitAusInt n = bruch (n, 1) := by
    simpa only [gleitAusInt, bruch, show ¬(1 : Int) < 0 by omega, ↓reduceIte,
      Int.natAbs_one] using Gleitkomma.ofInt_bruch Gleitkomma.f64 n
  have result := blockFloatLit_case hS hA hlo0 hens ihRest c top
    (by simpa only [lowB] using h) hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simpa only [execBlock, eval, Expr.orte, World.lese, World.merke,
    List.map_nil, List.nil_append, hx] using result

theorem blockFloatOfComputed_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {a b : Int} {e : Expr D Γ Λ (.int a b)} {low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatOf e low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB] at h
  split at h
  · next n =>
    exact blockFloatOfLit_case hS hA hlo0 hens ihRest c top
      (by simpa only [lowB] using h) hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    cases hc
    have het := computedFloatOfE_bounds he
    have hguard : -2^63 ≤ a ∧ b < 2^63 := by
      unfold computedFloatOfE at he
      split at he
      · next hg => exact hg.2
      · cases he
    let σr := σ.lese Λ e.orte
    let x := gleitAusInt (eval σr e σr ρ).n
    have hwf : Gleitkomma.wf Gleitkomma.f64 x :=
      Gleitkomma.ofInt_wf _ Gleitkomma.f64_p _
    have hfinite : gleitEndlich x = true := by
      let v := (eval σr e σr ρ)
      have habs : v.n.natAbs ≤ 2^63 := by
        have := v.lo_le; have := v.le_hi
        omega
      have hf := Gleitkomma.ofInt_finite Gleitkomma.f64 (by decide) v.n
        (by change v.n.natAbs < 2^1023; omega)
      rcases hf with hf | hf | hf <;> change gleitEndlich (Gleitkomma.ofInt Gleitkomma.f64 v.n) = true <;> simp [gleitEndlich, hf]
    have conv : ∀ j code t, computedFloatOfE L Gleitkomma.f64 e j = some (code, t) → t ≤ Ks →
        ∀ m pc, Pre L m pc fp Ks j code ρ (fun m => WeltAt m L σr) →
        Ok m pc fp Ks j code (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
          w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)) := by
      intro j code t hc ht m pc hp
      exact (computedFloatOfE_ok (σ₀ := σr) (σ := σr) hc hp ht
        (fun c t hc ht hp => lowE_ok σr σr (fun _ h => h) e j c t hc ht m pc ρ hp)).mono
          (fun w hw => ⟨hwf, hw⟩)
    simp only [floatNarrowC, List.length_append, List.length_singleton] at hs
    simp only [execBlock]
    have hchoice := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ)
      (cc := cc) (ct := stopC 107 (frei Γ)) (ce := ce ++ cr)
      (b := floatRangeReject low high x)
      (ot := match gleitPasst low high x with
        | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
        | none => .logik .bereich)
      (oe := match gleitPasst low high x with
        | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
        | none => .logik .bereich)
      (Nat.le_refl _) (by have := hW.ks; omega) (by simpa only [List.length_append] using hs)
      hW hlo hlo0 hlo2 hpr (σ := σr) ?_ ?_ ?_
      (by simpa only [floatNarrowC, List.length_append, Int.natCast_add] using hp) hu hk hWa
    · cases hv : gleitPasst low high x <;>
        simpa only [ite_self, hv, floatNarrowC, List.length_append, Int.natCast_add] using hchoice
    · intro hpc
      have hpw := PreS.welt hpc hW.ks hWa hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, st, a1, w, hw, hen⟩ := canonicalFloatRangeL_ok x hwf hfinite
        (fun j => computedFloatOfE L Gleitkomma.f64 e j) conv hcc (by omega) hpw
      exact ⟨m1, st, Agree.widen a1 hW.ks, w, hw, by simpa only [bool_word] using hen⟩
    · intro hb m' pc' hp' _ hu' hk' hw'
      rw [(floatRangeReject_none hwf hfinite).mpr hb]
      change Stops ⟨pc', fp⟩ m' 107
      exact stop_ok hp'.code hp'.far hp'.frame (by have := hW.ks; omega) hp'.small (by decide)
    · intro hb m' pc' hp' _ hu' hk' hw'
      cases hv : gleitPasst low high x with
      | none =>
        have hf := (floatRangeReject_none hwf hfinite).mp hv
        rw [hb] at hf
        cases hf
      | some v =>
        have hvx := floatPasst_x hv
        refine bindValue_ok (L := L) (τ := .fl low high) (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp' hu' hk' hw'
        · intro m pc hp
          exact (conv _ _ _ he (by omega) m pc hp).mono
            fun w hen => ⟨by simpa only [hvx] using hen.1, by simpa only [hvx] using hen.2⟩
        · intro m pc hp hu hk hw
          exact ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m pc σr _ hp hlo
            (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu hk hw
            (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)

end Gabbro.Stage0.Senke
