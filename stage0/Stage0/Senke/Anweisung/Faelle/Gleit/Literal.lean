/- Literal rounding is performed in Lean; the IR only materialises the resulting bits. -/
import Stage0.Senke.Anweisung.Faelle.Binden
import Stage0.Senke.Ausdruck.Gleit.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem blockFloatLit_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {q low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatLit q low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB] at h
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

end Gabbro.Stage0.Senke
