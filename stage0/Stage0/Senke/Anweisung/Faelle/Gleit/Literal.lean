/- Literal rounding is performed in Lean; the IR only materialises the resulting bits. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
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
    let cw := wordL 4 (Gleitkomma.zuBits Gleitkomma.f64 (bruch q)) (frei Γ)
    have ht := wordL_top 4 (Gleitkomma.zuBits Gleitkomma.f64 (bruch q)) (frei Γ)
    have hks := hW.ks
    have htop : frei Γ + 2 ≤ max cw.2 tr := by simp only [cw, wordL, bin2]; omega
    change max cw.2 tr + cap ≤ Ks at hK
    have hq : PreS L m pc fp K (frei Γ) (cw.1 ++ cr) ρ := hp
    have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ :=
      wordL_ok 4 _ (by simpa only [hx] using hb) (by change frei Γ + 2 ≤ Ks; omega) hpw
    have a1 := Agree.widen a1s hks
    have hen : Enc L (.fl low high) v w := ⟨hwf, by simpa only [hx] using hen⟩
    have hf := codeFar_right (n := cw.1.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * cw.1.length)) fp K (frei Γ + 1) cr
        (Env.cons (τ := .fl low high) v ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1,
       (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen,
       trivial, wstab_true _ _⟩
    have ih := ihRest (ex := ex) cr tr hr (by omega)
      (by simp only [List.length_append] at hs; omega) hW m1 _ σ _ hp1 hlo
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
      (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega))
      (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _)))
      (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
    simp only [execBlock, hv]
    rw [pc_add1]
    exact Sim.prefix hlo s1 (agreeW_of (a1.mono hlo2))
      (keeps_of_agreeW hW a1 hpr (by omega)) (Sim.schrumpf ih)

end Gabbro.Stage0.Senke
