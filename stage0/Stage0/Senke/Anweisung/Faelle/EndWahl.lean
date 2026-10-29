/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem endIte_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {cnd : Expr D Γ Λ .bool} {t : Endblock D (vertragVon D f) l Γ Λ} {e : Endblock D (vertragVon D f) l Γ Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex t) →
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex e) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .ite cnd t e) := by
  intro ihT ihE c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append, List.length_singleton] at hs
  have hFB3 : FB = 4 := rfl
  have hsm := hp.small
  have htop := lowE_top cnd (frei Γ) cc tc hcc
  have hq : PreS L m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ := by
    simpa [List.append_assoc] using hp
  have hks := hW.ks
  have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (fp := fp) (K := Ks) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) (fun _ h => h) cnd
    (frei Γ) cc tc hcc (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have h1 := hq.next a1 (Nat.le_refl _) (by omega)
  have hu1 := hu.agree a1 hp.frame (by omega)
  have hk1 := hk.agree a1 hp.frame (by omega)
  have hbrz := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
  have h2 := h1.next (a := [ci 19 (frei Γ) (16 * (ct.length + 1)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
    (by omega)
  have hd0 : sx (II.f (frei Γ : Int)) = BitVec.ofNat 64 (frei Γ) := sx_nat (by omega)
  simp only [execEnd]
  split
  · next hb =>
    have hw1 : w = 1 := by
      simp only [Enc] at hen
      rw [hen, if_pos hb]
    have sb := star_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
      (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact hw) (by rw [hw1]; decide))
    have ih := ihT (ex := exPlus ex ce.length) ct
      tt hct (by omega) (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h2.left hlo hu1 hk1 hWa1 hpr
    refine Ret.prefix (by omega) (s1.trans sb) (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.cast ih rfl ?_ ?_)
    · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · next hb =>
    have hw0 : w = 0 := by
      simp only [Enc] at hen
      rw [hen, if_neg hb]
    have hl : sx (II.f (16 * ((ct.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ct.length + 1)) := by
      have := sx_nat (d := 16 * (ct.length + 1)) (by omega); simpa using this
    have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
      (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd0, ← hw0]; exact hw)))
    rw [hl] at sb
    have h4 := h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have ih := ihE (ex := ex) ce te hce (by omega)
      (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h4 hlo hu1 hk1 hWa1 hpr
    refine Ret.prefix (by omega) (s1.trans sb) (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.cast ih ?_ ?_ ?_)
    · simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
      congr 2
      omega
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)

end Gabbro.Stage0.Senke
