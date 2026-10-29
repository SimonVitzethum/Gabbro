/-
  File:      stage0/Stage0/Senke/Anweisung/Wahl.lean
  Subject:   `ir_sim` for `if c { t } else { e }` (`ite`): the condition into slot `frei Γ`, `brz` to the `else` code, the
             `then` code and a jump over the `else` code; G's branch is the code's (`ite_ok`). The branches' own
             simulations come in as hypotheses (the induction of `lowS_ok`).
-/
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem ite_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cnd : Expr D Γ Λ .bool}
    {t e : Block D (vertragVon D f) l Γ Λ Λ'} {cc ct ce : List II} {tc tt te : Nat}
    (hcc : lowE L cnd (frei Γ) = some (cc, tc)) (htc : tc ≤ Ks) (htt : tt ≤ Ks) (hte : te ≤ Ks)
    (hs : 16 * (cc.length + 1 + ct.length + 1 + ce.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hthen : ∀ m' pc', PreS L m' pc' fp K (frei Γ) ct ρ → Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ cnd.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ct.length))
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).1)
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).2)
        (execBlock O passes R t (σ.lese Λ cnd.orte) ρ))
    (helse : ∀ m' pc', PreS L m' pc' fp K (frei Γ) ce ρ → Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ cnd.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ce.length))
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.2)
        (execBlock O passes R e (σ.lese Λ cnd.orte) ρ))
    (hp : PreS L m pc fp K (frei Γ) (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
      [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length))
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.ite cnd t e) σ ρ) := by
    have hsm := hp.small
    have htop := lowE_top cnd (frei Γ) cc tc hcc
    have hsm' := hsm
    have hq : PreS L m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ (ct ++
        ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))) ρ := by simpa [List.append_assoc] using hp
    have hks := hW.ks
    have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (fp := fp) (K := Ks) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) (fun _ h => h) cnd
      (frei Γ) cc tc hcc (by omega) m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have hu1 := hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo
    have hk1 := hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega)
    have hF1 := h1.frame
    have hbrz := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have h2 := h1.next (a := [ci 19 (frei Γ) (16 * (ct.length + 2)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
      (by omega)
    have hd0 : sx (II.f (frei Γ : Int)) = BitVec.ofNat 64 (frei Γ) := sx_nat (by omega)
    simp only [execStmt]
    split
    · next hb =>
      -- the condition holds: brz falls through, the `then` block, jmp to the end
      have hw1 : w = 1 := by
        simp only [Enc] at hen
        rw [hen, if_pos hb]
      have sb := star_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact hw) (by rw [hw1]; decide))
      have ih := hthen m1 _ h2.left hu1 hk1 hWa1
      have hf3 := codeFar_right (n := ct.length) (k := ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length)
        (by simpa using h2.far)
      refine Sim.prefix hlo (s1.trans sb) (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.cont ih (fun m2 a2 => ?_) ?_ ?_)
      rotate_left
      · simp only [exPlus, List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq (by omega)
      · simp only [exPlus, List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq (by omega)
      have hc3 := codeAt_agreeWIn hW a2 (codeAt_right h2.code) hf3
      have hjmp := hc3 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hjmp
      have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
      have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
        have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
      rw [hl] at sj
      refine star_cast sj rfl ?_
      simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
        List.length_nil, addr_norm]
      congr 2
      omega
    · next hb =>
      -- the condition fails: brz jumps to the `else` block
      have hw0 : w = 0 := by
        simp only [Enc] at hen
        rw [hen, if_neg hb]
      have hl : sx (II.f (16 * ((ct.length : Int) + 2))) = BitVec.ofNat 64 (16 * (ct.length + 2)) := by
        have := sx_nat (d := 16 * (ct.length + 2)) (by omega); simpa using this
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
        (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd0, ← hw0]; exact hw)))
      rw [hl] at sb
      have h4 := ((h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next
        (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega))
      have ih := helse m1 _ h4 hu1 hk1 hWa1
      refine Sim.prefix hlo (s1.trans sb) (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.cast ih ?_ ?_ ?_ ?_)
      · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq0 (by omega)
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq0 (by omega)

end Gabbro.Stage0.Senke
