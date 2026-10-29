/-
  File:      stage0/Stage0/Senke/Anweisung/Option.lean
  Subject:   `onOption`: keep the option word as the Some branch's index, test its XOR with the None sentinel
             in a scratch slot, and shrink the bound environment on exit. Branch simulations are hypotheses.
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Puffer

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem onOption_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {t : Block D (vertragVon D f) l (.index n :: Γ) Λ Λ'}
    {e : Block D (vertragVon D f) l Γ Λ Λ'} {cc ct ce : List II} {tc : Nat}
    (hn : n ≤ 2 ^ 63) (hs2 : frei Γ + 2 ≤ Ks)
    (hcc : lowE L o (frei Γ) = some (cc, tc)) (htc : tc ≤ Ks)
    (hs : 16 * (cc.length + 3 + ct.length + 1 + ce.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hthen : ∀ (k : Zahl 0 (n - 1)), eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = some k →
      ∀ m' pc', PreS m' pc' fp K (frei Γ + 1) ct (Env.cons (τ := .index n) k ρ) → Umf L A C dv m' fp Ks K → Kopf f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ o.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ct.length))
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).1)
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).2)
        (execBlock O passes R t (σ.lese Λ o.orte) (Env.cons (τ := .index n) k ρ)))
    (helse : ∀ m' pc', PreS m' pc' fp K (frei Γ) ce ρ → Umf L A C dv m' fp Ks K → Kopf f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ o.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ce.length))
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.2)
        (execBlock O passes R e (σ.lese Λ o.orte) ρ))
    (hp : PreS m pc fp K (frei Γ) (cc ++ [ci 1 (frei Γ + 1) (-1) 0, ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
        [ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0] ++ ct ++
      [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 1 (frei Γ + 1) (-1) 0, ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
        [ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length))
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 1 (frei Γ + 1) (-1) 0, ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
        [ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 1 (frei Γ + 1) (-1) 0, ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
        [ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.onOption o t e) σ ρ) := by
    have hsm := hp.small
    have hq : PreS m pc fp K (frei Γ) (cc ++ ([ci 1 (frei Γ + 1) (-1) 0] ++
      ([ci 10 (frei Γ + 1) (frei Γ) (frei Γ + 1)] ++
      ([ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0] ++ (ct ++
        ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))))) ρ := by simpa [List.append_assoc] using hp
    have hks := hW.ks
    have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (fp := fp) (K := Ks) (σ.lese Λ o.orte) (σ.lese Λ o.orte) (fun _ h => h) o
      (frei Γ) cc tc hcc (by omega) m pc ρ hpw
    have ae := Agree.widen a1s hks
    have q1 := hq.next ae (Nat.le_refl _) (by omega)
    have hF := q1.frame
    have sc := const_step (j := frei Γ + 1) (k := -1) q1.left.code hF (by omega) hsm (by decide)
    have acs : Agree fp (frei Γ + 1) Ks m1
        (write m1 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (BitVec.ofInt 64 (-1)).toNat) :=
      agree_write (frameOK_sub hF hks).room (Nat.le_refl _) (by omega) _
    have ac := Agree.widen acs hks
    have rc := rd_same hF (a := frei Γ + 1) (by omega) (BitVec.ofInt 64 (-1))
    have re : (write m1 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (BitVec.ofInt 64 (-1)).toNat).rd64
        (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
      rw [agree_rd_low ac hF.room (by omega) (by omega)]; exact hw
    have q2 := q1.next (ac.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
    generalize write m1 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (BitVec.ofInt 64 (-1)).toNat = m2
      at sc acs ac rc re q2
    have sxor := bin_star (o := 10) (d := frei Γ + 1) (a := frei Γ) (b := frei Γ + 1)
      (g := fun x y => some (x ^^^ y)) q2.left.code rfl (by decide) q2.frame
      (by omega) (by omega) (by omega) hsm re rc rfl
    have axs : Agree fp (frei Γ + 1) Ks m2
        (write m2 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (w ^^^ BitVec.ofInt 64 (-1)).toNat) :=
      agree_write (frameOK_sub q2.frame hks).room (Nat.le_refl _) (by omega) _
    have ax := Agree.widen axs hks
    have rx := rd_same q2.frame (a := frei Γ + 1) (by omega) (w ^^^ BitVec.ofInt 64 (-1))
    have ri : (write m2 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (w ^^^ BitVec.ofInt 64 (-1)).toNat).rd64
        (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
      rw [agree_rd_low ax hF.room (by omega) (by omega)]; exact re
    have h1 := q2.next (ax.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
    generalize write m2 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) 8 (w ^^^ BitVec.ofInt 64 (-1)).toNat = m3
      at sxor axs ax rx ri h1
    have a1 := ae.trans ((ac.trans ax).mono (Nat.le_succ _))
    have hWa1 : WeltAt m3 L σ := hpw.wstab m m3 hWa
      ((a1s.trans ((acs.trans axs).mono (Nat.le_succ _))).mono (Nat.zero_le _))
    have hu1 := hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo
    have hk1 := hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega)
    have spre := s1.trans ((star_cast sc rfl (by simp)).trans sxor)
    have hbrz := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have h2 := h1.next (a := [ci 19 (frei Γ + 1) (16 * (ct.length + 2)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
      (by omega)
    have hd0 : sx (II.f ((frei Γ : Int) + 1)) = BitVec.ofNat 64 (frei Γ + 1) := by
      simpa using sx_nat (d := frei Γ + 1) (by omega)
    simp only [execStmt]
    split
    · next k hb =>
      have hi : Enc (D := D) (.index n) k w := by simpa only [Enc, hb, optN] using hen
      have hne : w ^^^ BitVec.ofInt 64 (-1) ≠ 0 := by
        intro hz
        have heq := BitVec.xor_eq_zero_iff.mp (show w ^^^ BitVec.ofInt 64 (-1) = 0#64 from hz)
        have he : (BitVec.ofInt 64 k.n == BitVec.ofInt 64 (-1)) = true := by rw [← hi, heq]; decide
        rw [beq_in (by have := k.lo_le; have := k.le_hi; omega) (by decide)] at he
        have := k.lo_le
        simp only [decide_eq_true_eq] at he
        omega
      have sb := star_ins (fp := fp) (m' := m3) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact rx) hne)
      have hpt : PreS m3 _ fp K (frei Γ + 1) ct (Env.cons (τ := .index n) k ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, h2.small, h2.frame, h2.left.code, h2.left.far,
          envAt_cons h2.env ri hi, trivial, wstab_true _ _⟩
      have ih := Sim.schrumpf (hthen k hb m3 _ hpt hu1 hk1 hWa1)
      have hf3 := codeFar_right (n := ct.length) (k := ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length)
        (by simpa using h2.far)
      refine Sim.prefix hlo (spre.trans sb) (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.cont ih (fun m2 a2 => ?_) ?_ ?_)
      rotate_left
      · simp only [exPlus, List.length_append, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq (by omega)
      · simp only [exPlus, List.length_append, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq (by omega)
      have hc3 := codeAt_agreeWIn hW a2 (codeAt_right h2.code) hf3
      have hjmp := hc3 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hjmp
      have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
      have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
        have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
      rw [hl] at sj
      refine star_cast sj rfl ?_
      simp only [T.mk.injEq, and_true, List.length_append, List.length_cons,
        List.length_nil, addr_norm]
      congr 2
      omega
    · next hb =>
      -- None: the sentinel test is zero, so brz skips the Some branch.
      have hw0 : w ^^^ BitVec.ofInt 64 (-1) = 0 := by
        have he : w = BitVec.ofInt 64 (-1) := by simpa only [Enc, hb, optN] using hen
        rw [he, BitVec.xor_self]; rfl
      have hl : sx (II.f (16 * ((ct.length : Int) + 2))) = BitVec.ofNat 64 (16 * (ct.length + 2)) := by
        have := sx_nat (d := 16 * (ct.length + 2)) (by omega); simpa using this
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
        (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd0, ← hw0]; exact rx)))
      rw [hl] at sb
      have h4 := ((h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next
        (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega))
      have ih := helse m3 _ h4 hu1 hk1 hWa1
      refine Sim.prefix hlo (spre.trans sb) (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.cast ih ?_ ?_ ?_ ?_)
      · simp only [T.mk.injEq, and_true, List.length_cons, List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq0 (by omega)
      · simp only [List.length_append, List.length_cons, List.length_nil, addr_norm]
        exact tgt_eq0 (by omega)

end Gabbro.Stage0.Senke
