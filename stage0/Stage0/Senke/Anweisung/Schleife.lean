/-
  File:      stage0/Stage0/Senke/Anweisung/Schleife.lean
  Subject:   `traverse` (`travC`): the IR loop runs G's `traverseLauf` over the indices `0 ..< count` (`trav_ok`).

  The counter lives in the index's own slot `s = frei Γ`; the body may not write it (`s` is protected in the body,
  `Keeps`). The head checks the invariant (false: the stop 104, G's `logik schleife`) and `k < count` (false: the
  end, G's `ok`); the body's `ok` and `next` go on at the next part (`k := k + 1`, back to the head), its `leave`
  at the leave part (the invariant once more, then the end or the stop). The proof runs by induction over the
  indices left (`List.range'`).
-/
import Stage0.Senke.Anweisung.SchleifeTeile

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-! ## The loop -/

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp : Runner.W}
  {fp : Runner.W} {lo K Ks : Nat} {pr : List Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
  {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
  {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {ci' cb : List II × Nat} {pc eL eN : Runner.W}

/-- The stop at the end of the loop's code, from the first `brz` of the head or of the leave part. -/
theorem trav_stopped {m : Runner.Mem} {ρ : Env D Γ}
    (hp : PreS m pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ) (hks : frei Γ + 9 ≤ K) :
    Stops ⟨pc + BitVec.ofNat 64 (16 * (11 + 2 * ci'.1.length + cb.1.length)), fp⟩ m 104 := by
  have hlen := travCode_len (s := frei Γ) (n := D.count t) (ci' := ci'.1) (cb := cb.1)
  exact stop_ok (trav_stop hp.code) (codeFar_at (k := 3) hp.far (by rw [hlen]; omega)) hp.frame (by omega) hp.small
    (by decide)

theorem trav_loop (hn : lit32 (D.count t) = true) (hci : lowE L inv (frei Γ + 1) = some ci')
    (hlenc : 16 * (10 + ci'.1.length + cb.1.length) < 2 ^ 31) (hlo0 : lo = FB + (D.params f).length)
    (htop : max ci'.2 (max cb.2 (frei Γ + 9)) ≤ Ks) (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ)
    (hbody : ∀ m' pc' σ' ρ', PreS m' pc' fp K (frei (.index (D.count t) :: Γ)) cb.1 ρ' → Umf A C dv m' fp K →
      Kopf f m' fp K rp cfp ρ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K (frei Γ :: pr) ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cb.1.length))
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 48)
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 0) (execBlock O passes R body σ' ρ')) :
    ∀ (n k : Nat) (m' : Runner.Mem) (σ' : World D) (ρ' : Env D Γ), k + n = (D.count t).toNat →
    PreS m' pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ' →
    m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k) →
    Umf A C dv m' fp K → Kopf f m' fp K rp cfp ρ0 → WeltAt m' L σ' →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m'
      (pc + BitVec.ofNat 64 (16 * (travCode (frei Γ) (D.count t) ci'.1 cb.1).length)) eL eN
      (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) (idxAb (D.count t) k n) σ' ρ') := by
  have hks := hW.ks
  have hnl : (D.count t) < 2 ^ 31 ∧ -2 ^ 31 ≤ D.count t := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hn; omega
  intro n
  induction n with
  | zero =>
    intro k m' σ' ρ' hkn hp hk0 hu hk hWa
    have hlen := travCode_len (s := frei Γ) (n := D.count t) (ci' := ci'.1) (cb := cb.1)
    obtain ⟨m1, w, s1, a1s, hw, hwe, hWa1⟩ := trav_head (cb := cb.1) hci (by omega) hW hp hWa
    have a1 := Agree.widen a1s hks
    have hc1 := hp.code.agree (a1.mono (Nat.le_succ _)) hp.far
    have hp1 : PreS m1 pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ' :=
      mkPreS (Nat.le_refl _) hp.small (hp.frame.agree a1) hc1 hp.far
        (envAt_agree hp.env (a1.mono (Nat.le_succ _)) hp.frame (Nat.le_refl _) (by omega))
    simp only [idxAb_zero, traverseLauf]
    split
    · next hinv =>
      -- the invariant holds: `k < count` is false, the end
      have hw1 : w = 1 := by rw [hwe]; simpa using hinv
      have sb := brz_stay (trav_brz1 hc1) (by omega) hp.small hw (by rw [hw1]; decide)
      have hk1 : m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k) := by
        rw [agree_rd_low a1s (frameOK_sub hp.frame hks).room (Nat.lt_succ_self _) (by omega)]; exact hk0
      obtain ⟨m2, s2, a2s, hw2, hWa2⟩ := trav_cmp_ok hn hp1 hW hWa1 (by omega) hk1 (by omega)
      have hkc : decide ((k : Int) < D.count t) = false := by simp; omega
      rw [hkc] at hw2
      have a2 := Agree.widen a2s hks
      have hc2 := hp.code.agree ((a1.trans a2).mono (Nat.le_succ _)) hp.far
      have sc := brz_go (trav_brz2 hc2) (by omega) hp.small (lit_ok (by omega) (by omega)) hw2
      rw [adr_eq pc (y := 14 + 2 * ci'.1.length + cb.1.length) (by push_cast; omega)] at sc
      rw [step_eq pc (z := 2 + ci'.1.length) (by omega)] at sb
      rw [hlen]
      refine ⟨m2, s1.trans (sb.trans (s2.trans sc)),
        agreeW_of (((a1.trans a2).mono (Nat.le_succ _)).mono hlo2), ?_, hWa2,
        keeps_of_agree (a1.trans a2) hp.frame.room (fun j hj => by have := hpr j hj; omega) (by omega)⟩
      exact envAt_agree hp.env ((a1.trans a2).mono (Nat.le_succ _)) hp.frame (Nat.le_refl _) (by omega)
    · next hinv =>
      -- the invariant fails: the stop
      have hw0 : w = 0 := by rw [hwe]; simpa using hinv
      have sb := brz_go (trav_brz1 hc1) (by omega) hp.small (lit_ok (by omega) (by omega)) (by rw [← hw0]; exact hw)
      rw [adr_eq pc (y := 11 + 2 * ci'.1.length + cb.1.length) (by push_cast; omega)] at sb
      exact Stops.prefix (s1.trans sb) (trav_stopped hp1 (by omega))
  | succ n ih =>
    intro k m' σ' ρ' hkn hp hk0 hu hk hWa
    have hlen := travCode_len (s := frei Γ) (n := D.count t) (ci' := ci'.1) (cb := cb.1)
    have hroom := hp.frame.room
    have hFB3 : FB = 3 := rfl
    obtain ⟨m1, w, s1, a1s, hw, hwe, hWa1⟩ := trav_head (cb := cb.1) hci (by omega) hW hp hWa
    have a1 := Agree.widen a1s hks
    have hc1 := hp.code.agree (a1.mono (Nat.le_succ _)) hp.far
    have hp1 : PreS m1 pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ' :=
      mkPreS (Nat.le_refl _) hp.small (hp.frame.agree a1) hc1 hp.far
        (envAt_agree hp.env (a1.mono (Nat.le_succ _)) hp.frame (Nat.le_refl _) (by omega))
    obtain ⟨x, hxn, hxs⟩ := idxAb_succ (D.count t) k n (by omega)
    rw [hxs]
    simp only [traverseLauf]
    split
    · next hinv =>
      have hw0 : w = 0 := by rw [hwe]; simpa using hinv
      have sb := brz_go (trav_brz1 hc1) (by omega) hp.small (lit_ok (by omega) (by omega)) (by rw [← hw0]; exact hw)
      rw [adr_eq pc (y := 11 + 2 * ci'.1.length + cb.1.length) (by push_cast; omega)] at sb
      exact Stops.prefix (s1.trans sb) (trav_stopped hp1 (by omega))
    · next hinv =>
      have hw1 : w = 1 := by rw [hwe]; simp only [Bool.not_eq_false] at hinv; simp [hinv]
      have sb := brz_stay (trav_brz1 hc1) (by omega) hp.small hw (by rw [hw1]; decide)
      rw [step_eq pc (z := 2 + ci'.1.length) (by omega)] at sb
      have hk1 : m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k) := by
        rw [agree_rd_low a1s (frameOK_sub hp.frame hks).room (Nat.lt_succ_self _) (by omega)]; exact hk0
      obtain ⟨m2, s2, a2s, hw2, hWa2⟩ := trav_cmp_ok hn hp1 hW hWa1 (by omega) hk1 (by omega)
      have hkc : decide ((k : Int) < D.count t) = true := by simp; omega
      rw [hkc] at hw2
      have a2 := Agree.widen a2s hks
      have A12 : Agree fp (frei Γ + 1) K m' m2 := a1.trans a2
      have hc2 := hp.code.agree (A12.mono (Nat.le_succ _)) hp.far
      have sb2 := brz_stay (trav_brz2 hc2) (by omega) hp.small hw2 (by decide)
      rw [step_eq pc (z := 6 + ci'.1.length) (by omega)] at sb2
      have hk2 : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k) := by
        rw [agree_rd_low a2s (frameOK_sub hp.frame hks).room (Nat.lt_succ_self _) (by omega)]; exact hk1
      have hF2 := hp.frame.agree A12
      have hE2 : EnvAt m2 fp ρ' := envAt_agree hp.env (A12.mono (Nat.le_succ _)) hp.frame (Nat.le_refl _) (by omega)
      have hex : Enc (D := D) (.index (D.count t)) x (BitVec.ofNat 64 k) := by
        simp only [Enc]; rw [hxn, BitVec.ofInt_natCast]
      have hpb : PreS m2 (pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length))) fp K (frei (.index (D.count t) :: Γ)) cb.1
          (Env.cons (show Wert D (Ty.index (D.count t)) from x) ρ') :=
        mkPreS (Nat.le_refl _) hp.small hF2 (trav_body hc2) (codeFar_at hp.far (by omega)) (envAt_cons hE2 hk2 hex)
      have hu2 := hu.agree A12 hp.frame (by omega)
      have hk2' := hk.agree A12 hp.frame (by omega)
      have hb := hbody m2 _ (σ'.lese Λ inv.orte) (Env.cons (show Wert D (Ty.index (D.count t)) from x) ρ') hpb hu2 hk2' hWa2
      have pre : Star ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m'
          ⟨pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length)), fp⟩ m2 := s1.trans (sb.trans (s2.trans sb2))
      have K12 : Keeps fp pr m' m2 := keeps_of_agree A12 hroom (fun j hj => by have := hpr j hj; omega) (by omega)
      have Bend : pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length)) + BitVec.ofNat 64 (16 * cb.1.length) =
          pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length + cb.1.length)) := step_eq pc (by omega)
      -- the next part: `k := k + 1`, back to the head, the rest of the indices
      have nx : ∀ (σ1 : World D) (ρ1 : Env D (.index (D.count t) :: Γ)) (m4 : Runner.Mem),
          Star ⟨pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length)), fp⟩ m2
            ⟨pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length + cb.1.length)), fp⟩ m4 →
          AgreeW L fp lo K m2 m4 → EnvAt m4 fp ρ1 → WeltAt m4 L σ1 → Keeps fp (frei Γ :: pr) m2 m4 →
          Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m'
            (pc + BitVec.ofNat 64 (16 * (travCode (frei Γ) (D.count t) ci'.1 cb.1).length)) eL eN
            (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) (idxAb (D.count t) (k + 1) n)
              σ1 ρ1.tail) := by
        intro σ1 ρ1 m4 s4 a4 e4 w4 k4
        have A14 : AgreeW L fp lo K m' m4 := (agreeW_of (A12.mono (by omega))).trans a4
        have hc4 := codeAt_agreeWIn hW A14 hp.code hp.far
        have hk4 : m4.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k) := by
          rw [k4 _ List.mem_cons_self]; exact hk2
        have hF4 := frameOK_agreeW hp.frame A14
        have hq : PreS m4 (pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length + cb.1.length))) fp K (frei Γ)
            [ci 1 (frei Γ + 1) 1 0, ci 3 (frei Γ) (frei Γ) (frei Γ + 1)] ρ1.tail :=
          mkPreS (Nat.le_refl _) hp.small hF4 (trav_next hc4) (codeFar_at hp.far (by simp; omega)) (envAt_tail e4)
        have hpw := PreS.welt hq hks w4 hW.lay (by have := hW.lo; omega)
        obtain ⟨m5, s5, a5s, v5, hv5, hve5⟩ := binK_ok (r := BitVec.ofNat 64 k + BitVec.ofInt 64 1) hpw hk4
          (by decide) rfl (by decide) rfl (by omega)
        have hv5' : m5.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (k + 1)) := by
          rw [hv5, hve5, show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 by decide, ← BitVec.ofNat_add]
        have a5 := Agree.widen a5s hks
        have A15 : AgreeW L fp lo K m' m5 := A14.trans (agreeW_of (a5.mono hlo2))
        have hc5 := codeAt_agreeWIn hW A15 hp.code hp.far
        have sj := jmp_go (fp := fp) (trav_back hc5) (lit_ok (by omega) (by omega))
        rw [adr_eq pc (y := 1) (by push_cast; omega)] at sj
        have hp5 : PreS m5 pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ1.tail :=
          mkPreS (Nat.le_refl _) hp.small (frameOK_agreeW hp.frame A15) hc5 hp.far
            (envAt_agree (envAt_tail e4) a5 hF4 (Nat.le_refl _) (by omega))
        have ih5 := ih (k + 1) m5 σ1 ρ1.tail (by omega) hp5 hv5' (hu.agreeW hW A15 hlo)
          (hk.agreeW hW A15 (by omega)) (hpw.wstab m4 m5 w4 (a5s.mono (Nat.zero_le _)))
        have e8 : pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length + cb.1.length)) +
            BitVec.ofNat 64 (16 * [ci 1 (frei Γ + 1) 1 0, ci 3 (frei Γ) (frei Γ) (frei Γ + 1)].length) =
            pc + BitVec.ofNat 64 (16 * (8 + ci'.1.length + cb.1.length)) := by
          rw [addr_norm]; simp only [List.length_cons, List.length_nil]; congr 2; omega
        rw [e8] at s5
        refine Sim.prefix hlo (pre.trans (s4.trans (s5.trans sj))) A15
          (Keeps.trans K12 (Keeps.trans (fun j hj => k4 j (List.mem_cons_of_mem _ hj))
            (keeps_of_agree a5 hF4.room (fun j hj => hpr j hj) (by omega)))) ih5
      generalize execBlock O passes R body (σ'.lese Λ inv.orte) (Env.cons (show Wert D (Ty.index (D.count t)) from x) ρ') = o at hb ⊢
      cases o with
      | ok σ1 ρ1 =>
        obtain ⟨m4, s4, a4, e4, w4, k4⟩ := hb
        exact nx σ1 ρ1 m4 (by rw [← Bend]; exact s4) a4 e4 w4 k4
      | next _ σ1 ρ1 =>
        obtain ⟨m4, s4, a4, e4, w4, k4⟩ := hb
        exact nx σ1 ρ1 m4 (by rw [← Bend]; simpa using s4) a4 e4 w4 k4
      | leave _ σ1 ρ1 =>
        obtain ⟨m4, s4, a4, e4, w4, k4⟩ := hb
        have hLV : pc + BitVec.ofNat 64 (16 * (6 + ci'.1.length)) + BitVec.ofNat 64 (16 * cb.1.length) +
            BitVec.ofInt 64 48 = pc + BitVec.ofNat 64 (16 * (9 + ci'.1.length + cb.1.length)) := by
          rw [Bend]; exact adr_eq pc (by push_cast; omega)
        rw [hLV] at s4
        have A14 : AgreeW L fp lo K m' m4 := (agreeW_of (A12.mono (by omega))).trans a4
        have hc4 := codeAt_agreeWIn hW A14 hp.code hp.far
        have hF4 := frameOK_agreeW hp.frame A14
        have hq : PreS m4 (pc + BitVec.ofNat 64 (16 * (9 + ci'.1.length + cb.1.length))) fp K (frei Γ + 1) ci'.1
            ρ1.tail :=
          mkPreS (by simp only [frei]; omega) hp.small hF4 (trav_inv2 hc4) (codeFar_at hp.far (by omega)) (envAt_tail e4)
        have hpw := PreS.welt hq hks w4 hW.lay (by have := hW.lo; omega)
        obtain ⟨m6, s6, a6s, w', hw', hen'⟩ := lowE_ok (σ1.lese Λ inv.orte) (σ1.lese Λ inv.orte) (fun _ h => h) inv
          _ ci'.1 ci'.2 hci (by omega) m4 _ ρ1.tail hpw
        have hWa6 : WeltAt m6 L σ1 := hpw.wstab m4 m6 w4 (a6s.mono (Nat.zero_le _))
        have a6 := Agree.widen a6s hks
        have A16 : AgreeW L fp lo K m' m6 := A14.trans (agreeW_of (a6.mono (by omega)))
        have hc6 := codeAt_agreeWIn hW A16 hp.code hp.far
        rw [step_eq pc (z := 9 + 2 * ci'.1.length + cb.1.length) (by omega)] at s6
        have K16 : Keeps fp pr m' m6 := Keeps.trans K12 (Keeps.trans (fun j hj => k4 j (List.mem_cons_of_mem _ hj))
          (keeps_of_agree a6 hF4.room (fun j hj => by have := hpr j hj; omega) (by omega)))
        simp only [Enc] at hen'
        dsimp only
        split
        · next hinv =>
          have hw1 : w' = 1 := by rw [hen']; simpa using hinv
          have sb3 := brz_stay (trav_brz3 hc6) (by omega) hp.small hw' (by rw [hw1]; decide)
          rw [step_eq pc (z := 10 + 2 * ci'.1.length + cb.1.length) (by omega)] at sb3
          have sj := jmp_go (fp := fp) (trav_jmp2 hc6) (by decide)
          rw [adr_eq pc (y := 14 + 2 * ci'.1.length + cb.1.length) (by push_cast; omega)] at sj
          rw [hlen]
          exact ⟨m6, pre.trans (s4.trans (s6.trans (sb3.trans sj))), A16,
            envAt_agree (envAt_tail e4) (a6.mono (Nat.le_succ _)) hF4 (Nat.le_refl _) (by omega), hWa6, K16⟩
        · next hinv =>
          have hw0 : w' = 0 := by rw [hen']; simpa using hinv
          have sb3 := brz_go (trav_brz3 hc6) (by omega) hp.small (by decide) (by rw [← hw0]; exact hw')
          rw [adr_eq pc (y := 11 + 2 * ci'.1.length + cb.1.length) (by push_cast; omega)] at sb3
          have hp6 : PreS m6 pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ1.tail :=
            mkPreS (Nat.le_refl _) hp.small (frameOK_agreeW hp.frame A16) hc6 hp.far
              (envAt_agree (envAt_tail e4) (a6.mono (Nat.le_succ _)) hF4 (Nat.le_refl _) (by omega))
          exact Stops.prefix (pre.trans (s4.trans (s6.trans sb3))) (trav_stopped hp6 (by omega))
      | zurueck σ1 v =>
        simp only [Sim] at hb ⊢
        exact RetZ.prefix pre (agreeW_of (A12.mono (by omega))) hb
      | logik e =>
        simp only [Sim] at hb ⊢
        exact Stops.prefix pre hb
      | hardware e =>
        simp only [Sim] at hb ⊢
        exact Stops.prefix pre hb
      | why => exact hb.elim

/-- **`traverse`**: the code of `travC` runs G's `traverseLauf` over all indices. -/
theorem trav_ok (hn : lit32 (D.count t) = true) (hci : lowE L inv (frei Γ + 1) = some ci')
    (hlenc : 16 * (10 + ci'.1.length + cb.1.length) < 2 ^ 31) (hlo0 : lo = FB + (D.params f).length)
    (htop : max ci'.2 (max cb.2 (frei Γ + 9)) ≤ Ks) (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ)
    (hbody : ∀ m' pc' σ' ρ', PreS m' pc' fp K (frei (.index (D.count t) :: Γ)) cb.1 ρ' → Umf A C dv m' fp K →
      Kopf f m' fp K rp cfp ρ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K (frei Γ :: pr) ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cb.1.length))
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 48)
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 0) (execBlock O passes R body σ' ρ'))
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hp : PreS m pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ)
    (hu : Umf A C dv m fp K) (hk : Kopf f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (travCode (frei Γ) (D.count t) ci'.1 cb.1).length)) eL eN
      (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) (alleIndizes (D.count t)) σ ρ) := by
  have hks := hW.ks
  have hroom := hp.frame.room
  have hFB3 : FB = 3 := rfl
  have s0 := const_step (j := frei Γ) (k := 0) (codeAt_left (a := [ci 1 (frei Γ) 0 0]) (by simpa [travCode] using hp.code))
    hp.frame (by omega) hp.small (by decide)
  let m0 := write m (slot fp (BitVec.ofNat 64 (frei Γ))) 8 (BitVec.ofInt 64 (0 : Int)).toNat
  have a0s : Agree fp (frei Γ) Ks m m0 := agree_write (frameOK_sub hp.frame hks).room (Nat.le_refl _) (by omega) _
  have a0 := Agree.widen a0s hks
  have hk0 : m0.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 0) := by
    rw [show BitVec.ofNat 64 0 = BitVec.ofInt 64 (0 : Int) by decide]; exact rd_same hp.frame (by omega) _
  have hp0 : PreS m0 pc fp K (frei Γ) (travCode (frei Γ) (D.count t) ci'.1 cb.1) ρ :=
    mkPreS (Nat.le_refl _) hp.small (hp.frame.agree a0) (hp.code.agree a0 hp.far) hp.far
      (envAt_agree hp.env a0 hp.frame (Nat.le_refl _) (by omega))
  have hl := trav_loop (l := l) (eL := eL) (eN := eN) hn hci hlenc hlo0 htop hW hlo hlo2 hpr hbody
    (D.count t).toNat 0 m0 σ ρ (by omega) hp0 hk0 (hu.agree a0 hp.frame (by omega)) (hk.agree a0 hp.frame (by omega))
    (weltAt_stab hW.lay (by have := hW.lo; omega) m m0 hWa (a0s.mono (Nat.zero_le _)))
  rw [alleIndizes_ab]
  exact Sim.prefix hlo s0 (agreeW_of (a0.mono hlo2))
    (keeps_write hroom (by omega) (fun j hj => by have := hpr j hj; omega) (fun h => by have := hpr _ h; omega) _) hl

end

end Gabbro.Stage0.Senke
