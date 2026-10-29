/-
  File:      stage0/Stage0/Senke/Anweisung/Atomar.lean
  Subject:   The code of `exchange` (`exC`) against G: the global's word into the new variable's slot, the new value
             computed, `cas` of the global from the old word to the new one; one thread alone finds the old word
             still there, so the `cas` takes and the loop does not go round (`ex_tail`). The global then holds G's
             new value, the variable G's old one (`exch_ok`).
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Puffer
import Stage0.Senke.Sperre.Nimm
import Stage0.Senke.Anweisung

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- A word above the frame keeps its value while only the frame's slots change. -/
theorem agree_rd_far {m m' : Runner.Mem} {fp : Runner.W} {lo K x : Nat} (ha : Agree fp lo K m m')
    (hx : fp.toNat + 8 * K ≤ x) (hx2 : x + 8 < 2 ^ 31) :
    m'.rd64 (BitVec.ofNat 64 x) = m.rd64 (BitVec.ofNat 64 x) :=
  rd64_keep ha.rd fun j hj => ha.b _ fun ⟨_, h⟩ => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h; omega

/-- `const d ga; ld d d`: the word at `ga` into slot `d`. -/
theorem glob_word {m : Runner.Mem} {pc fp : Runner.W} {K d ga : Nat} {w0 : Runner.W}
    (hc : CodeAt m pc [ci 1 d ga 0, ci 15 d d 0]) (hcf : CodeFar pc 2 fp K) (hF : FrameOK m fp K) (hd : d < K)
    (hK : K < 2 ^ 31) (hga : m.rd64 (BitVec.ofNat 64 ga) = some w0) (hfar : fp.toNat + 8 * K ≤ ga)
    (hga31 : ga + 8 < 2 ^ 31) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m' ∧ Agree fp d K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w0 := by
  have hc' : CodeAt m pc ([ci 1 d ga 0] ++ [ci 15 d d 0]) := hc
  have s1 := const_step (j := d) (k := (ga : Int)) (codeAt_left hc') hF hd hK (lit32_nat (by omega))
  rw [BitVec.ofInt_natCast] at s1
  have a1 : Agree fp d K m (write m (slot fp (BitVec.ofNat 64 d)) 8 (BitVec.ofNat 64 ga).toNat) :=
    agree_write hF.room (Nat.le_refl _) hd _
  have hF1 := hF.agree a1
  have hc2 := (codeAt_right hc').agree a1 (codeFar_right (n := 1) (k := 1) hcf)
  have hr1 := rd_same hF hd (BitVec.ofNat 64 ga)
  have hv := (agree_rd_far a1 hfar hga31).trans hga
  have a2 := (wr_slot hF1 hd w0).2.2
  have hr2 := (wr_slot hF1 hd w0).2.1
  have hw := (wr_slot hF1 hd w0).1
  generalize write m (slot fp (BitVec.ofNat 64 d)) 8 (BitVec.ofNat 64 ga).toNat = m1 at s1 a1 hF1 hc2 hr1 hv a2 hr2 hw
  generalize write m1 (slot fp (BitVec.ofNat 64 d)) 8 w0.toNat = m2 at a2 hr2 hw
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  rw [← sx_nat (d := d) (by omega)] at hr1 hw
  have s2 := star_ins (fp := fp) hc2 (by simp [ci]) (run_ld (t := ⟨_, fp⟩) hi hr1 hv hw)
  refine ⟨m2, s1.trans (star_cast s2 rfl ?_), a1.trans (a2.mono (Nat.le_refl _)), hr2⟩
  simp only [List.length_singleton, T.mk.injEq, and_true]
  rw [pc_add16 pc 1]

/-- The tail of `exC` when nobody changed the global: `cas` from the old word `old` (slot `s`) to `new` (slot
    `s + 1`) takes, the word read back equals the old one, no jump back. The global holds `new` (as G's
    `storeGlob`), slot `s` still the old word, only slots from `s + 2` and the global changed. -/
theorem ex_tail {L : Lay D} {σ : World D} {g : D.Glob} {v : Wert D (D.gtyp g)} {m : Runner.Mem}
    {pc fp : Runner.W} {K s : Nat} {X : Int} {old new : Runner.W}
    (hc : CodeAt m pc [ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s,
      ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s, ci 19 ((s + 3 : Nat) : Int) X 0])
    (hcf : CodeFar pc 4 fp K) (hF : FrameOK m fp K) (hs : s + 4 ≤ K) (hK : K < 2 ^ 31)
    (h0 : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some old)
    (h1 : m.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some new)
    (hg : m.rd64 (BitVec.ofNat 64 (L.ga g)) = some old) (hWa : WeltAt m L σ) (hl : LayIn L) (hd : LayDis L)
    (hfar : fp.toNat + 8 * K ≤ L.lo) (he : Enc L (D.gtyp g) v new) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 4), fp⟩ m' ∧ AgreeW L fp (s + 2) K m m' ∧
      WeltAt m' L (σ.storeGlob g v) ∧ m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some old := by
  have hgin := hl.2.1 g
  have hhi := hl.2.2
  have hroom := hF.room
  have hga : fp.toNat + 8 * K ≤ L.ga g := by omega
  have hc' : CodeAt m pc ([ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0] ++ ([ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s]
      ++ ([ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s] ++ [ci 19 ((s + 3 : Nat) : Int) X 0]))) := hc
  -- const
  have s1 := const_step (j := s + 2) (k := ((L.ga g : Nat) : Int)) (codeAt_left hc') hF (by omega) hK
    (lit32_nat (by omega))
  rw [BitVec.ofInt_natCast] at s1
  have a1 : Agree fp (s + 2) K m (write m (slot fp (BitVec.ofNat 64 (s + 2))) 8 (BitVec.ofNat 64 (L.ga g)).toNat) :=
    agree_write hroom (Nat.le_refl _) (by omega) _
  have r12 := rd_same hF (a := s + 2) (by omega) (BitVec.ofNat 64 (L.ga g))
  have r10 : (write m (slot fp (BitVec.ofNat 64 (s + 2))) 8 (BitVec.ofNat 64 (L.ga g)).toNat).rd64
      (slot fp (BitVec.ofNat 64 s)) = some old := by
    rw [agree_rd_low a1 hroom (by omega) (by omega)]; exact h0
  have r11 : (write m (slot fp (BitVec.ofNat 64 (s + 2))) 8 (BitVec.ofNat 64 (L.ga g)).toNat).rd64
      (slot fp (BitVec.ofNat 64 (s + 1))) = some new := by
    rw [agree_rd_low a1 hroom (by omega) (by omega)]; exact h1
  have r1g := (agree_rd_far a1 hga (by omega)).trans hg
  have hF1 := hF.agree a1
  have hcf2 := codeFar_right (n := 1) (k := 3) hcf
  have hc2 := (codeAt_right hc').agree a1 hcf2
  have hW1 := weltAt_stab hl hfar m _ hWa (a1.mono (Nat.zero_le _))
  generalize write m (slot fp (BitVec.ofNat 64 (s + 2))) 8 (BitVec.ofNat 64 (L.ga g)).toNat = m1
    at s1 a1 r12 r10 r11 r1g hF1 hc2 hW1
  -- cas
  have hwg : all m1.wr (BitVec.ofNat 64 (L.ga g)) 8 = true := hW1.2.2.word hgin.1 hgin.2 hhi
  have hcas := cas_spec (e := old) (n := new) r1g hwg
  simp only [ite_true] at hcas
  have a2 : AgreeW L fp (s + 2) K m1 (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat) :=
    agreeW_write_welt hgin.1 hgin.2 hhi _
  have hW2 := weltAt_glob hW1 hl hd he
  have hF2 := frameOK_agreeW hF1 a2
  have far2 : ∀ j, j < K → Far (BitVec.ofNat 64 (L.ga g)) 8 (slot fp (BitVec.ofNat 64 j)) 8 := fun j hj => by
    rw [Far, slot_toNat hroom hj, BitVec.toNat_ofNat]; omega
  have r20 : (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat).rd64 (slot fp (BitVec.ofNat 64 s)) = some old := by
    rw [rd64_write_far (far2 s (by omega))]; exact r10
  have hw3 := (wr_slot hF2 (d := s + 3) (by omega) old)
  have hcf3 := codeFar_right (n := 1) (k := 2) hcf2
  have hc3 := codeAt_agreeW a2 (by omega) hhi (by have := hgin; omega) (codeAt_right hc2) hcf3
  have hi2 := hc2 0 (by simp)
  simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi2
  have run2 : Run (op 22 ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩) m1 ⟨pc + BitVec.ofNat 64 (16 * 1) + 16, fp⟩
      (write (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat) (slot fp (BitVec.ofNat 64 (s + 3))) 8 old.toNat) := by
    simp only [op]
    refine f2_run hi2 ?_
    rw [sx_nat (d := s + 2) (by omega)]
    simp only [ld]
    refine run_rd64 r12 ?_
    refine f3_run hi2 ?_
    rw [show ((s : Nat) : Int) = ((s : Nat) : Int) from rfl, sx_nat (d := s) (by omega)]
    refine run_rd64 r10 ?_
    rw [slot_plus8]
    refine run_rd64 r11 ?_
    refine .ask (a := some (old, 0)) (m' := write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat)
      (by simp only [memAns, hcas]) ?_
    simp only [Runner.opt_some, ret1]
    have hc2' := codeAt_agreeW a2 (by omega) hhi (by omega) hc2 hcf2
    have hi2b := hc2' 0 (by simp)
    simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, List.length_singleton] at hi2b
    refine f1_run hi2b ?_
    rw [sx_nat (d := s + 3) (by omega)]
    exact run_wr64 hw3.1
  have s2 : Star ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
      (write (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat) (slot fp (BitVec.ofNat 64 (s + 3))) 8 old.toNat) :=
    star_cast (Star.one (run_step (t := ⟨_, fp⟩) hi2 (by decide) run2)) rfl
      (by simp only [T.mk.injEq, and_true]; exact pc_next pc 1)
  have r33 := hw3.2.1
  have a3 := hw3.2.2
  have r30 : (write (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat) (slot fp (BitVec.ofNat 64 (s + 3))) 8
      old.toNat).rd64 (slot fp (BitVec.ofNat 64 s)) = some old := by
    rw [agree_rd_low a3 hroom (by omega) (by omega)]; exact r20
  have hc3' : CodeAt (write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat) (pc + BitVec.ofNat 64 (16 * 2))
      [ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s, ci 19 ((s + 3 : Nat) : Int) X 0] := by
    have := hc3; rwa [pc_jump] at this
  have hcf3' : CodeFar (pc + BitVec.ofNat 64 (16 * 2)) 2 fp K := by have := hcf3; rwa [pc_jump] at this
  have hc4 := hc3'.agree a3 hcf3'
  have hF3 := hF2.agree a3
  have hW3 := weltAt_stab hl hfar _ _ hW2 (a3.mono (Nat.zero_le _))
  generalize write m1 (BitVec.ofNat 64 (L.ga g)) 8 new.toNat = m2 at s2 a2 hW2 hF2 a3 r33 r30 hc4 hF3 hW3
  generalize write m2 (slot fp (BitVec.ofNat 64 (s + 3))) 8 old.toNat = m3 at s2 a3 r33 r30 hc4 hF3 hW3
  -- eq
  have s3 := bin_star (o := 14) (d := s + 3) (a := s + 3) (b := s) (g := fun a b => some (bool (a == b)))
    (codeAt_left (a := [ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s]) hc4) rfl (by decide) hF3
    (by omega) (by omega) (by omega) hK r33 r30 (r := 1) (by simp [Runner.IR.bool])
  have hw4 := wr_slot hF3 (d := s + 3) (by omega) 1
  have a4 := hw4.2.2
  have r44 := hw4.2.1
  have hcf4 := codeFar_right (n := 1) (k := 1) hcf3'
  have hc5 := (codeAt_right (a := [ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s]) hc4).agree a4 hcf4
  have hW4 := weltAt_stab hl hfar _ _ hW3 (a4.mono (Nat.zero_le _))
  have r40 : (write m3 (slot fp (BitVec.ofNat 64 (s + 3))) 8 (1 : Runner.W).toNat).rd64
      (slot fp (BitVec.ofNat 64 s)) = some old := by
    rw [agree_rd_low a4 hroom (by omega) (by omega)]; exact r30
  generalize write m3 (slot fp (BitVec.ofNat 64 (s + 3))) 8 (1 : Runner.W).toNat = m4 at s3 a4 r44 hc5 hW4 r40
  -- brz, not taken
  have hi5 := hc5 0 (by simp)
  simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi5
  rw [← sx_nat (d := s + 3) (by omega)] at r44
  have s4 := Star.one (run_step (t := ⟨_, fp⟩) hi5 (by decide) (run_brz_ne hi5 r44 (by decide)))
  have s3' : Star ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m3 ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m4 :=
    star_cast s3 rfl (by simp only [List.length_singleton, T.mk.injEq, and_true]; exact pc_jump pc 2 1)
  have s4' : Star ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m4 ⟨pc + BitVec.ofNat 64 (16 * 4), fp⟩ m4 :=
    star_cast s4 (by simp only [List.length_singleton, T.mk.injEq, and_true]; exact pc_jump pc 2 1)
      (by simp only [nxt, List.length_singleton, T.mk.injEq, and_true]; rw [pc_jump, pc_next])
  refine ⟨m4, s1.trans (s2.trans (s3'.trans s4')), ?_, hW4, r40⟩
  · exact (agreeW_of a1).trans (a2.trans (agreeW_of ((a3.trans a4).mono (by omega))))


theorem exC_len (s ga : Nat) (cn : List II) : (exC s ga cn).length = cn.length + 6 := by
  simp only [exC, List.length_append, List.length_cons, List.length_nil]; omega

section
variable {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
  {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
  {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **`exchange`**: what G answers for the block, the code does. -/
theorem exch_head {g : D.Glob} {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {cn cr : List II} {tn : Nat}
    (hn : lowE L neu (frei Γ + 1) = some (cn, tn)) (htn : tn ≤ Ks) (hs4 : frei Γ + 4 ≤ Ks)
    (hW : WIn L fp Ks K) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ) (exC (frei Γ) (L.ga g) cn ++ cr) ρ) (hWa : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length), fp⟩ m' ∧
      AgreeW L fp (frei Γ) K m m' ∧
      PreS L m' (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length)) fp K (frei Γ + 1) cr
        (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) ∧
      WeltAt m' L ((σ.lese Λ (.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
        (σ.lese Λ (.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))) := by
  generalize hsd : frei Γ = s at hn hs4 hp ⊢
  have hfr : frei (D.gtyp g :: Γ) = s + 1 := by simp only [frei, List.length_cons] at hsd ⊢; omega
  have hks := hW.ks
  have hK := hp.small
  have hl := hW.lay
  have hgin := hl.2.1 g
  have hhi := hl.2.2
  have hroom := hp.frame.room
  have hga : fp.toNat + 8 * K ≤ L.ga g := by have := hW.ord; have := hW.top; omega
  have hlen := exC_len s (L.ga g) cn
  have heq : exC s (L.ga g) cn ++ cr = [ci 1 s (L.ga g) 0, ci 15 s s 0] ++ (cn ++ ([ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0] ++ cr)) := by
    simp only [exC, List.append_assoc]
  have hp' := hp
  rw [heq] at hp'
  -- the old word
  obtain ⟨w0, hg0, he0⟩ := hWa.2.1 g
  obtain ⟨m1, s1, a1, r1⟩ := glob_word hp'.left.code hp'.left.far hp.frame (by omega) hK hg0 hga (by omega)
  have hq := hp'.next a1 (Nat.le_refl _) (by omega)
  -- the new value
  have hσ : WeltAt m L (σ.lese Λ (.inr g :: neu.orte)) := hWa
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * 2)) fp K (s + 1) (cn ++ ([ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0] ++ cr))
      (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) :=
    ⟨Nat.le_of_eq hfr, hK, hq.frame, hq.code, hq.far, envAt_cons hq.env (by rw [hsd]; exact r1) he0, trivial,
     wstab_true _ _⟩
  have hpw := PreS.welt hp1.left hks (weltAt_stab hl (by have := hW.top; omega) m m1 hσ (a1.mono (Nat.zero_le _)))
    hl (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, wn, rn, hen⟩ := lowE_ok (σ.lese Λ (.inr g :: neu.orte)) (σ.lese Λ (.inr g :: neu.orte))
    (fun _ h => h) neu (s + 1) cn tn hn htn m1 _ _ hpw
  have a2 := Agree.widen a2s hks
  have hq2 := hq.next (a2.mono (Nat.le_succ s)) (Nat.le_refl _) (by omega)
  have r2 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some w0 := by
    rw [agree_rd_low a2 hroom (by omega) (by omega)]; exact r1
  have g2 : m2.rd64 (BitVec.ofNat 64 (L.ga g)) = some w0 := by
    rw [agree_rd_far a2 hga (by omega), agree_rd_far a1 hga (by omega)]; exact hg0
  have hW2 := hpw.wstab m1 m2 hpw.welt (a2s.mono (Nat.zero_le _))
  -- the tail
  obtain ⟨m3, s3, a3, hW3, r3⟩ := ex_tail (σ := σ.lese Λ (.inr g :: neu.orte)) hq2.left.code hq2.left.far
    hq2.frame (by omega) hK r2 rn g2 hW2 hl hW.dis (by have := hW.top; omega) hen
  have hq3 := Pre.nextW hW hq2 a3 (by omega) (Nat.le_refl _) (by omega)
  have A : AgreeW L fp s K m m3 :=
    (agreeW_of (a1.trans (a2.mono (by omega)))).trans (a3.mono (by omega))
  have e3 : pc + BitVec.ofNat 64 (16 * [ci 1 s (L.ga g) 0, ci 15 s s 0].length) + BitVec.ofNat 64 (16 * cn.length) +
      BitVec.ofNat 64 (16 * [ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0].length) =
      pc + BitVec.ofNat 64 (16 * (exC s (L.ga g) cn).length) := by
    simp only [List.length_cons, List.length_nil]
    rw [pc_jump, pc_jump, hlen]; congr 2; omega
  have hp3 : PreS L m3 (pc + BitVec.ofNat 64 (16 * (exC s (L.ga g) cn).length)) fp K (s + 1) cr
      (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) := by
    rw [← e3]
    exact ⟨Nat.le_of_eq hfr, hq3.small, hq3.frame, hq3.code, hq3.far, envAt_cons hq3.env (by rw [hsd]; exact r3) he0,
      trivial, wstab_true _ _⟩
  exact ⟨m3, s1.trans (s2.trans (star_cast s3 rfl (by rw [← e3]; rfl))), A, hp3, hW3⟩

theorem exch_ok {g : D.Glob} {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)}
    {hw : (vertragVon D f).gschreibt g = true} {hL : gdarf D g Λ}
    {rest : Block D (vertragVon D f) l (D.gtyp g :: Γ) Λ Λ'} {cn cr : List II} {tn : Nat}
    (hn : lowE L neu (frei Γ + 1) = some (cn, tn)) (htn : tn ≤ Ks) (hs4 : frei Γ + 4 ≤ Ks)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hrest : ∀ m' σ' (ρ' : Env D (D.gtyp g :: Γ)),
      PreS L m' (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length)) fp K (frei Γ + 1) cr ρ' →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length), fp⟩ m'
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length))
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length) +
          BitVec.ofInt 64 ex.1)
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length) +
          BitVec.ofInt 64 ex.2)
        (execBlock O passes R rest σ' ρ'))
    (hp : PreS L m pc fp K (frei Γ) (exC (frei Γ) (L.ga g) cn ++ cr) ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn ++ cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (exC (frei Γ) (L.ga g) cn ++ cr).length) + BitVec.ofInt 64 ex.2)
      (execBlock O passes R (.exchange g neu hw hL rest) σ ρ) := by
  obtain ⟨m3, s3, A, hp3, hW3⟩ := exch_head (Λ := Λ) hn htn hs4 hW hp hWa
  have ih := hrest m3 _ _ hp3 (hu.agreeW hW (A.mono hlo2) hlo) (hk.agreeW hW (A.mono hlo2) (by omega)) hW3
  simp only [execBlock]
  rw [pc_add1]
  exact Sim.prefix hlo s3 (A.mono hlo2) (keeps_of_agreeW hW A hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)

/-- The load of `awaits`: the global's word into the new variable's slot. -/
theorem awaits_head {reserved : Nat} {g : D.Glob} {cr : List II} (hl : lit32 (L.ga g) = true) (hs1 : frei Γ reserved + 1 ≤ Ks)
    (hW : WIn L fp Ks K) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved) ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr) ρ reserved)
    (hWa : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m' ∧ AgreeW L fp (frei Γ reserved) K m m' ∧
      PreS L m' (pc + BitVec.ofNat 64 (16 * 2)) fp K (frei Γ reserved + 1) cr (Env.cons (σ.globs g) ρ) reserved ∧ WeltAt m' L σ := by
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := glob_ok (σ := σ) hl hpw (fun _ h => h) (by omega)
  have a1 := Agree.widen a1s hks
  have hq := hp.next a1 (Nat.le_refl _) (by have := hp.small; omega)
  exact ⟨m1, s1, agreeW_of a1, ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
    envAt_cons hq.env hw hen, trivial, wstab_true _ _⟩, hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))⟩

/-- **`awaits`**: the publication is visible (`SichtOK`); the global's word is the new variable. -/
theorem awaits_ok [SichtOK O] {g : D.Glob} {pl : List D.Glob} {hpl : pl = D.nutzlast g} {hL : gdarf D g Λ}
    {hat : D.atomar g = true} {rest : Block D (vertragVon D f) l (D.gtyp g :: Γ) Λ Λ'} {cr : List II}
    (hl : lit32 (L.ga g) = true) (hs1 : frei Γ + 1 ≤ Ks)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hrest : ∀ m' σ' (ρ' : Env D (D.gtyp g :: Γ)),
      PreS L m' (pc + BitVec.ofNat 64 (16 * 2)) fp K (frei Γ + 1) cr ρ' →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m'
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length))
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2)
        (execBlock O passes R rest σ' ρ'))
    (hp : PreS L m pc fp K (frei Γ) ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr).length) +
        BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ) (L.ga g) 0, ci 15 (frei Γ) (frei Γ) 0] ++ cr).length) +
        BitVec.ofInt 64 ex.2)
      (execBlock O passes R (.awaits g pl hpl hL hat rest) σ ρ) := by
  simp only [execBlock, SichtOK.sicht, ↓reduceIte]
  obtain ⟨m1, s1, A, hp1, hW1⟩ := awaits_head hl hs1 hW hp hWa
  have ih := hrest m1 ((σ.fragt (.inr (.inr g))).lese Λ [.inr g]) _ hp1
    (hu.agreeW hW (A.mono hlo2) hlo) (hk.agreeW hW (A.mono hlo2) (by omega)) hW1
  rw [pc_add1]
  exact Sim.prefix hlo s1 (A.mono hlo2) (keeps_of_agreeW hW A hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)

end

end Gabbro.Stage0.Senke
