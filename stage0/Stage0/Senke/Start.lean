/-
  File:      stage0/Stage0/Senke/Start.lean
  Subject:   A thread's start (`start_ok`): from its start code (`startC`) in a frame of its own, the thread runs its
             root as G's `rufAt n` and ends with the system call `e` (`exit_group` with `main`'s result, `exit` for a
             root), or with the stop of G's outcome.
-/
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The system call `nr` with the word of slot `r`. -/
theorem exitw_ok {m : Runner.Mem} {pc fp : Runner.W} {K nr s r : Nat} {w : Runner.W}
    (hc : CodeAt m pc [ci 1 s nr 0, ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0])
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hr : r < s) (hK : K < 2 ^ 31)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 r)) = some w) (hnr : nr < 2 ^ 31) :
    ∃ t' m' q, Star ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 nr ∧ q.a1 = w := by
  have hroom := hF.room
  have s1 := const_step (k := (nr : Int)) (codeAt_left (a := [ci 1 s nr 0]) hc) hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (nr : Int)).toNat
  have a1 : Agree fp 0 K m m1 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc1 : CodeAt m1 (pc + 16) [ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 s nr 0]) hc).agree a1 (codeFar_right (n := 1) (k := 2) hf)
    simpa using this
  have hF1 := hF.agree a1
  have hw1 : m1.rd64 (slot fp (BitVec.ofNat 64 r)) = some w := by
    simp only [m1]; rw [rd_other hroom (by omega) (by omega) (by omega)]; exact hw
  have s2 := mov_to (codeAt_left (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1) hF1 (j := s + 1) (s := r) (by omega)
    (by omega) hK hw1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 w.toNat
  have a2 : Agree fp 0 K m1 m2 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1).agree a2 (by
      have := codeFar_right (n := 2) (k := 1) hf
      simp only [List.length_singleton, Nat.mul_one]
      rw [BitVec.add_assoc, show (16 : Runner.W) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 2) by decide]
      exact this)
    simpa using this
  have hF2 := hF1.agree a2
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hsx : sx (II.f (s : Int)) = BitVec.ofNat 64 s := sx_nat (by omega)
  have r0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 (nr : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr s (by omega))) (hF.rd s (by omega))
  have r1 : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some w :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have rd : ∀ i, i < 7 → ∃ v, m2.rd64 (slot fp (BitVec.ofNat 64 (s + i))) = some v := fun i hi =>
    ⟨_, by simp only [Runner.Mem.rd64, hF2.rd (s + i) (by omega), ↓reduceIte]; rfl⟩
  obtain ⟨v2, r2⟩ := rd 2 (by decide)
  obtain ⟨v3, r3⟩ := rd 3 (by decide)
  obtain ⟨v4, r4⟩ := rd 4 (by decide)
  obtain ⟨v5, r5⟩ := rd 5 (by decide)
  obtain ⟨v6, r6⟩ := rd 6 (by decide)
  refine ⟨_, m2, ⟨BitVec.ofInt 64 (nr : Int), w, v2, v3, v4, v5, v6⟩, s1.trans s2,
    runTo_sys (t := ⟨pc + 16 + 16, fp⟩) hi (by rw [hsx]; exact r0) ?_ ?_ ?_ ?_ ?_ ?_, by rw [BitVec.ofInt_natCast], rfl⟩
  · rw [hsx, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]; exact r1
  · rw [hsx, show (16 : Runner.W) = BitVec.ofNat 64 (8 * 2) by rfl, slot_plus]; exact r2
  · rw [hsx, show (24 : Runner.W) = BitVec.ofNat 64 (8 * 3) by rfl, slot_plus]; exact r3
  · rw [hsx, show (32 : Runner.W) = BitVec.ofNat 64 (8 * 4) by rfl, slot_plus]; exact r4
  · rw [hsx, show (40 : Runner.W) = BitVec.ofNat 64 (8 * 5) by rfl, slot_plus]; exact r5
  · rw [hsx, show (48 : Runner.W) = BitVec.ofNat 64 (8 * 6) by rfl, slot_plus]; exact r6

theorem encErg_none' {e : Option Ty} (h : e = none) (v : ErgVal D e) (w : Runner.W) : EncErg e v w := by
  subst h; trivial

theorem codeFar_nat' {a k f K : Nat} (ha : a + 16 * k ≤ f) (hf : f + 8 * K < 2 ^ 64) :
    CodeFar (BitVec.ofNat 64 a) k (BitVec.ofNat 64 f) K := by
  simp only [CodeFar, BitVec.toNat_ofNat]
  omega

/-- **A thread's start**: from its start code at `pc` in its frame at `fpI` (`Ks` slots, the world above), the thread
    runs `f` as G's `rufAt n f` and ends with the system call `e` -- with `f`'s result when `keep` -- or with the stop
    of G's outcome. -/
theorem start_ok {P : Programm D} {O : Orakel D} {passes : Nat} {Y : Lay D} [hT : TorOK Y O] {A : D.Fn → Nat}
    {C : D.Fn → List II} {L Ks n : Nat} {f : D.Fn} {e : Nat} {keep : Bool}
    (hC : ∀ g, ∃ top, lowFun P A Y g = some (C g, top) ∧ top ≤ L) (hAlt : ∀ g, A g < 2 ^ 31)
    (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) (hpar : (D.params f).isEmpty = true)
    (hroomK : FB + 2 * L ≤ Ks) (hexK : exitSlot + 8 ≤ Ks) (hL1 : 1 ≤ L) (hn : n = depthOf Ks L) (he : e < 2 ^ 31)
    {pc fpI : Nat} {m : Runner.Mem} (hfit : fpI + 8 * Ks < 2 ^ 31)
    (hc : CodeAt m (BitVec.ofNat 64 pc) (startC A f n e keep)) (hpc : pc + 16 * startLen ≤ fpI)
    (hF : FrameOK m (BitVec.ofNat 64 fpI) Ks) (hP : PCode m A C (BitVec.ofNat 64 fpI) Ks)
    (hW : WIn Y (BitVec.ofNat 64 fpI) Ks Ks) (σ : World D) (ρ : Env D (D.params f)) (hWa : WeltAt m Y σ) :
    match rufAt P O passes n f σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = BitVec.ofNat 64 e ∧ (keep = true → EncErg (D.erg f) v q.a1)
    | .logik l => Stops ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m (logikCode l)
    | .hardware h => Stops ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m (hwCode h)
    | _ => False := by
  have hFB3 : FB = 3 := rfl
  have hex : exitSlot = 8 := rfl
  have hsl : startLen = 8 := rfl
  have hK : Ks < 2 ^ 31 := by omega
  have hroom := hF.room
  -- the depth
  have hq : 2 ≤ (Ks - FB) / L := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hn1 : n + 1 = (Ks - FB) / L := by rw [hn, depthOf]; omega
  have hdm := Nat.div_mul_le_self (Ks - FB) L
  have hnK : n + 1 ≤ Ks := by have := Nat.div_le_self (Ks - FB) L; omega
  have hS := lowFun_spec (Y := Y) (P := P) (O := O) (passes := passes) hC hAlt hlen n (by omega)
  have hS0' : CodeAt m (BitVec.ofNat 64 pc) ([ci 1 2 ((n + 1 : Nat) : Int) 0] ++ (callTail A f FB ++
      [ci 1 exitSlot e 0,
       if keep && (D.erg f).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
       ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0])) := by
    simpa [startC, List.append_assoc] using hc
  have s1 := const_step (j := 2) (k := ((n + 1 : Nat) : Int)) (codeAt_left hS0') hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 2)) 8 (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat
  have a1 : Agree (BitVec.ofNat 64 fpI) 2 Ks m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hfp0 : (BitVec.ofNat 64 fpI).toNat = fpI := by simp only [BitVec.toNat_ofNat]; omega
  have hWa1 : WeltAt m1 Y σ := weltAt_stab hW.lay hW.top m m1 hWa (a1.mono (Nat.zero_le _))
  have hfC : CodeFar (BitVec.ofNat 64 pc + BitVec.ofNat 64 (16 * [ci 1 2 ((n + 1 : Nat) : Int) 0].length))
      (callTail A f FB ++ [ci 1 exitSlot e 0,
       if keep && (D.erg f).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
       ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0]).length (BitVec.ofNat 64 fpI) Ks := by
    rw [ofNat_add64]; exact codeFar_nat' (by simp [callTail]; omega) (by omega)
  have hc1 := (codeAt_right hS0').agree a1 hfC
  have hdv : m1.rd64 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 n + 1) := by
    have hconv : BitVec.ofInt 64 ((n + 1 : Nat) : Int) = BitVec.ofNat 64 n + 1 := by
      rw [BitVec.ofInt_natCast]; exact ofNat_succ n
    simp only [m1]
    rw [rd_same hF (by omega), hconv]
  have hnp : (D.params f).length = 0 := by simpa using hpar
  have hE : EnvAt m1 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 FB)) ρ := fun τ x => by
    have := idx_lt x; omega
  have hcall := call_ok (σ := σ) hS (codeAt_left hc1) (codeFar_left (k := 3) (by
      have h4 : (callTail A f FB).length = 4 := rfl; simpa [h4] using hfC)) hF1 hK (Nat.le_refl _)
    (by omega) (by rw [hn1]; omega) (hAlt f) (pcode_agree hP a1) hdv hE hW hWa1
  generalize rufAt P O passes n f σ ρ = o at hcall ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m2, s2, a2, ⟨w, hw, hew⟩, _⟩ := hcall
    have hfE := codeFar_tail (a := callTail A f FB) hfC
    have hexC := codeAt_agreeWIn hW (a2.mono (Nat.zero_le _)) (codeAt_right (a := callTail A f FB) hc1) hfE
    have hF2 := frameOK_agreeW hF1 a2
    by_cases hs : (keep && (D.erg f).isSome) = true
    · simp only [hs, ite_true] at hexC hfE
      obtain ⟨t', m', q, sx, hq, hnr, ha⟩ := exitw_ok hexC hfE hF2 (by omega) (by omega) hK hw he
      refine ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr, fun _ => by rw [ha]; exact hew⟩
    · simp only [hs, Bool.false_eq_true, ite_false] at hexC hfE
      obtain ⟨t', m', q, sx, hq, hnr, _⟩ := sys_ok (nr := e) (c := 0) (s := exitSlot) hexC hfE hF2 (by omega) hK
        (by decide) he
      refine ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr, fun hk => ?_⟩
      simp only [hk, Bool.true_and, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hs
      exact encErg_none' hs v _
  | logik l => exact Stops.prefix s1 hcall
  | why _ _ => exact hcall.elim
  | hardware h => exact Stops.prefix s1 hcall

/-! ## `main` starts the roots -/

/-- **The named assumption at `clone`**: the kernel answers the thread that asks for a new thread with the new
    thread's id (not 0) and leaves the memory as it is. -/
class CloneOK : Prop where
  ans : ∀ m : Runner.Mem, ∃ r x : Runner.W, r ≠ 0 ∧ Kern.ans cloneReq m (some (r, x)) m

/-- One `spawn`: the start code's address and the frame's address into `exitSlot`, `exitSlot + 1`; the new thread's
    id into `exitSlot + 2`; the asking thread goes on. -/
theorem spawn1_ok [CloneOK] {m : Runner.Mem} {pc fp : Runner.W} {K a f : Nat}
    (hc : CodeAt m pc [ci 1 exitSlot a 0, ci 1 ((exitSlot + 1 : Nat) : Int) f 0,
      ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0]) (hF : FrameOK m fp K) (hK : exitSlot + 3 ≤ K)
    (hK2 : K < 2 ^ 31) (ha : a < 2 ^ 31) (hf : f < 2 ^ 31) (hcf : CodeFar pc 3 fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m' ∧ Agree fp exitSlot K m m' := by
  have hex : exitSlot = 8 := rfl
  have hroom := hF.room
  have hc' : CodeAt m pc ([ci 1 exitSlot a 0] ++ ([ci 1 ((exitSlot + 1 : Nat) : Int) f 0] ++
      [ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0])) := hc
  have s1 := const_step (k := (a : Int)) (codeAt_left hc') hF (by omega) hK2
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 exitSlot)) 8 (BitVec.ofInt 64 (a : Int)).toNat
  have a1 : Agree fp exitSlot K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hc1 := (codeAt_right hc').agree a1 (codeFar_right (n := 1) (k := 2) hcf)
  have s2 := const_step (j := exitSlot + 1) (k := (f : Int)) (codeAt_left hc1) hF1 (by omega) hK2
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (exitSlot + 1))) 8 (BitVec.ofInt 64 (f : Int)).toNat
  have a2 : Agree fp exitSlot K m1 m2 := agree_write hroom (by omega) (by omega) _
  have hF2 := hF1.agree a2
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0] := by
    have := (codeAt_right (a := [ci 1 exitSlot a 0, ci 1 ((exitSlot + 1 : Nat) : Int) f 0])
      (b := [ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0]) hc).agree (a1.trans a2) (codeFar_right (n := 2) (k := 1) hcf)
    rwa [show pc + BitVec.ofNat 64 (16 * [ci 1 exitSlot a 0, ci 1 ((exitSlot + 1 : Nat) : Int) f 0].length) =
      pc + 16 + 16 by rw [BitVec.add_assoc]; rfl] at this
  obtain ⟨r, x, hr0, hk⟩ := CloneOK.ans m2
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have h0 : m2.rd64 (slot fp (BitVec.ofNat 64 exitSlot)) = some (BitVec.ofInt 64 (a : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr _ (by omega))) (hF.rd _ (by omega))
  have h1 : m2.rd64 (slot fp (BitVec.ofNat 64 exitSlot) + 8) = some (BitVec.ofInt 64 (f : Int)) := by
    rw [show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]
    exact rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have s3 : Star ⟨pc + 16 + 16, fp⟩ m2 ⟨pc + 16 + 16 + 16, fp⟩
      (write m2 (slot fp (BitVec.ofNat 64 (exitSlot + 2))) 8 r.toNat) := by
    refine Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) ?_)
    simp only [op]
    refine f2_run (t := ⟨_, fp⟩) hi ?_
    rw [sx_nat (by omega)]
    simp only [ld]
    refine run_rd64 h0 (run_rd64 h1 ?_)
    refine Run.sys (a := some (r, x)) (m' := m2) hk ?_
    simp only [Runner.opt, hr0, ↓reduceIte, ret1]
    refine f1_run (t := ⟨_, fp⟩) hi ?_
    rw [sx_nat (by omega)]
    exact run_wr64 (wr64_some (hF2.wr _ (by omega)))
  refine ⟨_, s1.trans (s2.trans (star_cast s3 rfl ?_)), a1.trans (a2.trans (agree_write hroom (by omega)
    (by omega) _))⟩
  simp only [T.mk.injEq, and_true]
  rw [show (16 : Runner.W) = BitVec.ofNat 64 16 from rfl, addr_norm, addr_norm]

/-- The spawns of all roots. -/
theorem spawnC_ok [CloneOK] {fp : Runner.W} {K : Nat} (hK : exitSlot + 3 ≤ K) (hK2 : K < 2 ^ 31) :
    (l : List (Nat × Nat)) → (∀ x ∈ l, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31) → (m : Runner.Mem) → (pc : Runner.W) →
    CodeAt m pc (spawnC l) → FrameOK m fp K → CodeFar pc (spawnC l).length fp K →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (spawnC l).length), fp⟩ m' ∧ Agree fp exitSlot K m m'
  | [], _, m, pc, _, _, _ => ⟨m, by simpa [spawnC] using Star.refl _ m, Agree.refl _ _ _ _⟩
  | (a, f) :: r, hl, m, pc, hc, hF, hcf => by
    have h0 := hl (a, f) (by simp)
    have hc' : CodeAt m pc ([ci 1 exitSlot a 0, ci 1 ((exitSlot + 1 : Nat) : Int) f 0,
        ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0] ++ spawnC r) := hc
    have hcf' : CodeFar pc (3 + (spawnC r).length) fp K := by
      have h := hcf
      simp only [spawnC, List.length_append, List.length_cons, List.length_nil] at h
      rwa [show 0 + 1 + 1 + 1 + (spawnC r).length = 3 + (spawnC r).length by omega] at h
    obtain ⟨m1, s1, a1⟩ := spawn1_ok (codeAt_left hc') hF hK hK2 h0.1 h0.2 (codeFar_left hcf')
    have hc1 := (codeAt_right hc').agree a1 (codeFar_right hcf')
    obtain ⟨m2, s2, a2⟩ := spawnC_ok hK hK2 r (fun x hx => hl x (by simp [hx])) m1 _ hc1 (hF.agree a1)
      (codeFar_right hcf')
    refine ⟨m2, s1.trans (star_cast s2 (by simp) ?_), a1.trans a2⟩
    simp only [T.mk.injEq, and_true, spawnC, List.length_append, List.length_cons, List.length_nil, addr_norm]
    congr 2
    omega

end Gabbro.Stage0.Senke
