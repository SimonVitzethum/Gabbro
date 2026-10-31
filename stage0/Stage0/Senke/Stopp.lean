/-
  File:      stage0/Stage0/Senke/Stopp.lean
  Subject:   Stops: a logic outcome of G ends the process; in IR, `exit_group` with a code per kind.

  `stopC c s` writes 231 (`exit_group`) into slot `s` and the code `c` into slot `s+1` and asks the kernel with
  the slots `s .. s+6`; the other arguments are whatever the slots hold (`exit_group` reads only its first).
  `stop_ok`: the IR thread runs the two constants and stands at the request `exit_group(c)`.
-/
import Stage0.Senke.Umgebung

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The exit code of a logic outcome: 100 + its kind. -/
def logikCode : Logik D → Nat
  | .vorbedingung _ => 101
  | .nachbedingung _ => 102
  | .invariante _ => 103
  | .schleife => 104
  | .abstieg _ => 105
  | .vorzustand => 106
  | _ => 107

/-- The exit code of a hardware outcome: 110 + its kind. -/
def hwCode : Hardware D → Nat
  | .annahme _ => 110
  | .fortschritt _ => 111
  | .ieee => 112
  | .register _ => 113
  | .geraet _ => 114
  | .sichtbarkeit _ => 115

/-- The system call `nr` with first argument `c`, its request block at slot `s`. -/
def sysC (nr c s : Nat) : List II := [ci 1 s nr 0, ci 1 ((s + 1 : Nat) : Int) c 0, ci 23 ((s + 7 : Nat) : Int) s 0]

def stopC (c s : Nat) : List II := sysC 231 c s

/-- The thread at `t` stops with `exit_group(c)` after zero or more instructions. -/
def Stops (t : T) (m : Runner.Mem) (c : Nat) : Prop :=
  ∃ t' m' q, Star t m t' m' ∧ StopAt t' m' q ∧ q.nr = 231 ∧ q.a1 = BitVec.ofNat 64 c

theorem Stops.prefix {t t' : T} {m m' : Runner.Mem} {c : Nat} (h : Star t m t' m') (hs : Stops t' m' c) :
    Stops t m c := by
  obtain ⟨u, mu, q, hu, hq, h1, h2⟩ := hs
  exact ⟨u, mu, q, h.trans hu, hq, h1, h2⟩

theorem const_instruction {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {k : Int}
    (hc : CodeAt m pc [ci 1 j k 0]) (hF : FrameOK m fp K) (hj : j < K) (hK : K < 2 ^ 31) (hk : lit32 k = true) :
    Run (step ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 j)) 8 (BitVec.ofInt 64 k).toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine run_step (t := ⟨pc, fp⟩) hi (by decide) ?_
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_lit hk, sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr j hj))

theorem const_step {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {k : Int}
    (hc : CodeAt m pc [ci 1 j k 0]) (hF : FrameOK m fp K) (hj : j < K) (hK : K < 2 ^ 31) (hk : lit32 k = true) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 j)) 8 (BitVec.ofInt 64 k).toNat) :=
  Star.one (const_instruction hc hF hj hK hk)

theorem slot_plus (fp : Runner.W) (s i : Nat) :
    slot fp (BitVec.ofNat 64 s) + BitVec.ofNat 64 (8 * i) = slot fp (BitVec.ofNat 64 (s + i)) := by
  simp only [slot]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h8 : (8 : Runner.W).toNat = 8 := rfl
  rw [h8]
  omega

/-- The thread stands at the request `nr (c, ..)` after the two constants. -/
theorem sys_ok {m : Runner.Mem} {pc fp : Runner.W} {K nr c s : Nat} (hc : CodeAt m pc (sysC nr c s))
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31) (hcode : c < 2 ^ 31)
    (hnr : nr < 2 ^ 31) :
    ∃ t' m' q, Star ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 nr ∧ q.a1 = BitVec.ofNat 64 c := by
  have hroom := hF.room
  -- the two constants
  have s1 := const_step (k := (nr : Int)) (codeAt_left (a := [ci 1 s nr 0]) hc) hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (nr : Int)).toNat
  have a1 : Agree fp 0 K m m1 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc1 : CodeAt m1 (pc + 16) [ci 1 ((s + 1 : Nat) : Int) c 0, ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 s nr 0]) hc).agree a1 (codeFar_right (n := 1) (k := 2) hf)
    simpa using this
  have hF1 := hF.agree a1
  have s2 := const_step (j := s + 1) (k := c) (codeAt_left (a := [ci 1 ((s + 1 : Nat) : Int) c 0]) hc1) hF1 (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 (BitVec.ofInt 64 c).toNat
  have a2 : Agree fp 0 K m1 m2 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 ((s + 1 : Nat) : Int) c 0]) hc1).agree a2 (by
      have := codeFar_right (n := 2) (k := 1) hf
      simp only [List.length_singleton, Nat.mul_one]
      rw [BitVec.add_assoc, show (16 : Runner.W) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 2) by decide]
      exact this)
    simpa using this
  have hF2 := hF1.agree a2
  -- the request
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hsx : sx (II.f (s : Int)) = BitVec.ofNat 64 s := sx_nat (by omega)
  have r0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 (nr : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr s (by omega))) (hF.rd s (by omega))
  have r1 : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some (BitVec.ofInt 64 c) :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have rd : ∀ i, i < 7 → ∃ v, m2.rd64 (slot fp (BitVec.ofNat 64 (s + i))) = some v := fun i hi =>
    ⟨_, by simp only [Runner.Mem.rd64, hF2.rd (s + i) (by omega), ↓reduceIte]; rfl⟩
  obtain ⟨v2, r2⟩ := rd 2 (by decide)
  obtain ⟨v3, r3⟩ := rd 3 (by decide)
  obtain ⟨v4, r4⟩ := rd 4 (by decide)
  obtain ⟨v5, r5⟩ := rd 5 (by decide)
  obtain ⟨v6, r6⟩ := rd 6 (by decide)
  refine ⟨_, m2, ⟨BitVec.ofInt 64 (nr : Int), BitVec.ofInt 64 c, v2, v3, v4, v5, v6⟩, s1.trans s2,
    runTo_sys (t := ⟨pc + 16 + 16, fp⟩) hi (by rw [hsx]; exact r0) ?_ ?_ ?_ ?_ ?_ ?_,
    by rw [BitVec.ofInt_natCast], ?_⟩
  · rw [hsx, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]; exact r1
  · rw [hsx, show (16 : Runner.W) = BitVec.ofNat 64 (8 * 2) by rfl, slot_plus]; exact r2
  · rw [hsx, show (24 : Runner.W) = BitVec.ofNat 64 (8 * 3) by rfl, slot_plus]; exact r3
  · rw [hsx, show (32 : Runner.W) = BitVec.ofNat 64 (8 * 4) by rfl, slot_plus]; exact r4
  · rw [hsx, show (40 : Runner.W) = BitVec.ofNat 64 (8 * 5) by rfl, slot_plus]; exact r5
  · rw [hsx, show (48 : Runner.W) = BitVec.ofNat 64 (8 * 6) by rfl, slot_plus]; exact r6
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

theorem stop_ok {m : Runner.Mem} {pc fp : Runner.W} {K c s : Nat} (hc : CodeAt m pc (stopC c s))
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31) (hcode : c < 2 ^ 31) :
    Stops ⟨pc, fp⟩ m c := by
  obtain ⟨t', m', q, h1, h2, h3, h4⟩ := sys_ok hc hf hF hs hK hcode (by decide)
  exact ⟨t', m', q, h1, h2, by rw [h3]; rfl, h4⟩

/-- `brz a` over a stop: if slot `a` is zero, `exit_group(c)`; else on after it. -/
def guardC (a c s : Nat) : List II := [ci 19 a 32 0, ci 18 64 0 0] ++ stopC c s

end Gabbro.Stage0.Senke
