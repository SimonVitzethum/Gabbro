module

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil4

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

/-- Both large paths skip the SMALL code using the emitted jump. -/
theorem floatNormalizeLoopL_large_skip_small
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (fetch : CodeAt m pc code) :
    Run (step ⟨pc+336, fp⟩) m
      ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m := by
  have shape : 21 < code.length ∧ 25 ≤ code.length ∧
      code[21]? = some (ci 18 (16*((code.length-25 : Nat) : Int)) 0 0) ∧
      lit32 (16*((code.length-25 : Nat) : Int)) = true := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2, lit32]
  have entry : code[21] = ci 18 (16*((code.length-25 : Nat) : Int)) 0 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2.2.1
  have ins := fetch 21 shape.1
  rw [entry] at ins
  have run := run_step (t := ⟨pc+336, fp⟩) ins (by simp [ci]) (run_jmp ins)
  have offset : sx (II.f (16*((code.length-25 : Nat) : Int))) =
      BitVec.ofNat 64 (16*(code.length-25)) := by
    rw [sx_lit shape.2.2.2]
    rw [show 16*((code.length-25 : Nat) : Int) = ((16*(code.length-25) : Nat) : Int) by omega,
      BitVec.ofInt_natCast]
  have total : 336 + 16*(code.length-25) = 16*(code.length-4) := by omega
  have sum : (336 : Runner.W) + BitVec.ofNat 64 (16*(code.length-25)) =
      BitVec.ofNat 64 (16*(code.length-4)) := by
    change BitVec.ofNat 64 336 + _ = _
    rw [← BitVec.ofNat_add, total]
  simpa only [ci, offset, BitVec.add_assoc, sum] using run

#print axioms floatNormalizeLoopL_large_skip_small

/-- Actual execution of both large paths from the established prefix through
    carry arithmetic and the emitted jump to the shared tail. -/
theorem floatNormalizeLoopL_large_to_tail
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+8 < K) (large : 61 < distance) (active : q < target) :
    let carry : Runner.W := if distance-1 < 63 then
      1 - Runner.IR.bool (decide (r < (2 : Int)^(distance-1))) else 0
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q) + carry) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
        some (BitVec.ofInt 64 r - BitVec.ofInt 64 ((2 : Int)^(distance-1))*carry) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) := by
  dsimp only
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds, tested, den⟩ :=
    floatNormalizeLoopL_large_carry_tested hc head (by omega) large active
  by_cases guarded : distance-1 < 63
  · obtain ⟨m2, run2, ag2, pre2, rq2, rr2, kept⟩ :=
      floatNormalizeLoopL_large_carry_arithmetic hc pre1 room _ _ _ _ rq rr
        (den guarded) (tested guarded)
    have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+256, fp⟩ m1 := by
      simpa only [guarded, ↓reduceIte] using run1
    refine ⟨m2, connectedPrefix.trans (run2.trans (Star.one
      (floatNormalizeLoopL_large_skip_small hc pre2.code))), ag1.trans ag2, pre2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [guarded, ↓reduceIte] using rq2
    · simpa only [guarded, ↓reduceIte] using rr2
    · rw [kept (base+2) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rd
    · rw [kept (base+3) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rt
    · rw [kept (base+4) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rf
    · rw [kept (base+5) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rc
  · have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+336, fp⟩ m1 := by
      simpa only [guarded, ↓reduceIte] using run1
    refine ⟨m1, connectedPrefix.trans (Star.one
      (floatNormalizeLoopL_large_skip_small hc pre1.code)), ag1, pre1,
      ?_, ?_, rd, rt, rf, rc⟩
    · simpa [guarded] using rq
    · simpa [guarded] using rr

#print axioms floatNormalizeLoopL_large_to_tail

/-- The actual large-path words denote the canonical integer transfer.
    This connects execution to reconstruction rather than assuming a body. -/
theorem floatNormalizeLoopL_large_canonical_output
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+8 < K) (large : 61 < distance) (active : q < target) :
    let c : Int := if r < (2 : Int)^(distance-1) then 0 else 1
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q+c)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
        some (BitVec.ofInt 64 (r-c*(2 : Int)^(distance-1))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      (0 ≤ 2*q+c ∧ 2*q+c < 2^61) ∧
      (0 ≤ r-c*(2 : Int)^(distance-1) ∧ r-c*(2 : Int)^(distance-1) < 2^63 ∧
        r-c*(2 : Int)^(distance-1) < (2 : Int)^(distance-1)) ∧
      ((2*q+c)*(2 : Int)^(distance-1) + (r-c*(2 : Int)^(distance-1))) *
        (2 : Int)^originDistance = origin * (2 : Int)^(count+distance) := by
  dsimp only
  have dk : distance-1+1 = distance := by omega
  have transfer := floatNormalizeLoop_large_word_transfer q r target (distance-1)
    head.quotient.1 active head.targetBound.2 ⟨head.remainder.1, head.remainder.2.1⟩
    (by simpa only [dk] using head.remainder.2.2)
  dsimp only at transfer
  have carry : (if distance-1 < 63 then
      (1 : Runner.W) - Runner.IR.bool (decide (r < (2 : Int)^(distance-1))) else 0) =
      BitVec.ofInt 64 (if r < (2 : Int)^(distance-1) then 0 else 1) := by
    by_cases guarded : distance-1 < 63
    · by_cases below : r < (2 : Int)^(distance-1) <;>
        simp [guarded, below, Runner.IR.bool]
    · have below := floatNormalizeLoop_large_no_carry r (distance-1)
        head.remainder.2.1 (by omega)
      simp [guarded, below]
  obtain ⟨m', run, ag, pre, rq, rr, rd, rt, rf, rc⟩ :=
    floatNormalizeLoopL_large_to_tail hc head room large active
  rw [carry] at rq rr
  have qword : BitVec.ofInt 64 (2*q) = (BitVec.ofInt 64 q : Runner.W)*2 := by
    rw [show (2 : Runner.W) = BitVec.ofInt 64 2 from rfl, ← BitVec.ofInt_mul]
    congr 1
    ring
  rw [qword, transfer.1] at rq
  rw [transfer.2.1] at rr
  refine ⟨m', run, ag, pre, rq, rr, rd, rt, rf, rc,
    ⟨transfer.2.2.1, transfer.2.2.2.1⟩,
    ⟨transfer.2.2.2.2.2.1, transfer.2.2.2.2.2.2.2.1,
      transfer.2.2.2.2.2.2.1⟩, ?_⟩
  rw [transfer.2.2.2.2.1, dk]
  exact head.reconstruction

#print axioms floatNormalizeLoopL_large_canonical_output

set_option maxHeartbeats 800000 in
/-- Execute the common emitted counter/fuel tail and backedge. Only the
    temporary, count and fuel slots change; the transfer result is retained. -/
theorem floatNormalizeLoopL_shared_tail
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K) (fuel count : Runner.W)
    (rf : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some fuel)
    (rc : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some count) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m ⟨pc, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (fuel-1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (count+1) ∧
      (∀ i, i < K → i ≠ base+4 → i ≠ base+5 → i ≠ base+6 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
  have sxslot (j : Nat) (hj : j < K) : sx (II.f (j : Int)) = BitVec.ofNat 64 j :=
    sx_nat (by have := h.small; omega)
  have kept (mem : Runner.Mem) (j i : Nat) (hi : i < K) (hj : j < K)
      (ne : i ≠ j) (v : Runner.W) :
      (write mem (slot fp (BitVec.ofNat 64 j)) 8 v.toNat).rd64
        (slot fp (BitVec.ofNat 64 i)) = mem.rd64 (slot fp (BitVec.ofNat 64 i)) := by
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := j) h.frame.room hj
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega
  have shape1 : code.length ≥ 4 ∧ code.length-4 < code.length ∧
      code[code.length-4]? = some (ci 1 (base+6) 1 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry1 : code[code.length-4] = ci 1 (base+6) 1 0 := by
    simpa only [List.getElem?_eq_getElem shape1.2.1, Option.some.injEq] using shape1.2.2
  have ins1 := h.code (code.length-4) shape1.2.1
  rw [entry1] at ins1
  simp only [ci] at ins1
  let v1 : Runner.W := (1 : Runner.W)
  let m1 := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat
  have ag1 : Agree fp base K m m1 :=
    agree_write h.frame.room (by omega) (by omega) v1.toNat
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag1, h.code.agree ag1 h.far, h.far,
      envAt_agree h.env ag1 h.frame h.ctx (by omega),
      h.wstab m m1 h.welt (ag1.mono (by omega)), h.wstab⟩
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some v1 := by
    simp only [m1, Runner.Mem.rd64, write_rd, h.frame.rd (base+6) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run1 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) m
      ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩ m1 := by
    have run : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) m ⟨(pc + BitVec.ofNat 64 (16*(code.length-4)))+16, fp⟩ m1 := by
      refine run_step ins1 (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) ins1 ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) ins1 ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast sxslot (base+6) room
      rw [sx_lit (by decide : lit32 1 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    have advance : BitVec.ofNat 64 (16*(code.length-4)) + 16 =
        BitVec.ofNat 64 (16*(code.length-3)) := by
      change BitVec.ofNat 64 (16*(code.length-4)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  have shape2 : code.length ≥ 4 ∧ code.length-3 < code.length ∧
      code[code.length-3]? = some (ci 3 (base+5) (base+5) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry2 : code[code.length-3] = ci 3 (base+5) (base+5) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape2.2.1, Option.some.injEq] using shape2.2.2
  have ins2 := pre1.code (code.length-3) shape2.2.1
  rw [entry2] at ins2
  simp only [ci] at ins2
  let v2 : Runner.W := count+1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat
  have ag2 : Agree fp base K m1 m2 :=
    agree_write pre1.frame.room (by omega) (by omega) v2.toNat
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree ag2, pre1.code.agree ag2 pre1.far, pre1.far,
      envAt_agree pre1.env ag2 pre1.frame pre1.ctx (by omega),
      pre1.wstab m1 m2 pre1.welt (ag2.mono (by omega)), pre1.wstab⟩
  have read2 : m2.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some v2 := by
    simp only [m2, Runner.Mem.rd64, write_rd, pre1.frame.rd (base+5) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run2 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩) m1
      ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩ m2 := by
    have sxa : sx (II.f ((base : Int)+5)) = BitVec.ofNat 64 (base+5) := by
      exact_mod_cast sxslot (base+5) (by omega)
    have sxb : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
      exact_mod_cast sxslot (base+6) (by omega)
    have sxd : sx (II.f ((base : Int)+5)) = BitVec.ofNat 64 (base+5) := by
      exact_mod_cast sxslot (base+5) (by omega)
    have ra : m1.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some count := by
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact rc
    have rb : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some (1 : Runner.W) := by
      exact read1
    have wr : m1.wr64 (slot fp (sx (II.f ((base : Int)+5)))) v2 = some m2 := by
      rw [sxd]; exact wr64_some (pre1.frame.wr (base+5) (by omega))
    have run := run_step (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩) ins2 (by decide)
      (run_bin (g := fun a b => some (a+b)) ins2
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    have advance : BitVec.ofNat 64 (16*(code.length-3)) + 16 =
        BitVec.ofNat 64 (16*(code.length-2)) := by
      change BitVec.ofNat 64 (16*(code.length-3)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  have shape3 : code.length ≥ 4 ∧ code.length-2 < code.length ∧
      code[code.length-2]? = some (ci 4 (base+4) (base+4) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry3 : code[code.length-2] = ci 4 (base+4) (base+4) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape3.2.1, Option.some.injEq] using shape3.2.2
  have ins3 := pre2.code (code.length-2) shape3.2.1
  rw [entry3] at ins3
  simp only [ci] at ins3
  let v3 : Runner.W := fuel-1
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (base+4))) 8 v3.toNat
  have ag3 : Agree fp base K m2 m3 :=
    agree_write pre2.frame.room (by omega) (by omega) v3.toNat
  have pre3 : Pre L m3 pc fp K base code ρ W reserved :=
    ⟨pre2.ctx, pre2.small, pre2.frame.agree ag3, pre2.code.agree ag3 pre2.far, pre2.far,
      envAt_agree pre2.env ag3 pre2.frame pre2.ctx (by omega),
      pre2.wstab m2 m3 pre2.welt (ag3.mono (by omega)), pre2.wstab⟩
  have read3 : m3.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some v3 := by
    simp only [m3, Runner.Mem.rd64, write_rd, pre2.frame.rd (base+4) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run3 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩) m2
      ⟨pc + BitVec.ofNat 64 (16*(code.length-1)), fp⟩ m3 := by
    have sxa : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
      exact_mod_cast sxslot (base+4) (by omega)
    have sxb : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
      exact_mod_cast sxslot (base+6) (by omega)
    have sxd : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
      exact_mod_cast sxslot (base+4) (by omega)
    have ra : m2.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some fuel := by
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact rf
    have rb : m2.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some (1 : Runner.W) := by
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact read1
    have wr : m2.wr64 (slot fp (sx (II.f ((base : Int)+4)))) v3 = some m3 := by
      rw [sxd]; exact wr64_some (pre2.frame.wr (base+4) (by omega))
    have run := run_step (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩) ins3 (by decide)
      (run_bin (g := fun a b => some (a-b)) ins3
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    have advance : BitVec.ofNat 64 (16*(code.length-2)) + 16 =
        BitVec.ofNat 64 (16*(code.length-1)) := by
      change BitVec.ofNat 64 (16*(code.length-2)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  refine ⟨m3, (Star.one run1).trans ((Star.one run2).trans
      ((Star.one run3).trans (Star.one (floatNormalizeLoopL_backedge hc pre3.code)))),
    ag1.trans (ag2.trans ag3), pre3, read3, ?_, ?_⟩
  · rw [show m3 = write m2 (slot fp (BitVec.ofNat 64 (base+4))) 8 v3.toNat from rfl,
      kept _ _ _ (by omega) (by omega) (by omega)]
    exact read2
  · intro i hi n4 n5 n6
    simp only [m3, m2, m1, kept _ _ i hi (by omega) n4,
      kept _ _ i hi (by omega) n5, kept _ _ i hi (by omega) n6]

#print axioms floatNormalizeLoopL_shared_tail

/-- A complete actual LARGE iteration returns to the canonical next head.
    The initial budget ceiling pays for the count increment. No execution
    or iteration premise is assumed. -/
theorem floatNormalizeLoopL_large_iteration
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r)
    (room : base+8 < K) (ceiling : budget < 2^63)
    (large : 61 < distance) (active : q < target) :
    let c : Int := if r < (2 : Int)^(distance-1) then 0 else 1
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' n (count+1) (distance-1)
        (2*q+c) (r-c*(2 : Int)^(distance-1)) := by
  dsimp only
  obtain ⟨m0, entry, ag0, h0⟩ :=
    floatNormalizeLoopL_active_entry hc head (by omega) (by omega) active
  obtain ⟨m1, body, ag1, pre1, rq, rr, rd, rt, rf, rc, qb, rb, reconstruct⟩ :=
    floatNormalizeLoopL_large_canonical_output hc h0 room large active
  obtain ⟨m2, tail, ag2, pre2, rf2, rc2, kept⟩ :=
    floatNormalizeLoopL_shared_tail hc pre1 (by omega) _ _ rf rc
  have resource := head.active_budget_bounds ceiling
  have fuelWord : (BitVec.ofNat 64 (n+1) : Runner.W)-1 = BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have countWord : (BitVec.ofNat 64 count : Runner.W)+1 = BitVec.ofNat 64 (count+1) := by
    rw [BitVec.ofNat_add]
    rfl
  refine ⟨m2, entry.trans (body.trans tail), ag0.trans (ag1.trans ag2),
    { pre := pre2
      room := head.room
      fuelWord := resource.2.1
      countWord := resource.1
      distanceWord := by have := head.distanceWord; omega
      quotient := qb
      remainder := rb
      targetBound := head.targetBound
      readQ := ?_
      readR := ?_
      readDistance := ?_
      readTarget := ?_
      readFuel := by simpa only [fuelWord] using rf2
      readCount := by simpa only [countWord] using rc2
      conservedBudget := resource.2.2
      reconstruction := ?_ }⟩
  · rw [kept base (by omega) (by omega) (by omega) (by omega)]; exact rq
  · rw [kept (base+1) (by omega) (by omega) (by omega) (by omega)]; exact rr
  · rw [kept (base+2) (by omega) (by omega) (by omega) (by omega)]; exact rd
  · rw [kept (base+3) (by omega) (by omega) (by omega) (by omega)]; exact rt
  · simpa only [show count+1+(distance-1) = count+distance by omega] using reconstruct

#print axioms floatNormalizeLoopL_large_iteration

set_option maxHeartbeats 800000 in
end
end Gabbro.Stage0.Senke
