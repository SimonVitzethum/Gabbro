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


end
end Gabbro.Stage0.Senke
