module

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

set_option maxHeartbeats 800000 in
/-- Materialize the carry threshold only after the actual distance guard. -/
theorem floatNormalizeLoopL_large_carry_denominator
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat}
    (h : Pre L m pc fp K base code ρ W reserved)
    (readDistance : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 distance))
    (room : base+7 < K) (small : distance < 63)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1) :
    ∃ m', Star ⟨pc+224, fp⟩ m ⟨pc+240, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^distance)) := by
  have shape : 14 < code.length ∧
      code[14]? = some (ci 11 (base+7) (base+6) (base+2)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[14] = ci 11 (base+7) (base+6) (base+2) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 14 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := BitVec.ofInt 64 ((2 : Int)^distance)
  let next := write m (slot fp (BitVec.ofNat 64 (base+7))) 8 value.toNat
  have ag : Agree fp (base+7) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+2)) = BitVec.ofNat 64 (base+2) := by
    exact_mod_cast (sx_nat (d := base+2) (by have := h.small; omega))
  have sx7 : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
    exact_mod_cast (sx_nat (d := base+7) (by have := h.small; omega))
  have result : (1 : Runner.W) <<< ((BitVec.ofNat 64 distance).toNat % 64) = value := by
    have shift : (BitVec.ofNat 64 distance).toNat % 64 = distance := by
      simp only [BitVec.toNat_ofNat]
      omega
    rw [shift]
    change (1 : Runner.W) <<< distance = BitVec.ofInt 64 ((2 : Int)^distance)
    rw [show (2 : Int)^distance = ((2^distance : Nat) : Int) by simp, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have comparison : Run (step ⟨pc+224, fp⟩) m ⟨pc+240, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+7)))) value = some next := by
      rw [sx7]; exact wr64_some (h.frame.wr (base+7) room)
    have run := run_step (t := ⟨pc+224, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (a <<< (b.toNat % 64))) ins
        (by rw [sx6]; exact loaded) (by rw [sx2]; exact readDistance)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag.mono (by omega), preNext, ?_⟩
  change (write m (slot fp (BitVec.ofNat 64 (base+7))) 8 value.toNat).rd64 _ = some value
  simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+7) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms floatNormalizeLoopL_large_carry_denominator

set_option maxHeartbeats 800000 in
theorem floatNormalizeLoopL_large_carry_compare
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat} {r : Int}
    (h : Pre L m pc fp K base code ρ W reserved)
    (bound : 0 ≤ r ∧ r < 2^63) (small : distance < 63)
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
      some (BitVec.ofInt 64 r))
    (room : base+6 < K)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some (BitVec.ofInt 64 ((2 : Int)^distance))) :
    ∃ m', Star ⟨pc+240, fp⟩ m ⟨pc+256, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (r < (2 : Int)^distance))) ∧
      (∀ i, i < K → i ≠ base+6 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
  have shape : 15 < code.length ∧
      code[15]? = some (ci 13 (base+6) (base+1) (base+7)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[15] = ci 13 (base+6) (base+1) (base+7) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 15 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := Runner.IR.bool (decide (r < (2 : Int)^distance))
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+1)) = BitVec.ofNat 64 (base+1) := by
    exact_mod_cast (sx_nat (d := base+1) (by have := h.small; omega))
  have sx7 : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
    exact_mod_cast (sx_nat (d := base+7) (by have := h.small; omega))
  have powerBound : (2 : Int)^distance ≤ 2^62 := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show distance ≤ 62 by omega))
  have powerPositive : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have result : Runner.IR.bool ((BitVec.ofInt 64 r).slt
      (BitVec.ofInt 64 ((2 : Int)^distance))) = value := by
    rw [slt_in (by constructor <;> omega) (by constructor <;> omega)]
  have comparison : Run (step ⟨pc+240, fp⟩) m ⟨pc+256, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) value = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+240, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins
        (by rw [sx2]; exact readR) (by rw [sx7]; exact loaded)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag, preNext, ?_, ?_⟩
  · change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
        le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]


  · intro i hi ne
    change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = _
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := base+6) h.frame.room room
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega

#print axioms floatNormalizeLoopL_large_carry_compare

/-- Connected execution through the large carry decision preserves every
    state word already established at byte 160. -/
theorem floatNormalizeLoopL_large_carry_tested
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+7 < K) (large : 61 < distance) (active : q < target) :
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + (if distance-1 < 63 then 256 else 336), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      (0 ≤ 2*q ∧ 2*q < 2^61) ∧
      (distance-1 < 63 → m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (r < (2 : Int)^(distance-1))))) ∧
      (distance-1 < 63 → m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^(distance-1)))) := by
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds⟩ :=
    floatNormalizeLoopL_large_carry_dispatch hc head (by omega) large active
  by_cases guarded : distance-1 < 63
  · obtain ⟨m2, run2, ag2, pre2, seed⟩ := floatNormalizeLoopL_large_carry_seed hc pre1 (by omega)
    have rd2 := rd
    rw [← agree_rd_low ag2 pre1.frame.room (show base+2 < base+6 by omega) (by omega)] at rd2
    obtain ⟨m3, run3, ag3, pre3, den⟩ :=
      floatNormalizeLoopL_large_carry_denominator hc pre2 rd2 room guarded seed
    have rr3 : m3.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) := by
      rw [agree_rd_low (ag2.trans ag3) pre1.frame.room (by omega) (by omega)]; exact rr
    obtain ⟨m4, run4, ag4, pre4, tested, kept⟩ :=
      floatNormalizeLoopL_large_carry_compare hc pre3 ⟨head.remainder.1, head.remainder.2.1⟩
        guarded rr3 (by omega) den
    have ag := ag2.trans (ag3.trans ag4)
    have reads (i : Nat) (hi : i < base+6) :=
      agree_rd_low ag pre1.frame.room hi (show base+6 ≤ K by omega)
    refine ⟨m4, ?_, ag1.trans (ag.mono (by omega)), pre4, ?_, ?_, ?_, ?_, ?_, ?_, bounds, (fun _ => tested), (fun _ => ?_)⟩
    · have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+208, fp⟩ m1 := by
        simpa only [guarded, ↓reduceIte] using run1
      simpa only [guarded, ↓reduceIte] using
        connectedPrefix.trans (run2.trans (run3.trans run4))
    · rw [reads base (by omega)]; exact rq
    · rw [reads (base+1) (by omega)]; exact rr
    · rw [reads (base+2) (by omega)]; exact rd
    · rw [reads (base+3) (by omega)]; exact rt
    · rw [reads (base+4) (by omega)]; exact rf
    · rw [reads (base+5) (by omega)]; exact rc
    · rw [kept (base+7) room (by omega)]; exact den
  · exact ⟨m1, by simpa [guarded] using run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds, (fun h => (guarded h).elim), (fun h => (guarded h).elim)⟩

#print axioms floatNormalizeLoopL_large_carry_tested


end
end Gabbro.Stage0.Senke
