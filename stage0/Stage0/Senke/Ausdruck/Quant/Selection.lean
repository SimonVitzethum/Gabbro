/- Typed frame selection uses the common physical pointer transport. -/
import Stage0.Senke.Ausdruck.Quant.Memory
import Stage0.Senke.Ausdruck.Eng
import Stage0.Senke.Ausdruck.Aggregat.Scalar

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem slot_nested (fp : Runner.W) (base offset : Nat) :
    slot (slot fp (BitVec.ofNat 64 base)) (BitVec.ofNat 64 offset) =
      slot fp (BitVec.ofNat 64 (base + offset)) := by
  simp only [slot, BitVec.ofNat_add, BitVec.add_mul, BitVec.add_assoc]

theorem ValueAt.rebase {m : Runner.Mem} {fp : Runner.W} {base : Nat} {τ : Ty}
    {v : Wert D τ} (value : ValueAt L m fp base τ v) :
    ValueAt L m (slot fp (BitVec.ofNat 64 base)) 0 τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  simpa only [Nat.zero_add, slot_nested] using value.2 i hi

/-- Actual address arithmetic followed by the shared full-span load. The source
    lies before the two explicit temporaries; every represented limb is copied. -/
theorem selectFrameSpan_ok {m : Runner.Mem} {pc fp : Runner.W} {K base dst ptr tmp index : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {τ : Ty} {v : Wert D τ}
    (fits : base + (index + 1) * valueWords τ ≤ ptr) (order : dst ≤ base + index * valueWords τ)
    (pt : ptr < tmp) (ht : tmp < K) (literal : 8 * valueWords τ < 2 ^ 31)
    (indexWord : m.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 index))
    (input : ValueAt L m fp (base + index * valueWords τ) τ v)
    (pre : Pre L m pc fp K ptr (selectFrameSpan (valueWords τ) base dst ptr tmp) ρ W reserved) :
    ValueOk L m pc fp K dst (selectFrameSpan (valueWords τ) base dst ptr tmp) τ v := by
  let w := valueWords τ
  have positive : 0 < w := valueWords_pos τ
  have sourceBound : base + index * w + w ≤ ptr := by simpa [Nat.add_mul, Nat.add_assoc] using fits
  have order' : dst ≤ base + index * w := order
  have dstBound : dst + w ≤ ptr := by omega
  have hp : Pre L m pc fp K ptr
      ([ci 1 tmp (8 * w) 0] ++ ([ci 5 ptr ptr tmp] ++
      ([ci 17 tmp base 0] ++ ([ci 3 ptr tmp ptr] ++ loadPointerSpan w dst ptr tmp 0)))) ρ W reserved := pre
  obtain ⟨m1, s1, a1, factor, r1, ef⟩ := const_ok
    { hp.left with ctx := by have := pre.ctx; omega }
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega) ht
  subst factor
  have a1' := a1.mono (by omega : ptr ≤ tmp)
  have p1 := hp.next a1' (Nat.le_refl _) (by omega)
  have index1 : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 index) := by
    rw [agree_rd_low a1 pre.frame.room pt (by omega)]; exact indexWord
  obtain ⟨m2, s2, a2, offset, r2, eo⟩ := eng_bin_ok p1.left (by omega) (by omega) ht index1 r1
    (g := fun a b => some (a * b)) rfl (by decide) rfl
  subst offset
  have p2 := p1.next a2 (Nat.le_refl _) (by omega)
  have addressRun : Ok m2 (pc + 16 + 16) fp K tmp [ci 17 tmp base 0]
      (· = slot fp (BitVec.ofNat 64 base)) := by
    have p : Pre L m2 _ fp K tmp [ci 17 tmp base 0] ρ W reserved :=
      { p2.left with ctx := by have := pre.ctx; omega }
    refine one_ok p (by simp [ci]) ht rfl fun m' write => ?_
    have instruction := p.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at instruction
    simp only [ci, op]
    refine f2_run (t := ⟨_, fp⟩) instruction ?_
    simp only [ret1]
    refine f1_run (t := ⟨_, fp⟩) instruction ?_
    rw [sx_nat (by have := pre.small; omega), sx_nat (by have := pre.small; omega)]
    exact run_wr64 write
  obtain ⟨m3, s3, a3, address, r3, ea⟩ := addressRun
  subst address
  have p3 := p2.next (a3.mono (by omega : ptr ≤ tmp)) (Nat.le_refl _) (by omega)
  have offset3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) =
      some (BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * w)) := by
    rw [agree_rd_low a3 p2.frame.room pt (by omega)]; exact r2
  obtain ⟨m4, s4, a4, selected, r4, es⟩ := eng_bin_ok p3.left (by omega) ht (by omega) r3 offset3
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  subst selected
  have pointerEq : slot fp (BitVec.ofNat 64 base) +
      BitVec.ofNat 64 index * BitVec.ofInt 64 (8 * w) =
      slot fp (BitVec.ofNat 64 (base + index * w)) := by
    simp only [Int.natCast_mul, BitVec.ofInt_natCast, slot, BitVec.ofNat_add,
      BitVec.ofNat_mul, BitVec.mul_assoc, BitVec.add_mul, BitVec.add_assoc]
    congr 2
    have eight : BitVec.ofInt 64 (8 * (w : Int)) = BitVec.ofNat 64 w * 8 := by
      have : (8 * (w : Int)) = ((8 * w : Nat) : Int) := by push_cast; rfl
      rw [this, BitVec.ofInt_natCast, BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [eight]
  rw [pointerEq] at r4
  have a14 := a1'.trans (a2.trans ((a3.mono (by omega : ptr ≤ tmp)).trans a4))
  have source := input.agree a14 pre.frame (by omega) (by omega)
  have next := p3.next a4 (Nat.le_refl _) (by omega : ptr ≤ K)
  have frame := pre.frame.agree a14
  have room := frame.room
  have addressNat := slot_toNat frame.room (show base + index * w < K by omega)
  obtain ⟨m5, s5, a5, effect, output, pointer⟩ := loadPointerValue_run frame pre.small dstBound pt ht
    (by simpa only [Nat.zero_add] using literal) (by rw [addressNat]; omega)
    (Or.inl (by rw [addressNat]; omega)) (Or.inl (by rw [addressNat]; omega))
    next.code (by simpa using next.far) r4 source.rebase
  refine ⟨m5, ?_, (a14.mono (by omega : dst ≤ ptr)).trans a5, output⟩
  have steps := s1.trans (s2.trans (s3.trans (s4.trans s5)))
  rw [selectFrameSpan_length, show 16 * (4 + 3 * valueWords τ) = 16 * 4 + 48 * valueWords τ by omega,
    BitVec.ofNat_add, ← BitVec.add_assoc]
  simpa only [List.length_cons, List.length_nil, pc_add, Nat.reduceAdd, Nat.zero_add] using steps

end Gabbro.Stage0.Senke
