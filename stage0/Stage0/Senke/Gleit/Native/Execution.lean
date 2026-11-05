/- Composition of actual native FP instructions with the ordinary frame proof. -/
module
public import Stage0.Senke.Gleit.Native.Code
public import Stage0.Senke.Ausdruck.Sim
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The two child executions supply the words actually read by `run_fp`.
    The output relation is native value equality, with no NaN bit assumption. -/
theorem nativeFP_bin_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {ca cb : List II} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {Pa Pb P : Runner.W → Prop} (kind : Runner.NativeFPOp)
    (dispatch : op kind.code = Runner.IR.fp kind)
    (hA : ∀ m pc, Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca Pa)
    (hB : ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W reserved →
      Ok m pc fp K (d + 1) cb Pb)
    (result : ∀ wa wb, Pa wa → Pb wb →
      ∃ r, Runner.NativeFPEval kind wa wb r ∧ P r)
    (hK : d + 1 < K)
    (h : Pre L m pc fp K d (ca ++ cb ++ [ci kind.code d d (d + 1)]) ρ W reserved) :
    Ok m pc fp K d (ca ++ cb ++ [ci kind.code d d (d + 1)]) P := by
  have h' : Pre L m pc fp K d (ca ++ (cb ++ [ci kind.code d d (d + 1)])) ρ W reserved := by
    simpa using h
  obtain ⟨m1, s1, a1, wa, ra, pa⟩ := hA m pc h'.left
  have h1 := h'.next a1 (Nat.le_succ d) (by omega)
  obtain ⟨m2, s2, a2, wb, rb, pb⟩ := hB m1 _ h1.left
  have h2 := h1.next (d := d + 1) (d' := d + 1) a2 (Nat.le_refl _) (by omega)
  obtain ⟨r, hr, pr⟩ := result wa wb pa pb
  have hF2 : FrameOK m2 fp K := h1.frame.agree a2
  obtain ⟨hw, hrd, a3⟩ := wr_slot hF2 (d := d) (by omega) r
  have ra2 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some wa := by
    rw [agree_rd_low a2 hF2.room (Nat.lt_succ_self d) (by omega)]
    exact ra
  have small := h.small
  have hs : sx (II.f (d : Int)) = BitVec.ofNat 64 d := sx_nat (by omega)
  have hs1 : sx (II.f ((d : Int) + 1)) = BitVec.ofNat 64 (d + 1) := by
    simpa using (sx_nat (d := d + 1) (by omega))
  have hi := h2.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hi
  have opcode := kind.code_bounds
  have s3 := star_ins (fp := fp)
    (m' := write m2 (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) h2.code
    (by simpa only [ci] using (show kind.code < 256 by omega)) (by
      simp only [ci]
      rw [dispatch]
      refine run_fp (t := ⟨_, fp⟩)
        (m1 := write m2 (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) hi
        (va := wa) (vb := wb) ?_ ?_ hr ?_
      · simpa [ci, hs] using ra2
      · simpa [ci, hs1] using rb
      · simpa [ci, hs] using hw)
  refine ⟨_, (s1.trans s2).trans ?_,
    (a1.trans (a2.mono (Nat.le_succ d))).trans a3, r, hrd, pr⟩
  have finish : pc + BitVec.ofNat 64 (16 * (ca ++ cb ++ [ci kind.code d d (d + 1)]).length) =
      pc + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * cb.length) +
        BitVec.ofNat 64 (16 * [ci kind.code d d (d + 1)].length) := by
    simp only [List.length_append, List.length_singleton, pc_add]
  rw [finish]
  exact s3

/-- A native instruction consumes the complete accepted child programs and keeps
    the same world, context reservation and untouched frame prefix. -/
theorem nativeFPWordL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W}
    {a b : Option (List II × Nat)} {c : List II}
    {Pa Pb P : Runner.W → Prop} (kind : Runner.NativeFPOp)
    (dispatch : op kind.code = Runner.IR.fp kind)
    (h : nativeFPWordL kind d a b = some (c, top)) (hK : top ≤ K)
    (iha : ∀ ca ta, a = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca Pa)
    (ihb : ∀ cb tb, b = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb Pb)
    (result : ∀ wa wb, Pa wa → Pb wb → ∃ r, Runner.NativeFPEval kind wa wb r ∧ P r)
    (hp : Pre L m pc fp K d c ρ W reserved) : Ok m pc fp K d c P := by
  simp only [nativeFPWordL, wordL, bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, hc⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact nativeFP_bin_ok kind dispatch (iha ca ta ha (by omega))
    (ihb cb tb hb (by omega)) result (by omega) hp

end Gabbro.Stage0.Senke
