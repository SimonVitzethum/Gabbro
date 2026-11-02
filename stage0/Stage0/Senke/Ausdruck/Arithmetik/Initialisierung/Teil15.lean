module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil14

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Joint witness connects the actual test branch, body, and backedge. It has
    a negative correction, a nonzero significand, and a strictly falling exponent.
    The flag premise must still be supplied by the preceding condition run. -/
theorem floatFiniteAddL_left_active_backedge_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {head fp : Runner.W}
    {K dst reserved conditionLength : Nat} (tail : List II)
    (offsetRange : lit32 (-(16*((conditionLength+5 : Nat) : Int))) = true)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some 1)
    (pre : Pre L m (head+BitVec.ofNat 64 (16*conditionLength)) fp K (dst+5)
      ([ci 19 (dst+9) 96 0] ++
        [ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++
        [ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨head+BitVec.ofNat 64 (16*conditionLength),fp⟩ m ⟨head,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 26 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 3 ∧
      FiniteLeftInvariant 205 16 (-3) 4 1 26 3 ∧
      (3 : Int).toNat < (4 : Int).toNat := by
  obtain ⟨enter,next⟩ := floatFiniteAddL_left_test_enter (dst := dst) (K := K)
    [ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
      ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)]
    ([ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail)
    (by omega) flag (by simpa only [List.append_assoc] using pre)
  have entryPc : head+BitVec.ofNat 64 (16*conditionLength)+16 =
      head+BitVec.ofNat 64 (16*(conditionLength+1)) := by
    change head+BitVec.ofNat 64 (16*conditionLength)+BitVec.ofNat 64 16 = _
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    congr 2 <;> omega
  rw [entryPc] at next
  obtain ⟨out,run,agree,readQ,readE,inv,decreasing⟩ := floatFiniteAddL_left_body_backedge
    (conditionLength := conditionLength) (steps := 0) tail finiteLeftInvariant_zeuge.1
    (by norm_num) (by norm_num) offsetRange room rq re next
  refine ⟨out,?_,agree,readQ,readE,inv,decreasing⟩
  apply enter.trans
  simpa only [entryPc] using run

#print axioms floatFiniteAddL_left_active_backedge_zeuge

/-- The whole actual f32 test computes an active flag while retaining the
    nonzero, negative-correction invariant in that same memory. -/
theorem floatFiniteAddL_left_condition_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (tail : List II) (room : dst+12 ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (pre : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^26) (dst+10)).1 ++
        [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 13 (dst+11) (dst+10) (dst+5), ci 5 (dst+9) (dst+9) (dst+11),
          ci 1 (dst+10) 0 0, ci 14 (dst+11) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+11) (dst+10) (dst+11),
          ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*(konstWL 4 (2^26) (dst+10)).1.length)+144,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some 1 ∧
      FiniteLeftInvariant 205 16 (-3) 4 0 13 4 := by
  obtain ⟨out,run,agree,readQ,readE,flag,_⟩ := floatFiniteAddL_left_condition
    Gleitkomma.f32 tail (by decide) room rq re pre
  have flagEq : Runner.IR.bool ((13 : Runner.W).slt (BitVec.ofNat 64 (2^26))) *
      Runner.IR.bool ((1 : Runner.W).slt 4) * (1-Runner.IR.bool ((13 : Runner.W) == 0)) = 1 := by decide
  change out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some
    (Runner.IR.bool ((13 : Runner.W).slt (BitVec.ofNat 64 (2^26))) *
      Runner.IR.bool ((1 : Runner.W).slt 4) * (1-Runner.IR.bool ((13 : Runner.W) == 0))) at flag
  exact ⟨out,run,agree,readQ,readE,by simpa only [flagEq] using flag,
    finiteLeftInvariant_zeuge.1⟩

#print axioms floatFiniteAddL_left_condition_zeuge

/-- Both formats and both RIGHT outcomes jointly satisfy the concrete arithmetic
    side of the test; the execution premises are shared with the generic run. -/
theorem floatFiniteAddL_right_condition_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    (F : Gleitkomma.Format) (format : F = Gleitkomma.f32 ∨ F = Gleitkomma.f64)
    (large : Bool) (tail : List II)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 23)) =
      some (if large then BitVec.ofNat 64 (2^56) else 13))
    (re : m.rd64 (slot fp (BitVec.ofNat 64 21)) = some 4)
    (pre : Pre L m pc fp 40 25
      ((konstWL 4 (2^(F.fracBits+4)) 26).1 ++
        [ci 13 25 23 26, ci 1 26 1 0, ci 4 25 26 25] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m
      ⟨pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) 26).1.length)+48,fp⟩ out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 23)) =
        some (if large then BitVec.ofNat 64 (2^56) else 13) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 21)) = some 4 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 25)) = some (if large then 1 else 0) := by
  have bound : 2^(F.fracBits+4) < 65536^4 := by
    rcases format with rfl | rfl <;> decide
  obtain ⟨out,run,_,rq',re',flag,_⟩ := floatFiniteAddL_right_condition
    (dst := 16) F tail bound (by omega) rq re pre
  refine ⟨out,run,rq',re',?_⟩
  have eq : (1-Runner.IR.bool ((if large then BitVec.ofNat 64 (2^56) else 13).slt
      (BitVec.ofNat 64 (2^(F.fracBits+4))))) = (if large then 1 else 0) := by
    rcases format with rfl | rfl <;> cases large <;> decide
  simpa only [eq] using flag

#print axioms floatFiniteAddL_right_condition_zeuge

end Gabbro.Stage0.Senke
