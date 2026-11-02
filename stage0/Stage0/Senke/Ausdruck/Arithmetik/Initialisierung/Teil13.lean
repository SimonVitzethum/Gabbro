module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil12

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatFiniteAddL_read_fields_align_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (sortRoom : 27 < K) (alignRoom : 33 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ executed tail aligned continuation alignTop, ∃ values : Nat → Runner.W, ∃ out,
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1)) (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = executed ++
        ([ci 13 (16+9) (16+5) (16+6),
          ci 14 (16+10) (16+5) (16+6),
          ci 13 (16+11) (16+7) (16+8),
          ci 5 (16+10) (16+10) (16+11),
          ci 9 (16+9) (16+9) (16+10),
          ci 19 (16+9) 176 0,
          ci 2 (16+9) (16+3) 0, ci 2 (16+3) (16+4) 0, ci 2 (16+4) (16+9) 0,
          ci 2 (16+9) (16+5) 0, ci 2 (16+5) (16+6) 0, ci 2 (16+6) (16+9) 0,
          ci 2 (16+9) (16+7) 0, ci 2 (16+7) (16+8) 0, ci 2 (16+8) (16+9) 0,
          ci 18 16 0 0] ++ tail) ∧
      tail = aligned ++ continuation ∧
      floatShiftJamL (16+16)
        (fun j => some ([ci 2 j (16+8) 0],j+1))
        (fun j => wordL 4 j (some ([ci 2 j (16+5) 0],j+1))
          (some ([ci 2 (j+1) (16+6) 0],j+2))) = some (aligned,alignTop) ∧
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.length),fp⟩ out ∧
      Agree fp (16+1) K m out ∧
      (∀ i, i < 8 → values (16+1+i) =
        match i with
        | 0 => 7
        | 1 => 11
        | 2 => floatFieldWord 7 (F.fracBits+F.ebits) 1
        | 3 => floatFieldWord 11 (F.fracBits+F.ebits) 1
        | _ => finiteAddRemainingValue F 7 11 (i-4)) ∧
      (∀ i, i < 16+9 → out.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if (values (16+5)).slt (values (16+6)) ||
            ((values (16+5) == values (16+6)) && (values (16+7)).slt (values (16+8))) then
          if i = 16+3 then values (16+4) else
          if i = 16+4 then values (16+3) else
          if i = 16+5 then values (16+6) else
          if i = 16+6 then values (16+5) else
          if i = 16+7 then values (16+8) else
          if i = 16+8 then values (16+7) else values i
         else values i)) ∧
      (∃ ex ey q r : Runner.W,
        out.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some ex ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+6))) = some ey ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+8))) = some r ∧
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt) ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+16))) =
          some (floatShiftJamWord r (ex-ey)) ∧
        ∃ sx sy jam : Runner.W,
          out.rd64 (slot fp (BitVec.ofNat 64 (16+3))) = some sx ∧
          out.rd64 (slot fp (BitVec.ofNat 64 (16+4))) = some sy ∧
          out.rd64 (slot fp (BitVec.ofNat 64 (16+16))) = some jam ∧
          let signX : Int := if sx = 0 then 1 else -1
          let signY : Int := if sy = 0 then 1 else -1
          let denominator : Int := (2^(ex-ey).toNat : Nat)
          let quotient : Int := (r.toNat / 2^(ex-ey).toNat : Nat)
          let remainder : Int := (r.toNat % 2^(ex-ey).toNat : Nat)
          (signX*(q.toNat : Int) + signY*(jam.toNat : Int))*denominator +
            signY*(remainder - ((jam.toNat : Int)-quotient)*denominator) =
            signX*(q.toNat : Int)*denominator + signY*(r.toNat : Int)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.length))
        fp K (16+17) continuation ρ W 13 ∧
      ∃ out2 sx sy q jam,
        out.rd64 (slot fp (BitVec.ofNat 64 (16+3))) = some sx ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+4))) = some sy ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+16))) = some jam ∧
        Star ⟨pc,fp⟩ m
          ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.length)+96,fp⟩ out2 ∧
        Agree fp (16+1) K m out2 ∧
        out2.rd64 (slot fp (BitVec.ofNat 64 (16+7))) =
          some (if sx == sy then q+jam else q-jam) ∧
        ((∀ i, i < 4 →
            if i < 2 then 1 ≤ (finiteAddRemainingValue F 7 11 i).toNat ∧
              (finiteAddRemainingValue F 7 11 i).toNat < F.bexpMax
            else (finiteAddRemainingValue F 7 11 i).toNat < 2^56) →
          ∃ ex ey : Runner.W,
            out2.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some ex ∧
            out2.rd64 (slot fp (BitVec.ofNat 64 (16+6))) = some ey ∧
            1 ≤ ex.toNat ∧ ex.toNat < F.bexpMax ∧
            1 ≤ ey.toNat ∧ ey.toNat < F.bexpMax ∧ q.toNat < 2^56 ∧ jam.toNat < 2^56 ∧
            -2^57 < (if sx == sy then q+jam else q-jam).toInt ∧
            (if sx == sy then q+jam else q-jam).toInt < 2^57 ∧
            ((sx = sy ∨ ex = ey) →
              (if sx == sy then q+jam else q-jam) ≠ 0 →
              0 < (if sx == sy then q+jam else q-jam).toInt) ∧
            (∀ (x y : Gleitkomma.GBits F), F.dicht →
              F.ebits + F.fracBits + 1 ≤ 64 → F.fracBits ≤ 52 → 1 < F.bexpMax →
              Gleitkomma.wf F x → Gleitkomma.wf F y →
              x.bexp ≠ F.bexpMax → y.bexp ≠ F.bexpMax →
              7 = BitVec.ofNat 64 (Gleitkomma.zuBits F x) →
              11 = BitVec.ofNat 64 (Gleitkomma.zuBits F y) →
              (if sx == sy then q+jam else q-jam) ≠ 0 →
              0 < (if sx == sy then q+jam else q-jam).toInt) ∧
            ∃ source : Runner.W,
              out.rd64 (slot fp (BitVec.ofNat 64 (16+8))) = some source ∧
              let den : Int := (2^(ex-ey).toNat : Nat)
              let numerator : Int := if sx == sy then
                (q.toNat : Int)*den + source.toNat else
                (q.toNat : Int)*den - source.toNat
              let correction : Int := if sx == sy then
                (source.toNat : Int) - (jam.toNat : Int)*den else
                (jam.toNat : Int)*den - source.toNat
              numerator = (if sx == sy then q+jam else q-jam).toInt*den + correction ∧
              (numerator.natAbs : Int) =
                floatSumMagnitude (numerator/den) (numerator%den)*den +
                  (if numerator/den < 0 then
                    if numerator%den = 0 then 0 else den - numerator%den
                   else numerator%den) ∧
              ((numerator < 0) ↔ numerator/den < 0) ∧
              (numerator = 0 ↔ numerator/den = 0 ∧ numerator%den = 0)) ∧
        ∃ signedTail,
          continuation = [ci 2 (16+8) (16+16) 0,
            ci 14 (16+9) (16+3) (16+4), ci 19 (16+9) 48 0,
            ci 3 (16+7) (16+7) (16+8), ci 18 32 0 0,
            ci 4 (16+7) (16+7) (16+8)] ++ signedTail ∧
          Pre L out2 (pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.length)+96) fp K (16+7)
            signedTail ρ W 13 ∧
          ∃ normalization,
            signedTail = [ci 1 (16+10) 0 0,
              ci 14 (16+9) (16+7) (16+10)] ++ normalization ∧
            ∃ tested,
              Star ⟨pc,fp⟩ m
                ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                  BitVec.ofNat 64 (16*aligned.length)+128,fp⟩ tested ∧
              Agree fp (16+1) K m tested ∧
              tested.rd64 (slot fp (BitVec.ofNat 64 (16+9))) =
                some (Runner.IR.bool ((if sx == sy then q+jam else q-jam) == 0)) ∧
              Pre L tested (pc+BitVec.ofNat 64 (16*executed.length)+256+
                BitVec.ofNat 64 (16*aligned.length)+128) fp K (16+7)
                normalization ρ W 13 ∧
              Agree fp (16+9) K out2 tested ∧
              tested.rd64 (slot fp (BitVec.ofNat 64 (16+7))) =
                some (if sx == sy then q+jam else q-jam) ∧
              ∃ branchTail,
                Star ⟨pc,fp⟩ m
                  ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                    BitVec.ofNat 64 (16*aligned.length)+128+
                    (if ((if sx == sy then q+jam else q-jam) == 0) then 16 else 64),fp⟩ tested ∧
                Pre L tested (pc+BitVec.ofNat 64 (16*executed.length)+256+
                  BitVec.ofNat 64 (16*aligned.length)+128+
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 16 else 64))
                  fp K (16+7) branchTail ρ W 13 ∧
                branchTail = normalization.drop
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 1 else 4) ∧
                ((if sx == sy then q+jam else q-jam) ≠ 0 →
                  2^(F.fracBits+4) < 65536^4 →
                  ∃ rightTail rightOut ex,
                    branchTail = (konstWL 4 (2^(F.fracBits+4)) (16+10)).1 ++
                      [ci 13 (16+9) (16+7) (16+10), ci 1 (16+10) 1 0,
                        ci 4 (16+9) (16+10) (16+9)] ++ rightTail ∧
                    Star ⟨pc,fp⟩ m
                      ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48,fp⟩ rightOut ∧
                    Agree fp (16+1) K m rightOut ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (16+7))) =
                      some (if sx == sy then q+jam else q-jam) ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some ex ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (16+9))) =
                      some (1-Runner.IR.bool ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4))))) ∧
                    Pre L rightOut
                      (pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48)
                      fp K (16+9) rightTail ρ W 13 ∧
                    ∃ yes leftTail shiftCode shiftTop,
                      floatShiftJamL (16+16)
                        (fun j => some ([ci 2 j (16+7) 0],j+1))
                        (fun j => some ([ci 1 j 1 0],j+1)) = some (shiftCode,shiftTop) ∧
                      yes = shiftCode ++ [ci 2 (16+7) (16+16) 0,
                        ci 3 (16+5) (16+5) (16+10)] ∧
                      rightTail = [ci 19 (16+9) (16*(yes.length+2)) 0] ++
                        yes ++ [ci 18 16 0 0] ++ leftTail ∧
                      Star ⟨pc,fp⟩ m
                        ⟨(pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48)+
                          BitVec.ofNat 64 (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then 16*(yes.length+2) else 16),fp⟩ rightOut ∧
                      Pre L rightOut ((pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48)+
                          BitVec.ofNat 64 (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then 16*(yes.length+2) else 16))
                        fp K (16+9)
                        (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then leftTail else yes ++ [ci 18 16 0 0] ++ leftTail)
                        ρ W 13 ∧
                      ((if sx == sy then q+jam else q-jam).slt (BitVec.ofNat 64 (2^(F.fracBits+4))) = false →
                        ∃ shifted,
                          Star ⟨pc,fp⟩ m
                            ⟨(pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48)+16+BitVec.ofNat 64 (16*shiftCode.length),fp⟩ shifted ∧
                          Agree fp (16+16) K rightOut shifted ∧
                          shifted.rd64 (slot fp (BitVec.ofNat 64 (16+7))) = some (if sx == sy then q+jam else q-jam) ∧
                          shifted.rd64 (slot fp (BitVec.ofNat 64 (16+16))) =
                            some (floatShiftJamWord (if sx == sy then q+jam else q-jam) 1) ∧
                          Pre L shifted ((pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (16+10)).1.length)+48)+16+BitVec.ofNat 64 (16*shiftCode.length))
                            fp K (16+17)
                            ([ci 2 (16+7) (16+16) 0, ci 3 (16+5) (16+5) (16+10)] ++
                              [ci 18 16 0 0] ++ leftTail) ρ W 13)) := by
  apply floatFiniteAddL_read_fields_align F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> decide +kernel
  · decide +kernel
  all_goals try { simp only [List.mem_cons, List.not_mem_nil, or_false] at format
                  rcases format with rfl | rfl <;> decide +kernel }
  · exact room
  · exact sortRoom
  · exact alignRoom
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre




#print axioms floatFiniteAddL_read_fields_align_zeuge

/-- Execute the rounding expression used literally by the finite candidate.
    This rounds the retained normalized word, not an independently supplied
    quotient/guard/tail triple. Relating that word to the original exact
    numerator remains the normalization continuation's obligation. -/
theorem floatFiniteAddL_round_retained {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst input top reserved : Nat} {code : List II} (q : Int)
    (range : 0 ≤ q ∧ q < 2^63)
    (compiled : floatGuardRoundL dst
      (fun j => wordK 6 j (some ([ci 2 j input 0],j+1)) 8)
      (fun j => wordK 8 j (some ([ci 2 j input 0],j+1)) 7)
      (fun j => some ([ci 1 j 0 0],j+1)) = some (code,top))
    (room : top ≤ K) (dstRoom : dst ≤ K)
    (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 q))
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code
      (· = BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat (q%8).toNat 8)) := by
  apply retainedWordCode_ok (BitVec.ofInt 64 q) _
    (fun load j => floatGuardRoundL j
      (fun k => wordK 6 k (load k) 8)
      (fun k => wordK 8 k (load k) 7)
      (fun k => some ([ci 1 k 0 0],k+1))) ?_ compiled room dstRoom lower retained read pre
  intro Δ η load
  have div := sdiv_w (a := q) (b := 8)
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
  rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg range.1] at div
  have quotient : WordCode (L := L) η (fun _ => True)
      (fun j => wordK 6 j (some ([ci 2 j input 0],j+1)) 8)
      (BitVec.ofNat 64 (q/8).toNat) := by
    have h : WordCode (L := L) η (fun _ => True) _ (BitVec.ofInt 64 (q/8)) := WordCode.bin load (WordCode.const 8 (by decide)) div
      (rfl : op 6 = bin sdiv) (by decide : 6 < 256)
    have eq : BitVec.ofInt 64 (q/8) = BitVec.ofNat 64 (q/8).toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg (Int.ediv_nonneg range.1 (by decide))]
    rw [eq] at h
    intro fp K j c t hc ht mm pp hp
    exact h (by simpa [wordK, Nat.add_assoc] using hc) ht mm pp
      (by simpa [wordK, Nat.add_assoc] using hp)
  have guard : WordCode (L := L) η (fun _ => True)
      (fun j => wordK 8 j (some ([ci 2 j input 0],j+1)) 7)
      (BitVec.ofNat 64 (q%8).toNat) := by
    have h : WordCode (L := L) η (fun _ => True) _ (BitVec.ofInt 64 q &&& 7) := WordCode.bin load (WordCode.const 7 (by decide))
      (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
    have eq : BitVec.ofInt 64 q &&& 7 = BitVec.ofNat 64 (q%8).toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [show (7 : Runner.W) = BitVec.ofNat 64 (2^3-1) from rfl,
        BitVec.toNat_and, BitVec.toNat_ofNat]
      simp only [show (2^3-1) % 2^64 = 7 from rfl]
      rw [show 7 = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt range.1 (by omega)]
      rw [BitVec.toNat_ofNat, Int.toNat_emod range.1 (by decide)]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [eq] at h
    intro fp K j c t hc ht mm pp hp
    exact h (by simpa [wordK, Nat.add_assoc] using hc) ht mm pp
      (by simpa [wordK, Nat.add_assoc] using hp)
  have rounded : WordCode (L := L) η (fun _ => True) _
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat ((q%8).toNat * 1 + 0) (8*1))) := floatGuardRoundL_ok (q/8).toNat (q%8).toNat 0 1
    (by decide) (by decide) (by omega) quotient guard
    (WordCode.const 0 (by decide))
  intro fp K j c t hc ht mm pp hp
  simpa using rounded hc ht mm pp hp

#print axioms floatFiniteAddL_round_retained

/-- An odd halfway significand is incremented by the actual retained-load
    expression, with all execution premises shared in one frame. -/
theorem floatFiniteAddL_round_retained_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K reserved : Nat}
    (read : m.rd64 (slot fp 23) = some 44)
    (room : 40 ≤ K)
    (pre : Pre L m pc fp K 32
      ((floatGuardRoundL 32
        (fun j => wordK 6 j (some ([ci 2 j 23 0],j+1)) 8)
        (fun j => wordK 8 j (some ([ci 2 j 23 0],j+1)) 7)
        (fun j => some ([ci 1 j 0 0],j+1))).getD ([],0)).1 ρ W reserved) :
    Ok m pc fp K 32
      ((floatGuardRoundL 32
        (fun j => wordK 6 j (some ([ci 2 j 23 0],j+1)) 8)
        (fun j => wordK 8 j (some ([ci 2 j 23 0],j+1)) 7)
        (fun j => some ([ci 1 j 0 0],j+1))).getD ([],0)).1
      (· = 6) := by
  exact floatFiniteAddL_round_retained 44 (by decide) rfl
    (by change 38 ≤ K; omega)
    (by omega) (by decide) (by decide) read pre

#print axioms floatFiniteAddL_round_retained_zeuge

set_option maxHeartbeats 1200000 in
/-- Execute the four literal instructions in the candidate's left-normalization
    body. Both retained fields are updated in one run; the exponent lives below
    the quotient, so the agreement boundary is the exponent slot. -/
theorem floatFiniteAddL_left_body {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex : Runner.W} (tail : List II)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (q*2) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (ex-1) ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0] ++ ([ci 5 (dst+7) (dst+7) (dst+10)] ++
        ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+5) (dst+5) (dst+10)] ++ tail)))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,rfl⟩ := const_ok (d := dst+10)
    {hp.left with ctx := by have := hp.ctx; omega} (by decide) (by omega)
  have h1 := hp.next (a1.mono (by omega : dst+5 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rq1 := slotRead_agree hp.frame a1 (by omega) (by omega) rq
  obtain ⟨m2,s2,a2,w2,r2,rfl⟩ := eng_bin_ok (d := dst+7) (a := dst+7) (b := dst+10)
    {h1.left with ctx := by have := hp.ctx; omega} (by omega) (by omega) (by omega)
    rq1 r1 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h2 := h1.next (a2.mono (by omega : dst+5 ≤ dst+7)) (Nat.le_refl _) (by omega)
  obtain ⟨m3,s3,a3,w3,r3,rfl⟩ := const_ok (d := dst+10)
    {h2.left with ctx := by have := hp.ctx; omega} (by decide) (by omega)
  have h3 := h2.next (a3.mono (by omega : dst+5 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have re3 := slotRead_agree hp.frame
    ((a1.mono (by omega : dst+7 ≤ dst+10)).trans
      (a2.trans (a3.mono (by omega : dst+7 ≤ dst+10)))) (by omega) (by omega) re
  let out := write m3 (slot fp (BitVec.ofNat 64 (dst+5))) 8 (ex-1).toNat
  obtain ⟨wr4,r4,a4⟩ := wr_slot h3.frame (by omega : dst+5 < K) (ex-1)
  have s4 : Star ⟨pc+16+16+16,fp⟩ m3 ⟨pc+16+16+16+16,fp⟩ out := by
    apply star_ins h3.left.code (by simp [ci])
    have ins := h3.left.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
    simp only [ci, op]
    have sx5 : sx (II.f ((dst : Int)+5)) = BitVec.ofNat 64 (dst+5) := by
      exact_mod_cast (sx_nat (d := dst+5) (by have := h3.small; omega))
    have sx10 : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := h3.small; omega))
    apply run_bin (g := fun x y => some (x-y)) (va := ex) (vb := 1) (r := ex-1) ins
    · simpa only [sx5] using re3
    · simpa [sx10] using r3
    · rfl
    · simpa only [sx5] using wr4
  have done := h3.next a4 (Nat.le_refl _) (by omega)
  have rq3 := slotRead_agree h2.frame a3 (by omega) (by omega) r2
  have rq4 : out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (q*2) := by
    change (write m3 _ 8 _).rd64 _ = _
    rw [rd64_write_far]
    · exact rq3
    · unfold Far
      rw [slot_toNat h3.frame.room (by omega : dst+5 < K),
        slot_toNat h3.frame.room (by omega : dst+7 < K)]
      have := h3.frame.lt
      omega
  refine ⟨out,?_,(a1.mono (by omega)).trans ((a2.mono (by omega)).trans
    ((a3.mono (by omega)).trans a4)),rq4,r4,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans s4))
  · simpa [out, BitVec.add_assoc] using done


#print axioms floatFiniteAddL_left_body

/-- The actual left body doubles the jammed word, rather than transferring an
    exact remainder bit. Carry the signed correction explicitly: it doubles too.
    This states the invariant needed by this candidate, without identifying it
    with the separate adaptive normalization routine. -/
theorem floatFiniteAddL_left_body_exact (q ex den correction numerator : Int)
    (hq : 0 ≤ q) (small : q < 2^56) (he : 1 < ex) (expBound : ex < 2^63)
    (exactRest : numerator = q*den+correction) :
    (BitVec.ofInt 64 q * 2).toInt = 2*q ∧
    (BitVec.ofInt 64 ex - 1).toInt = ex-1 ∧
    0 ≤ 2*q ∧ 2*q < 2^57 ∧ 1 ≤ ex-1 ∧
    numerator*2 = (2*q)*den + 2*correction := by
  have iq : (BitVec.ofInt 64 q).toInt = q :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  have ie : (BitVec.ofInt 64 ex).toInt = ex :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  refine ⟨?_,?_,by omega,by omega,by omega,?_⟩
  · rw [BitVec.toInt_mul, iq]
    change (q*2).bmod (2^64) = 2*q
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  · rw [BitVec.toInt_sub, ie]
    change (ex-1).bmod (2^64) = ex-1
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
  · rw [exactRest]
    ring

end Gabbro.Stage0.Senke
