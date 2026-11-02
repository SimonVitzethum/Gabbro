module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil12

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


end Gabbro.Stage0.Senke
