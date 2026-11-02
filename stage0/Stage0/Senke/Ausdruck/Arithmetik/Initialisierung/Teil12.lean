module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil11
@[expose] public section
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxHeartbeats 6000000 in
/-- Execute decoding, SORT, alignment and signed ADD/SUB from encoded operands.
    The exact correction and arithmetic result belong to one connected run. -/
theorem floatFiniteAddL_read_fields_align {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (sortRoom : dst+11 < K) (alignRoom : dst+17 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail aligned continuation alignTop, ∃ values : Nat → Runner.W, ∃ out,
      code = executed ++
        ([ci 13 (dst+9) (dst+5) (dst+6),
          ci 14 (dst+10) (dst+5) (dst+6),
          ci 13 (dst+11) (dst+7) (dst+8),
          ci 5 (dst+10) (dst+10) (dst+11),
          ci 9 (dst+9) (dst+9) (dst+10),
          ci 19 (dst+9) 176 0,
          ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
          ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
          ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0,
          ci 18 16 0 0] ++ tail) ∧
      tail = aligned ++ continuation ∧
      floatShiftJamL (dst+16)
        (fun j => some ([ci 2 j (dst+8) 0],j+1))
        (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
          (some ([ci 2 (j+1) (dst+6) 0],j+2))) = some (aligned,alignTop) ∧
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.length),fp⟩ out ∧
      Agree fp (dst+1) K m out ∧
      (∀ i, i < 8 → values (dst+1+i) =
        match i with
        | 0 => wa
        | 1 => wb
        | 2 => floatFieldWord wa (F.fracBits+F.ebits) 1
        | 3 => floatFieldWord wb (F.fracBits+F.ebits) 1
        | _ => finiteAddRemainingValue F wa wb (i-4)) ∧
      (∀ i, i < dst+9 → out.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if (values (dst+5)).slt (values (dst+6)) ||
            ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8))) then
          if i = dst+3 then values (dst+4) else
          if i = dst+4 then values (dst+3) else
          if i = dst+5 then values (dst+6) else
          if i = dst+6 then values (dst+5) else
          if i = dst+7 then values (dst+8) else
          if i = dst+8 then values (dst+7) else values i
         else values i)) ∧
      (∃ ex ey q r : Runner.W,
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r ∧
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt) ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) =
          some (floatShiftJamWord r (ex-ey)) ∧
        ∃ sx sy jam : Runner.W,
          out.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) = some sx ∧
          out.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) = some sy ∧
          out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) = some jam ∧
          let signX : Int := if sx = 0 then 1 else -1
          let signY : Int := if sy = 0 then 1 else -1
          let denominator : Int := (2^(ex-ey).toNat : Nat)
          let quotient : Int := (r.toNat / 2^(ex-ey).toNat : Nat)
          let remainder : Int := (r.toNat % 2^(ex-ey).toNat : Nat)
          (signX*(q.toNat : Int) + signY*(jam.toNat : Int))*denominator +
            signY*(remainder - ((jam.toNat : Int)-quotient)*denominator) =
            signX*(q.toNat : Int)*denominator + signY*(r.toNat : Int)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.length))
        fp K (dst+17) continuation ρ W reserved ∧
      ∃ out2 sx sy q jam,
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) = some sx ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) = some sy ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) = some jam ∧
        Star ⟨pc,fp⟩ m
          ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.length)+96,fp⟩ out2 ∧
        Agree fp (dst+1) K m out2 ∧
        out2.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) =
          some (if sx == sy then q+jam else q-jam) ∧
        ((∀ i, i < 4 →
            if i < 2 then 1 ≤ (finiteAddRemainingValue F wa wb i).toNat ∧
              (finiteAddRemainingValue F wa wb i).toNat < F.bexpMax
            else (finiteAddRemainingValue F wa wb i).toNat < 2^56) →
          ∃ ex ey : Runner.W,
            out2.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
            out2.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
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
              wa = BitVec.ofNat 64 (Gleitkomma.zuBits F x) →
              wb = BitVec.ofNat 64 (Gleitkomma.zuBits F y) →
              (if sx == sy then q+jam else q-jam) ≠ 0 →
              0 < (if sx == sy then q+jam else q-jam).toInt) ∧
            ∃ source : Runner.W,
              out.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some source ∧
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
          continuation = [ci 2 (dst+8) (dst+16) 0,
            ci 14 (dst+9) (dst+3) (dst+4), ci 19 (dst+9) 48 0,
            ci 3 (dst+7) (dst+7) (dst+8), ci 18 32 0 0,
            ci 4 (dst+7) (dst+7) (dst+8)] ++ signedTail ∧
          Pre L out2 (pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.length)+96) fp K (dst+7)
            signedTail ρ W reserved ∧
          ∃ normalization,
            signedTail = [ci 1 (dst+10) 0 0,
              ci 14 (dst+9) (dst+7) (dst+10)] ++ normalization ∧
            ∃ tested,
              Star ⟨pc,fp⟩ m
                ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                  BitVec.ofNat 64 (16*aligned.length)+128,fp⟩ tested ∧
              Agree fp (dst+1) K m tested ∧
              tested.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
                some (Runner.IR.bool ((if sx == sy then q+jam else q-jam) == 0)) ∧
              Pre L tested (pc+BitVec.ofNat 64 (16*executed.length)+256+
                BitVec.ofNat 64 (16*aligned.length)+128) fp K (dst+7)
                normalization ρ W reserved ∧
              Agree fp (dst+9) K out2 tested ∧
              tested.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) =
                some (if sx == sy then q+jam else q-jam) ∧
              ∃ branchTail,
                Star ⟨pc,fp⟩ m
                  ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                    BitVec.ofNat 64 (16*aligned.length)+128+
                    (if ((if sx == sy then q+jam else q-jam) == 0) then 16 else 64),fp⟩ tested ∧
                Pre L tested (pc+BitVec.ofNat 64 (16*executed.length)+256+
                  BitVec.ofNat 64 (16*aligned.length)+128+
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 16 else 64))
                  fp K (dst+7) branchTail ρ W reserved ∧
                branchTail = normalization.drop
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 1 else 4) ∧
                ((if sx == sy then q+jam else q-jam) ≠ 0 →
                  2^(F.fracBits+4) < 65536^4 →
                  ∃ rightTail rightOut ex,
                    branchTail = (konstWL 4 (2^(F.fracBits+4)) (dst+10)).1 ++
                      [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
                        ci 4 (dst+9) (dst+10) (dst+9)] ++ rightTail ∧
                    Star ⟨pc,fp⟩ m
                      ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48,fp⟩ rightOut ∧
                    Agree fp (dst+1) K m rightOut ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) =
                      some (if sx == sy then q+jam else q-jam) ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
                    rightOut.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
                      some (1-Runner.IR.bool ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4))))) ∧
                    Pre L rightOut
                      (pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)
                      fp K (dst+9) rightTail ρ W reserved ∧
                    ∃ yes leftTail shiftCode shiftTop,
                      floatShiftJamL (dst+16)
                        (fun j => some ([ci 2 j (dst+7) 0],j+1))
                        (fun j => some ([ci 1 j 1 0],j+1)) = some (shiftCode,shiftTop) ∧
                      yes = shiftCode ++ [ci 2 (dst+7) (dst+16) 0,
                        ci 3 (dst+5) (dst+5) (dst+10)] ∧
                      rightTail = [ci 19 (dst+9) (16*(yes.length+2)) 0] ++
                        yes ++ [ci 18 16 0 0] ++ leftTail ∧
                      Star ⟨pc,fp⟩ m
                        ⟨(pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)+
                          BitVec.ofNat 64 (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then 16*(yes.length+2) else 16),fp⟩ rightOut ∧
                      Pre L rightOut ((pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)+
                          BitVec.ofNat 64 (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then 16*(yes.length+2) else 16))
                        fp K (dst+9)
                        (if ((if sx == sy then q+jam else q-jam).slt
                        (BitVec.ofNat 64 (2^(F.fracBits+4)))) then leftTail else yes ++ [ci 18 16 0 0] ++ leftTail)
                        ρ W reserved ∧
                      ((if sx == sy then q+jam else q-jam).slt (BitVec.ofNat 64 (2^(F.fracBits+4))) = false →
                        ∃ shifted,
                          Star ⟨pc,fp⟩ m
                            ⟨(pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)+16+BitVec.ofNat 64 (16*shiftCode.length),fp⟩ shifted ∧
                          Agree fp (dst+16) K rightOut shifted ∧
                          shifted.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (if sx == sy then q+jam else q-jam) ∧
                          shifted.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) =
                            some (floatShiftJamWord (if sx == sy then q+jam else q-jam) 1) ∧
                          Pre L shifted ((pc+BitVec.ofNat 64 (16*executed.length)+256+
                        BitVec.ofNat 64 (16*aligned.length)+192+
                        BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)+16+BitVec.ofNat 64 (16*shiftCode.length))
                            fp K (dst+17)
                            ([ci 2 (dst+7) (dst+16) 0, ci 3 (dst+5) (dst+5) (dst+10)] ++
                              [ci 18 16 0 0] ++ leftTail) ρ W reserved)) := by
  obtain ⟨executed,fieldTail,before,hcode,run,ag,ra,rb,rsx,rsy,fields,rest,it,hi⟩ :=
    floatFiniteAddL_read_fields F dst a b wa wb compiled width lower frac mask
      fracMask hiddenBound room (by omega) producerA producerB pre
  obtain ⟨inputs,inputTop,tail,hinputs,hfull,_⟩ :=
    floatFiniteAddL_sort_continuation F dst a b compiled
  have heq : inputs = executed := by
    rw [hi] at hinputs
    exact (Prod.mk.inj (Option.some.inj hinputs)).1.symm
  subst inputs
  have ht := List.append_cancel_left (hcode.symm.trans hfull)
  rw [ht] at rest
  let values : Nat → Runner.W := fun i =>
    (before.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0
  have reads : ∀ i, i < K → before.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i) := by
    intro i hi
    have hr := rest.frame.rd i hi
    simp only [values, Runner.Mem.rd64, hr, ↓reduceIte, Option.getD_some]
  obtain ⟨out,sortRun,sortAgree,sorted,done⟩ := floatFiniteAddL_order_execute
    (dst := dst) values tail sortRoom reads
    {rest with ctx := Nat.le_trans pre.ctx (by omega : dst+1 ≤ dst+3)}
  have fieldValues : ∀ i, i < 8 → values (dst+1+i) =
        match i with
        | 0 => wa
        | 1 => wb
        | 2 => floatFieldWord wa (F.fracBits+F.ebits) 1
        | 3 => floatFieldWord wb (F.fracBits+F.ebits) 1
        | _ => finiteAddRemainingValue F wa wb (i-4) :=
    floatFiniteAddL_read_fields_align_fields F dst a b wa wb compiled width lower frac mask fracMask hiddenBound room sortRoom alignRoom executed before ra rb rsx rsy fields it hi
  have hc := compiled
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at hc
  obtain ⟨ins,his,aligned,ha,shift,hs,rounded,hr,result⟩ := hc
  have hie : ins.1 = executed := by
    have eq : some ins = some (executed,inputTop) :=
      his.symm.trans (by simpa [finiteAddRemaining] using hinputs)
    exact (Prod.mk.inj (Option.some.inj eq)).1
  simp only [Option.some.injEq, Prod.mk.injEq] at result
  have tailShape : ∃ continuation, tail = aligned.1 ++ continuation := by
    have eq := congrArg (fun xs : List II => xs.drop (executed.length+16))
      (hfull.symm.trans result.1.symm)
    rw [hie] at eq
    simp [List.drop_append, List.append_assoc] at eq
    exact ⟨_,eq⟩
  obtain ⟨continuation,tailEq⟩ := tailShape
  obtain ⟨ex,ey,q,r,rx,ry,rq,rr,dominance⟩ := finiteAdd_ordered_memory values sorted
  rw [tailEq] at done
  obtain ⟨final,alignRun,alignAgree,jammed,finalPre⟩ :=
    floatFiniteAddL_align_execute (by omega : FB ≤ dst+5)
      (by omega : aligned.2 ≤ K) alignRoom rx ry rr ha
      {done with ctx := Nat.le_trans done.ctx (by omega : dst+3 ≤ dst+16)}
  have keep : ∀ i, i < dst+9 → final.rd64 (slot fp (BitVec.ofNat 64 i)) =
      out.rd64 (slot fp (BitVec.ofNat 64 i)) := by
    intro i hi
    exact agree_rd_low alignAgree done.frame.room (by omega) (by omega)
  have signedShape : ∃ rest, continuation =
      [ci 2 (dst+8) (dst+16) 0, ci 14 (dst+9) (dst+3) (dst+4),
        ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
        ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ rest := by
    have eq := hfull.symm.trans result.1.symm
    rw [hie,tailEq] at eq
    simp [List.append_assoc] at eq
    exact ⟨_,eq⟩
  obtain ⟨signedTail,signedEq⟩ := signedShape
  have normalizationShape : ∃ normalization, signedTail =
      [ci 1 (dst+10) 0 0, ci 14 (dst+9) (dst+7) (dst+10)] ++ normalization := by
    have eq := hfull.symm.trans result.1.symm
    rw [hie,tailEq,signedEq] at eq
    simp [List.append_assoc] at eq
    exact ⟨_,eq⟩
  let vs : Nat → Runner.W := fun i => (final.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0
  have vreads : ∀ i, i < K → final.rd64 (slot fp (BitVec.ofNat 64 i)) = some (vs i) := by
    intro i hi
    have hr := finalPre.frame.rd i hi
    simp only [vs, Runner.Mem.rd64, hr, ↓reduceIte, Option.getD_some]
  have signedPre := finalPre
  rw [signedEq] at signedPre
  obtain ⟨signedOut,signedRun,signedAgree,signedRead,signedRest⟩ :=
    floatFiniteAddL_signed_execute vs signedTail (by omega) vreads
      {signedPre with ctx := Nat.le_trans pre.ctx (by omega : dst+1 ≤ dst+7)}
  have wholeRun := run.trans (sortRun.trans alignRun)
  have wholeAgree := ag.trans ((sortAgree.mono (by omega : dst+1 ≤ dst+3)).trans
    (alignAgree.mono (by omega : dst+1 ≤ dst+16)))
  obtain ⟨normalization,normalizationEq⟩ := normalizationShape
  have headerPre := signedRest
  rw [normalizationEq] at headerPre
  have hp : Pre L signedOut
      (pc+BitVec.ofNat 64 (16*executed.length)+256+
        BitVec.ofNat 64 (16*aligned.1.length)+96) fp K (dst+7)
      ([ci 1 (dst+10) 0 0] ++
        ([ci 14 (dst+9) (dst+7) (dst+10)] ++ normalization)) ρ W reserved := headerPre
  obtain ⟨zeroMem,zeroRun,zeroAgree,zeroWord,zeroRead,zeroEq⟩ :=
    const_ok (d := dst+10)
      {hp.left with ctx := by have := hp.ctx; omega} (by decide) (by omega)
  subst zeroWord
  have cmpPre := hp.next (zeroAgree.mono (by omega : dst+7 ≤ dst+10))
    (Nat.le_refl _) (by omega)
  have qr := slotRead_agree hp.frame zeroAgree (by omega) (by omega) signedRead
  obtain ⟨tested,testRun,testAgree,testWord,testRead,testEq⟩ :=
    eng_bin_ok (a := dst+7) (b := dst+10) (d := dst+9) (o := 14)
      {cmpPre.left with ctx := by have := cmpPre.ctx; omega}
      (by omega) (by omega) (by omega) qr zeroRead
      (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst testWord
  have testedPre := cmpPre.next (testAgree.mono (by omega : dst+7 ≤ dst+9))
    (Nat.le_refl _) (by omega)
  have branchShape : ∃ jump rest, normalization =
      [ci 19 (dst+9) 64 0, ci 5 (dst+3) (dst+3) (dst+4),
        ci 1 (dst+7) 0 0, jump] ++ rest := by
    have eq := hfull.symm.trans result.1.symm
    rw [hie,tailEq,signedEq,normalizationEq] at eq
    simp [List.append_assoc] at eq
    exact ⟨_,_,eq⟩
  obtain ⟨endJump,normalRest,branchEq⟩ := branchShape
  have bp := testedPre
  rw [branchEq] at bp
  have branchIns : Runner.IR.InsAt tested
      (pc+BitVec.ofNat 64 (16*executed.length)+256+
        BitVec.ofNat 64 (16*aligned.1.length)+96+16+16)
      19 (II.f ((dst+9 : Nat) : Int)) (II.f 64) (II.f 0) := by
    simpa [ci] using bp.code 0 (by simp)
  have branchRead : tested.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) =
      some (Runner.IR.bool ((if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)) == 0)) := by
    rw [sx_nat (by have := bp.small; omega)]
    exact testRead
  have branchDone : ∃ branchTail,
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+
          BitVec.ofNat 64 (16*aligned.1.length)+128+
          (if ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
            else vs (dst+7)-vs (dst+16)) == 0) then 16 else 64),fp⟩ tested ∧
      Pre L tested (pc+BitVec.ofNat 64 (16*executed.length)+256+
        BitVec.ofNat 64 (16*aligned.1.length)+128+
        (if ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
          else vs (dst+7)-vs (dst+16)) == 0) then 16 else 64))
        fp K (dst+7) branchTail ρ W reserved ∧
      branchTail = normalization.drop
        (if ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
          else vs (dst+7)-vs (dst+16)) == 0) then 1 else 4) :=
    floatFiniteAddL_read_fields_align_branch F dst width lower frac mask fracMask hiddenBound room sortRoom alignRoom executed before tail rest aligned final signedOut signedRun wholeRun normalization zeroMem zeroRun tested testRun endJump normalRest branchEq bp branchIns branchRead
  refine ⟨executed,tail,aligned.1,continuation,aligned.2,values,final,hfull,
    tailEq,ha,run.trans (sortRun.trans alignRun),
    ag.trans ((sortAgree.mono (by omega)).trans (alignAgree.mono (by omega))),
    fieldValues,?_,?_,finalPre,signedOut,vs (dst+3),vs (dst+4),vs (dst+7),vs (dst+16),
    vreads _ (by omega),vreads _ (by omega),vreads _ (by omega),vreads _ (by omega),
    wholeRun.trans signedRun,wholeAgree.trans (signedAgree.mono (by omega)),
    signedRead,?_,signedTail,signedEq,signedRest,normalization,normalizationEq,
    tested,?_,?_,testRead,?_,?_,?_,?_⟩
  · intro i hi
    rw [keep i hi]
    exact sorted i hi
  · refine ⟨ex,ey,q,r,(keep _ (by omega)).trans rx,(keep _ (by omega)).trans ry,
      (keep _ (by omega)).trans rq,(keep _ (by omega)).trans rr,
      dominance.1,dominance.2,jammed,?_⟩
    let sx := (final.rd64 (slot fp (BitVec.ofNat 64 (dst+3)))).getD 0
    let sy := (final.rd64 (slot fp (BitVec.ofNat 64 (dst+4)))).getD 0
    have signRead (i : Nat) (hi : i < K) :
        final.rd64 (slot fp (BitVec.ofNat 64 i)) =
          some ((final.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0) := by
      have hr := finalPre.frame.rd i hi
      simp only [Runner.Mem.rd64, hr, ↓reduceIte, Option.getD_some]
    refine ⟨sx,sy,floatShiftJamWord r (ex-ey),signRead _ (by omega),
      signRead _ (by omega),jammed,?_⟩
    exact floatShiftJamWord_signed_exact r (ex-ey) (q.toNat : Int)
      (if sx = 0 then 1 else -1) (if sy = 0 then 1 else -1)
  · have hb := @floatFiniteAddL_read_fields_align_bounds _ D L Γ ρ W F dst a b wa wb top K reserved fp pc m width lower frac mask fracMask hiddenBound room sortRoom alignRoom executed before it hi
    exact hb out sorted fieldValues aligned shift hs rounded hr continuation ex ey q r rx ry rq rr dominance final jammed finalPre keep vreads signedOut signedRun signedAgree wholeRun wholeAgree normalization zeroMem zeroRun zeroAgree cmpPre qr tested testRun testAgree testedPre
  · simpa [BitVec.add_assoc] using
      wholeRun.trans (signedRun.trans (zeroRun.trans testRun))
  · exact wholeAgree.trans ((signedAgree.trans
      ((zeroAgree.mono (by omega)).trans (testAgree.mono (by omega)))).mono (by omega))
  · simpa [BitVec.add_assoc] using testedPre
  · exact (zeroAgree.mono (by omega : dst+9 ≤ dst+10)).trans testAgree
  · exact slotRead_agree cmpPre.frame testAgree (by omega) (by omega) qr
  · obtain ⟨branchTail,branchRun,branchPre,branchShape⟩ := branchDone
    refine ⟨branchTail,branchRun,branchPre,branchShape,?_⟩
    intro nz thresholdRange
    have hz : ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
      else vs (dst+7)-vs (dst+16)) == 0) = false := by
      cases h : ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
        else vs (dst+7)-vs (dst+16)) == (0 : Runner.W)) with
      | false => rfl
      | true => exact False.elim (nz (by simpa only [beq_iff_eq] using h))
    have selected : branchTail = normalRest := by
      rw [hz, branchEq] at branchShape
      simpa using branchShape
    have rightShape : ∃ rightTail, normalRest =
        (konstWL 4 (2^(F.fracBits+4)) (dst+10)).1 ++
        [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 4 (dst+9) (dst+10) (dst+9)] ++ rightTail := by
      have eq := hfull.symm.trans result.1.symm
      rw [hie,tailEq,signedEq,normalizationEq,branchEq] at eq
      simp [List.append_assoc] at eq
      refine ⟨normalRest.drop ((konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length+3), ?_⟩
      rw [eq.2]
      simp [List.drop_append, List.append_assoc]
    obtain ⟨rightTail,rightShape⟩ := rightShape
    rw [hz] at branchRun branchPre
    simp only [Bool.false_eq_true, ↓reduceIte] at branchRun branchPre
    have offset :
        (pc+BitVec.ofNat 64 (16*executed.length)+256+
          BitVec.ofNat 64 (16*aligned.1.length))+128+64 =
        (pc+BitVec.ofNat 64 (16*executed.length)+256+
          BitVec.ofNat 64 (16*aligned.1.length))+192 := by
      exact (BitVec.add_assoc _ _ _).trans
        (congrArg (fun z : Runner.W =>
          (pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.1.length))+z)
          (by decide : (128 : Runner.W)+64 = 192))
    rw [offset] at branchRun branchPre
    have rightPre := branchPre
    rw [selected,rightShape] at rightPre
    have resultRead := slotRead_agree cmpPre.frame testAgree (by omega) (by omega) qr
    let e := (tested.rd64 (slot fp (BitVec.ofNat 64 (dst+5)))).getD 0
    have exponentRead : tested.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some e := by
      have rd := testedPre.frame.rd (dst+5) (by omega)
      simp only [e,Runner.Mem.rd64,rd,↓reduceIte,Option.getD_some]
    obtain ⟨rightOut,rightRun,rightAgree,rq,re,flag,done⟩ :=
      floatFiniteAddL_right_condition F rightTail thresholdRange (by omega)
        resultRead exponentRead
        {rightPre with ctx := Nat.le_trans rightPre.ctx (by omega : dst+7 ≤ dst+9)}
    refine ⟨rightTail,rightOut,e,selected.trans rightShape,?_,?_,rq,re,flag,?_⟩
    · exact branchRun.trans rightRun
    · exact (wholeAgree.trans ((signedAgree.trans
        ((zeroAgree.mono (by omega)).trans (testAgree.mono (by omega)))).mono (by omega))).trans
        (rightAgree.mono (by omega))
    · refine ⟨done, ?_⟩
      let yes := shift.1 ++ [ci 2 (dst+7) (dst+16) 0, ci 3 (dst+5) (dst+5) (dst+10)]
      have shape : ∃ leftTail, rightTail =
          [ci 19 (dst+9) (16*(yes.length+2)) 0] ++ yes ++ [ci 18 16 0 0] ++ leftTail := by
        have eq := hfull.symm.trans result.1.symm
        rw [hie,tailEq,signedEq,normalizationEq,branchEq,rightShape] at eq
        simp [List.append_assoc] at eq
        exact ⟨_, by simpa [yes, List.append_assoc, Nat.add_assoc] using eq.2⟩
      obtain ⟨leftTail,shape⟩ := shape
      have range : 16*(yes.length+2) < 2^31 := by
        have shiftEq := hs
        simp [floatShiftJamL, floatShiftQuotL, wordL, wordK] at shiftEq
        obtain ⟨rfl,rfl⟩ := shiftEq
        simp [yes, bin2]
      have branchPre := done
      rw [shape] at branchPre
      obtain ⟨dispatch,dispatchPre⟩ := floatFiniteAddL_right_branch yes leftTail
        _ (by omega) range flag branchPre
      refine ⟨yes,leftTail,shift.1,shift.2,hs,rfl,shape,
        (branchRun.trans rightRun).trans dispatch,dispatchPre,?_⟩
      intro notSmall
      rw [notSmall] at dispatch dispatchPre
      simp only [Bool.false_eq_true, ↓reduceIte] at dispatch dispatchPre
      have shiftPre : Pre L rightOut
          (pc+BitVec.ofNat 64 (16*executed.length)+256+
            BitVec.ofNat 64 (16*aligned.1.length)+192+
            BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48+16)
          fp K (dst+9)
        (shift.1 ++ ([ci 2 (dst+7) (dst+16) 0, ci 3 (dst+5) (dst+5) (dst+10)] ++
          [ci 18 16 0 0] ++ leftTail)) ρ W reserved := by
        simpa only [yes,List.append_assoc,BitVec.ofNat_eq_ofNat] using dispatchPre
      have shiftRoom : shift.2 ≤ K := by have := result.2; omega
      obtain ⟨shifted,shiftRun,shiftAgree,shiftQ,shiftValue,shiftDone⟩ :=
        floatFiniteAddL_right_shift (by omega) shiftRoom (by omega) rq hs
          {shiftPre with ctx := Nat.le_trans shiftPre.ctx (by omega : dst+9 ≤ dst+16)}
      exact ⟨shifted,((branchRun.trans rightRun).trans dispatch).trans shiftRun,
        shiftAgree,shiftQ,shiftValue,shiftDone⟩
#print axioms floatFiniteAddL_read_fields_align

end Gabbro.Stage0.Senke
