module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil6

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The comparisons and both concrete branches form one executed SORT block.
    The original packed operand slots remain in place; every exchanged field
    is related to the same original frame valuation. -/
theorem floatFiniteAddL_order_execute {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II)
    (room : dst+11 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K (dst+3)
      ([ci 13 (dst+9) (dst+5) (dst+6), ci 14 (dst+10) (dst+5) (dst+6),
        ci 13 (dst+11) (dst+7) (dst+8), ci 5 (dst+10) (dst+10) (dst+11),
        ci 9 (dst+9) (dst+9) (dst+10)] ++
       ([ci 19 (dst+9) 176 0,
        ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
        ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
        ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0,
        ci 18 16 0 0] ++ tail)) ρ W reserved) :
    let swap := (values (dst+5)).slt (values (dst+6)) ||
      ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8)))
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+256,fp⟩ m' ∧ Agree fp (dst+3) K m m' ∧
      (∀ i, i < dst+9 → m'.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if swap then
          if i = dst+3 then values (dst+4) else
          if i = dst+4 then values (dst+3) else
          if i = dst+5 then values (dst+6) else
          if i = dst+6 then values (dst+5) else
          if i = dst+7 then values (dst+8) else
          if i = dst+8 then values (dst+7) else values i
         else values i)) ∧
      Pre L m' (pc+256) fp K (dst+3) tail ρ W reserved := by
  dsimp only
  obtain ⟨m1,comp,ag,flag,rest⟩ := floatFiniteAddL_order_compare room
    (reads (dst+5) (by omega)) (reads (dst+6) (by omega))
    (reads (dst+7) (by omega)) (reads (dst+8) (by omega))
    {pre with ctx := Nat.le_trans pre.ctx (by omega : dst+3 ≤ dst+9)}
  let values1 : Nat → Runner.W := fun i =>
    (m1.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0
  have reads1 : ∀ i, i < K → m1.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values1 i) := by
    intro i hi
    have hr := rest.frame.rd i hi
    simp only [values1, Runner.Mem.rd64, hr, ↓reduceIte, Option.getD_some]
  have retained : ∀ i, i < dst+9 → values1 i = values i := by
    intro i hi
    have hr := slotRead_agree pre.frame ag hi (by omega) (reads i (by omega))
    simpa [values1, hr]
  have flag1 : values1 (dst+9) = Runner.IR.bool
      ((values (dst+5)).slt (values (dst+6)) ||
       ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8)))) := by
    simp [values1, flag]
  obtain ⟨out,run,ag2,rd,done⟩ := floatFiniteAddL_swap_dispatch values1 tail _
    (by omega) reads1 flag1 {rest with ctx := pre.ctx}
  refine ⟨out,?_,(ag.mono (by omega)).trans ag2,?_,?_⟩
  · simpa [BitVec.add_assoc] using comp.trans run
  · intro i hi
    have h := rd i (by omega)
    have keep := retained i hi
    have h3 := retained (dst+3) (by omega)
    have h4 := retained (dst+4) (by omega)
    have h5 := retained (dst+5) (by omega)
    have h6 := retained (dst+6) (by omega)
    have h7 := retained (dst+7) (by omega)
    have h8 := retained (dst+8) (by omega)
    simpa [show i ≠ dst+9 by omega,keep,h3,h4,h5,h6,h7,h8] using h
  · simpa [BitVec.add_assoc] using done

#print axioms floatFiniteAddL_order_execute

theorem floatFiniteAddL_sort_continuation (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ inputs inputTop tail,
      floatStateSlotsL (dst+1)
        ([a,b,
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+2) 0],k+1))] ++
          finiteAddRemaining F dst) = some (inputs,inputTop) ∧
      code = inputs ++
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
      inputTop ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  refine ⟨inputs.1,inputs.2,code.drop (inputs.1.length+16),?_,?_,?_⟩
  · simpa [finiteAddRemaining] using hi
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    rw [← result.1]
    simp [List.drop_append, List.append_assoc]
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    omega


#print axioms floatFiniteAddL_sort_continuation

/-- The actual comparison flag orders the selected exponent/significand pair
    lexicographically, including equal magnitudes. -/
theorem finiteAdd_order_dominance (ex ey q r : Runner.W) :
    let swap := ex.slt ey || ((ex == ey) && q.slt r)
    let bigE := if swap then ey else ex
    let smallE := if swap then ex else ey
    let bigM := if swap then r else q
    let smallM := if swap then q else r
    smallE.toInt ≤ bigE.toInt ∧ (smallE = bigE → smallM.toInt ≤ bigM.toInt) := by
  dsimp only
  by_cases h : (ex.slt ey || ((ex == ey) && q.slt r)) = true
  · simp [h]
    simp only [Bool.or_eq_true, Bool.and_eq_true, BitVec.slt_eq_decide,
      decide_eq_true_eq, beq_iff_eq, ← BitVec.toInt_inj] at h
    constructor
    · omega
    · intro eq
      have he := congrArg BitVec.toInt eq
      omega
  · simp [h]
    simp only [Bool.or_eq_true, Bool.and_eq_true, BitVec.slt_eq_decide,
      decide_eq_true_eq, beq_iff_eq, ← BitVec.toInt_inj] at h
    constructor
    · omega
    · intro eq
      have he := congrArg BitVec.toInt eq
      omega

#print axioms finiteAdd_order_dominance

/-- Turn the executed joint field correspondence into an ordered machine
    state, rather than an ordering assertion detached from memory reads. -/
theorem finiteAdd_ordered_memory {out : Runner.Mem} {fp : Runner.W} {dst : Nat}
    (values : Nat → Runner.W)
    (reads : ∀ i, i < dst+9 → out.rd64 (slot fp (BitVec.ofNat 64 i)) = some
      (if (values (dst+5)).slt (values (dst+6)) ||
          ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8))) then
        if i = dst+3 then values (dst+4) else
        if i = dst+4 then values (dst+3) else
        if i = dst+5 then values (dst+6) else
        if i = dst+6 then values (dst+5) else
        if i = dst+7 then values (dst+8) else
        if i = dst+8 then values (dst+7) else values i
       else values i)) :
    ∃ ex ey q r : Runner.W,
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r ∧
      ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt) := by
  let swap := (values (dst+5)).slt (values (dst+6)) ||
    ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8)))
  refine ⟨if swap then values (dst+6) else values (dst+5),
    if swap then values (dst+5) else values (dst+6),
    if swap then values (dst+8) else values (dst+7),
    if swap then values (dst+7) else values (dst+8),?_,?_,?_,?_,?_⟩
  · simpa [swap] using reads (dst+5) (by omega)
  · simpa [swap] using reads (dst+6) (by omega)
  · simpa [swap] using reads (dst+7) (by omega)
  · simpa [swap] using reads (dst+8) (by omega)
  · exact finiteAdd_order_dominance _ _ _ _

#print axioms finiteAdd_ordered_memory


end Gabbro.Stage0.Senke
