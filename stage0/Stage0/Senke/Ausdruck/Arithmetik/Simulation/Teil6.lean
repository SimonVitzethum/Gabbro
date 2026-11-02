module
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil6a

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil5

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

private abbrev normalizeWordTy : Ty := .int (-2^63) (2^63-1)

private theorem normalizeFrameEnv {m : Runner.Mem} {fp : Runner.W} {K n : Nat}
    (frame : FrameOK m fp K) (room : FB+n ≤ K) :
    ∃ ρ : Env D (List.replicate n normalizeWordTy), EnvAt L m fp ρ := by
  induction n with
  | zero => exact ⟨Env.nil, fun _ x => nomatch x⟩
  | succ n ih =>
    obtain ⟨ρ, env⟩ := ih (by omega)
    obtain ⟨w, read⟩ : ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (FB+n))) = some w := by
      simp only [Runner.Mem.rd64, frame.rd (FB+n) (by omega), ↓reduceIte]
      exact ⟨_, rfl⟩
    let z : Zahl (-2^63) (2^63-1) :=
      ⟨w.toInt, by simpa using BitVec.le_toInt w, by simpa using BitVec.toInt_le (x := w)⟩
    refine ⟨Env.cons z ρ, envAt_cons env ?_⟩
    exact ValueAt.of_enc (by decide) (by simpa [frei] using read) BitVec.ofInt_toInt.symm

private theorem normalizeFrameVar (n i : Nat) (hi : i < n) :
    ∃ x : Var (List.replicate n normalizeWordTy) normalizeWordTy, vslot x = FB+i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · obtain ⟨x, hx⟩ := ih h
      exact ⟨Var.there x, by simpa only [vslot_there] using hx⟩
    · exact ⟨Var.here, by simp [vslot_here, frei]; omega⟩

private theorem normalizeContextLoad {Δ : Ctx} (η : Env D Δ)
    (x : Var Δ normalizeWordTy) (i : Nat) (hx : vslot x = i) :
    WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j i 0], j+1)) (BitVec.ofInt 64 (η.get x).n) := by
  intro fp K j c t hc ht m pc hp
  cases hc
  obtain ⟨w, hr, he⟩ := ValueAt.word normalizeWordTy _ trivial (hp.env _ x)
  rw [hx] at hr
  change w = BitVec.ofInt 64 (η.get x).n at he
  subst w
  have bound : i < j := by
    have := variableOffset_bound x
    have hw : valueWords normalizeWordTy = 1 := by decide
    have := hp.ctx
    simp only [vslot, frei] at hx this
    omega
  exact mov_ok hp (by omega) (by omega) hr

#print axioms normalizeFrameEnv
#print axioms normalizeContextLoad

/-- Execute an adaptive arithmetic result from concrete retained frame inputs.
    The auxiliary environment is constructed from memory, never assumed. -/
theorem floatNormalizeStepL_slots
    {m : Runner.Mem} {entryPc : Runner.W} {out : Bool} {dst : Nat}
    {body : List II} {limit : Nat} (q r den target : Int)
    (hq : 0 ≤ q ∧ q < 2^62) (hd : 0 < den ∧ den < 2^62)
    (hr : 0 ≤ r ∧ r < den) (ht : 0 ≤ target ∧ target < 2^62)
    (hc : floatNormalizeStepL out dst
      (fun j => some ([ci 2 j base 0], j+1))
      (fun j => some ([ci 2 j (base+1) 0], j+1))
      (fun j => some ([ci 2 j (base+7) 0], j+1))
      (fun j => some ([ci 2 j (base+3) 0], j+1)) = some (body, limit))
    (hp : Pre L m entryPc fp K dst body ρ W reserved)
    (hb : FB ≤ base) (free : base+8 ≤ dst) (room : limit ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 q))
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r))
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some (BitVec.ofInt 64 den))
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target)) :
    Ok m entryPc fp K dst body (· = BitVec.ofInt 64
      (if out then (floatNormalizeStep q r den target).2
       else (floatNormalizeStep q r den target).1)) := by
  have dstBound : dst < limit := by
    unfold floatNormalizeStepL at hc
    cases out <;> simp [wordL] at hc <;>
      obtain ⟨rfl, rfl⟩ := hc <;> omega
  obtain ⟨η, env⟩ := normalizeFrameEnv (L := L) (n := base+8-FB) hp.frame (by omega)
  have producer (i : Nat) (hi : base ≤ i) (hi' : i < base+8)
      (v : Int) (hv : -2^63 ≤ v ∧ v < 2^63)
      (read : m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (BitVec.ofInt 64 v)) :
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j i 0], j+1)) (BitVec.ofInt 64 v) := by
    obtain ⟨x, hx⟩ := normalizeFrameVar (base+8-FB) (i-FB) (by omega)
    have hx' : vslot x = i := by omega
    obtain ⟨w, read', enc⟩ := ValueAt.word normalizeWordTy _ trivial (env _ x)
    rw [hx', read] at read'
    cases read'
    change BitVec.ofInt 64 v = BitVec.ofInt 64 (η.get x).n at enc
    have eq := congrArg BitVec.toInt enc
    rw [toInt_ofInt_in hv.1 hv.2,
      toInt_ofInt_in (η.get x).lo_le (by have := (η.get x).le_hi; omega)] at eq
    rw [eq]
    intro fp' K' j c t hc ht m' pc' hp'
    exact normalizeContextLoad (L := L) η x i hx' hc ht m' pc' hp'
  have pre : Pre L m entryPc fp K dst body η (fun _ => True) :=
    ⟨by simp [frei]; omega, hp.small, hp.frame, hp.code, hp.far,
      env, trivial, wstab_true _ _⟩
  exact floatNormalizeStepL_ok q r den target out hq hd hr ht
    (producer base (by omega) (by omega) q (by constructor <;> omega) rq)
    (producer (base+1) (by omega) (by omega) r (by constructor <;> omega) rr)
    (producer (base+7) (by omega) (by omega) den (by constructor <;> omega) rd)
    (producer (base+3) (by omega) (by omega) target (by constructor <;> omega) rt)
    hc room m entryPc pre

#print axioms floatNormalizeStepL_slots

set_option maxHeartbeats 1600000 in
/-- Run both real SMALL arithmetic expressions, retaining the six head slots.
    The output words are ready for the emitted copies, without assuming a body. -/
theorem floatNormalizeLoopL_small_calculation
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (ceiling : top ≤ K) (small : distance ≤ 61)
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
      some (BitVec.ofInt 64 ((2 : Int)^distance))) :
    ∃ m', Star ⟨pc+384, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩ m' ∧
      Agree fp (base+8) K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+8))) =
        some (BitVec.ofInt 64 (floatNormalizeStep q r (2^distance) target).1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+9))) =
        some (BitVec.ofInt 64 (floatNormalizeStep q r (2^distance) target).2) := by
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  obtain ⟨cq, eqQ⟩ : ∃ cq, floatNormalizeStepL false (base+8)
      (load base) (load (base+1)) (load (base+7)) (load (base+3)) = some cq := by
    simp [floatNormalizeStepL, load, wordL]
  obtain ⟨cr, eqR⟩ : ∃ cr, floatNormalizeStepL true (base+9)
      (load base) (load (base+1)) (load (base+7)) (load (base+3)) = some cr := by
    simp [floatNormalizeStepL, load, wordL]
  have shape : base+9 < top ∧ cq.2 ≤ top ∧ cr.2 ≤ top ∧
      24+cq.1.length+cr.1.length = code.length-6 ∧
      24+cq.1.length+cr.1.length ≤ code.length ∧
      (∀ i, i < cq.1.length → code[24+i]? = cq.1[i]?) ∧
      (∀ i, i < cr.1.length → code[24+cq.1.length+i]? = cr.1[i]?) := by
    simp [floatNormalizeStepL, load, wordL] at eqQ eqR
    obtain ⟨rfl, rfl⟩ := eqQ
    obtain ⟨rfl, rfl⟩ := eqR
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
    constructor <;> intro i hi <;> interval_cases i <;> norm_num
  have part (start : Nat) (body : List II)
      (bound : start+body.length ≤ code.length)
      (entries : ∀ i, i < body.length → code[start+i]? = body[i]?) :
      CodeAt m (pc + BitVec.ofNat 64 (16*start)) body := by
    intro i hi
    have ins := head.pre.code (start+i) (by omega)
    have eq := entries i hi
    simp only [List.getElem?_eq_getElem (by omega : start+i < code.length),
      List.getElem?_eq_getElem hi, Option.some.injEq] at eq
    rw [eq, ← pc_add] at ins
    exact ins
  have hb : FB ≤ base := by have := head.pre.ctx; unfold frei at this; omega
  have hd : 0 < (2 : Int)^distance ∧ (2 : Int)^distance < 2^62 := by
    exact ⟨Int.pow_pos (by decide), by
      exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (show distance < 62 by omega))⟩
  have preQ : Pre L m (pc+384) fp K (base+8) cq.1 ρ W reserved :=
    ⟨by have := head.pre.ctx; omega, head.pre.small, head.pre.frame,
      by simpa using part 24 cq.1 (by omega) shape.2.2.2.2.2.1,
      by simpa using codeFar_at head.pre.far (i := 24) (k := cq.1.length) (by omega),
      head.pre.env, head.pre.welt, head.pre.wstab⟩
  obtain ⟨m1, runQ, agQ, wq, rq, valQ⟩ := floatNormalizeStepL_slots q r (2^distance) target
    (by have := head.quotient; constructor <;> omega) hd
    ⟨head.remainder.1, head.remainder.2.2⟩
    (by have := head.targetBound; constructor <;> omega)
    eqQ preQ hb (by omega) (by omega) head.readQ head.readR rd head.readTarget
  subst wq
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨head.pre.ctx, head.pre.small, head.pre.frame.agree agQ,
      head.pre.code.agree agQ head.pre.far, head.pre.far,
      envAt_agree head.pre.env agQ head.pre.frame (by have := head.pre.ctx; omega) (by omega),
      head.pre.wstab m m1 head.pre.welt (agQ.mono (by omega)), head.pre.wstab⟩
  have keepQ (i : Nat) (hi : i < base+8) := agree_rd_low agQ head.pre.frame.room hi (by omega)
  have codeR := (part (24+cq.1.length) cr.1 shape.2.2.2.2.1 shape.2.2.2.2.2.2).agree agQ
    (codeFar_at head.pre.far shape.2.2.2.2.1)
  have preR : Pre L m1 (pc+BitVec.ofNat 64 (16*(24+cq.1.length))) fp K (base+9) cr.1 ρ W reserved :=
    ⟨by have := head.pre.ctx; omega, pre1.small, pre1.frame, codeR,
      codeFar_at head.pre.far shape.2.2.2.2.1, pre1.env, pre1.welt, pre1.wstab⟩
  obtain ⟨m2, runR, agR, wr, rr, valR⟩ := floatNormalizeStepL_slots q r (2^distance) target
    (by have := head.quotient; constructor <;> omega) hd
    ⟨head.remainder.1, head.remainder.2.2⟩
    (by have := head.targetBound; constructor <;> omega)
    eqR preR hb (by omega) (by omega)
    (by rw [keepQ base (by omega)]; exact head.readQ)
    (by rw [keepQ (base+1) (by omega)]; exact head.readR)
    (by rw [keepQ (base+7) (by omega)]; exact rd)
    (by rw [keepQ (base+3) (by omega)]; exact head.readTarget)
  subst wr
  have ag := agQ.trans (agR.mono (by omega))
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree agR, pre1.code.agree agR pre1.far, pre1.far,
      envAt_agree pre1.env agR pre1.frame (by have := pre1.ctx; omega) (by omega),
      pre1.wstab m1 m2 pre1.welt (agR.mono (by omega)), pre1.wstab⟩
  have keep (i : Nat) (hi : i < base+8) := agree_rd_low ag head.pre.frame.room hi (by omega)
  refine ⟨m2, ?_, ag, ?_, ?_, rr⟩
  · have qpc : pc+384+BitVec.ofNat 64 (16*cq.1.length) =
        pc+BitVec.ofNat 64 (16*(24+cq.1.length)) := by simpa using pc_add pc 24 cq.1.length
    rw [qpc] at runQ
    have endpc := pc_add pc (24+cq.1.length) cr.1.length
    rw [shape.2.2.2.1] at endpc
    rw [endpc] at runR
    exact runQ.trans runR
  · exact { head with pre := pre2
                      readQ := by rw [keep base (by omega)]; exact head.readQ
                      readR := by rw [keep (base+1) (by omega)]; exact head.readR
                      readDistance := by rw [keep (base+2) (by omega)]; exact head.readDistance
                      readTarget := by rw [keep (base+3) (by omega)]; exact head.readTarget
                      readFuel := by rw [keep (base+4) (by omega)]; exact head.readFuel
                      readCount := by rw [keep (base+5) (by omega)]; exact head.readCount }
  · rw [agree_rd_low agR pre1.frame.room (by omega : base+8 < base+9) (by omega)]
    exact rq

#print axioms floatNormalizeLoopL_small_calculation

/-- Complete the SMALL branch through arithmetic, copies and the real backedge. -/
theorem floatNormalizeLoopL_small_iteration
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r)
    (room : top ≤ K) (ceiling : budget < 2^63)
    (small : distance ≤ 61) (active : q < target) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' n (count+1) distance
        (floatNormalizeStep q r (2^distance) target).1
        (floatNormalizeStep q r (2^distance) target).2 := by
  have slots : base+9 < K := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2] at room
    omega
  obtain ⟨m0, entry, ag0, h0⟩ :=
    floatNormalizeLoopL_active_entry hc head (by omega) (by omega) active
  obtain ⟨m1, dispatch, ag1, h1, den⟩ :=
    floatNormalizeLoopL_small_dispatch hc h0 (by omega) small
  obtain ⟨m2, arithmetic, ag2, h2, rq, rr⟩ :=
    floatNormalizeLoopL_small_calculation hc h1 room small den
  obtain ⟨m3, copies, ag3, pre3, rq3, rr3, kept3⟩ :=
    floatNormalizeLoopL_small_copies hc h2.pre slots _ _ rq rr
  obtain ⟨m4, tail, ag4, pre4, rf4, rc4, kept4⟩ :=
    floatNormalizeLoopL_shared_tail hc pre3 (by omega) _ _
      (by rw [kept3 (base+4) (by omega) (by omega) (by omega)]; exact h2.readFuel)
      (by rw [kept3 (base+5) (by omega) (by omega) (by omega)]; exact h2.readCount)
  have resource := head.active_budget_bounds ceiling
  have bounds := floatNormalizeStep_bounds q r (2^distance) target head.quotient.1
    (Int.pow_pos (by decide)) ⟨head.remainder.1, head.remainder.2.2⟩
  have qb : (floatNormalizeStep q r (2^distance) target).1 < 2^61 := by
    have := head.targetBound
    unfold floatNormalizeStep floatNormalizeActive floatNormalizeCarry
    simp only [active, ↓reduceIte]
    split <;> simp_all <;> omega
  have denBound : (2 : Int)^distance < 2^63 := by
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (show distance < 63 by omega))
  refine ⟨m4, entry.trans (dispatch.trans (arithmetic.trans (copies.trans tail))),
    ag0.trans (ag1.trans ((ag2.mono (by omega)).trans (ag3.trans ag4))),
    { pre := pre4
      room := head.room
      fuelWord := resource.2.1
      countWord := resource.1
      distanceWord := head.distanceWord
      quotient := ⟨bounds.1, qb⟩
      remainder := ⟨bounds.2.1, by omega, bounds.2.2⟩
      targetBound := head.targetBound
      readQ := ?_
      readR := ?_
      readDistance := ?_
      readTarget := ?_
      readFuel := ?_
      readCount := ?_
      conservedBudget := resource.2.2
      reconstruction := ?_ }⟩
  · rw [kept4 base (by omega) (by omega) (by omega) (by omega)]; exact rq3
  · rw [kept4 (base+1) (by omega) (by omega) (by omega) (by omega)]; exact rr3
  · rw [kept4 (base+2) (by omega) (by omega) (by omega) (by omega),
      kept3 (base+2) (by omega) (by omega) (by omega)]; exact h2.readDistance
  · rw [kept4 (base+3) (by omega) (by omega) (by omega) (by omega),
      kept3 (base+3) (by omega) (by omega) (by omega)]; exact h2.readTarget
  · have eq : (BitVec.ofNat 64 (n+1) : Runner.W)-1 = BitVec.ofNat 64 n := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    simpa only [eq] using rf4
  · have eq : (BitVec.ofNat 64 count : Runner.W)+1 = BitVec.ofNat 64 (count+1) := by
      rw [BitVec.ofNat_add]
      rfl
    simpa only [eq] using rc4
  · have exactness := floatNormalizeStep_exact q r (2^distance) target
    simp only [floatNormalizeActive, active, ↓reduceIte] at exactness
    rw [exactness, show count+1+distance = (count+distance)+1 by omega, pow_succ]
    calc
      (q * 2^distance+r)*2*2^originDistance =
          ((q * 2^distance+r)*2^originDistance)*2 := by ring
      _ = _ := by rw [head.reconstruction]; ring

#print axioms floatNormalizeLoopL_small_iteration

end
end Gabbro.Stage0.Senke
