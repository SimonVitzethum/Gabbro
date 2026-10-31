/- Executed slot initialization, retaining each earlier result across temporaries. -/
import Stage0.Senke.Ausdruck.Arithmetik.Simulation
import Stage0.Senke.Ausdruck.Gleit.SlotContext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- Evaluate producers at successive state slots. Later producers may use arbitrary
    higher temporaries; their results cannot overwrite earlier state words. -/
def floatStateSlotsL (base : Nat)
    (producers : List (Nat → Option (List II × Nat))) : Option (List II × Nat) := do
  match producers with
  | [] => pure ([], base)
  | p :: ps =>
    let a ← p base
    let b ← floatStateSlotsL (base+1) ps
    pure (a.1 ++ b.1, max a.2 b.2)

variable [Kern] {D : Deklaration} {L : Lay D}

/-- This is execution, including all producer writes, rather than a premise
    asserting that the state slots already contain the desired words.
    The producer contract explicitly carries the reserved environment prefix. -/
theorem floatStateSlotsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp : Runner.W} {K reserved base top : Nat} {code : List II}
    (ps : List (Nat → Option (List II × Nat))) (values : Nat → Runner.W)
    (compiled : floatStateSlotsL base ps = some (code, top)) (room : top ≤ K)
    (slots : base + ps.length ≤ K)
    (producers : ∀ i, (hi : i < ps.length) → ∀ c t,
      ps[i] (base+i) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (base+i) c ρ W reserved →
      Ok m pc fp K (base+i) c (· = values i))
    (m : Runner.Mem) (pc : Runner.W)
    (pre : Pre L m pc fp K base code ρ W reserved) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      ∀ i, i < ps.length →
        m'.rd64 (slot fp (BitVec.ofNat 64 (base+i))) = some (values i) := by
  induction ps generalizing base top code values m pc with
  | nil =>
    simp [floatStateSlotsL] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    exact ⟨m, by simpa using Star.refl ⟨pc,fp⟩ m,
      Agree.refl _ _ _ _, by simp⟩
  | cons p ps ih =>
    simp only [floatStateSlotsL] at compiled
    cases ha : p base with
    | none => simp [ha] at compiled
    | some a =>
      cases hb : floatStateSlotsL (base+1) ps with
      | none => simp [ha, hb] at compiled
      | some b =>
        simp [ha, hb] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        obtain ⟨m1, run1, agree1, w, read1, result1⟩ :=
          producers 0 (by simp) a.1 a.2 (by simpa using ha)
            (by omega) m pc pre.left
        subst w
        have next := pre.next agree1 (Nat.le_succ base) (by simp at slots; omega)
        obtain ⟨m2, run2, agree2, reads⟩ := ih (fun i => values (i+1)) hb
          (by omega) (by simp at slots; omega) (by
            intro i hi c t hc ht m pc hp
            have h := producers (i+1) (by simp; omega) c t
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              h (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
                ht m pc (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp)) m1 _ next
        refine ⟨m2, ?_, agree1.trans (agree2.mono (Nat.le_succ base)), ?_⟩
        · have endPc : pc + BitVec.ofNat 64 (16*(a.1 ++ b.1).length) =
              pc + BitVec.ofNat 64 (16*a.1.length) + BitVec.ofNat 64 (16*b.1.length) := by
            rw [List.length_append, pc_add]
          rw [endPc]
          exact run1.trans run2
        · intro i hi
          cases i with
          | zero =>
            simpa using slotRead_agree next.frame agree2 (Nat.lt_succ_self base)
              (by simp at slots; omega) (by simpa using read1)
          | succ i =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              reads i (by simpa using hi)

/-- Two distinct writes execute jointly without assuming either initial slot. -/
theorem floatStateSlotsL_ok_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {base K reserved : Nat} (room : base+2 ≤ K)
    (pre : Pre L m pc fp K base
      [ci 1 base 7 0, ci 1 (base+1) 11 0] ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 32,fp⟩ m' ∧
      Agree fp base K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some 7 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some 11 := by
  let ps : List (Nat → Option (List II × Nat)) :=
    [fun d => some ([ci 1 d 7 0], d+1),
     fun d => some ([ci 1 d 11 0], d+1)]
  have compiled : floatStateSlotsL base ps =
      some ([ci 1 base 7 0, ci 1 (base+1) 11 0], base+2) := by
    simp [floatStateSlotsL, ps]
  obtain ⟨m', run, agree, reads⟩ := floatStateSlotsL_ok ps
    (fun i => if i = 0 then 7 else 11) compiled room (by simpa [ps] using room)
    (by
      intro i hi c t hc ht m pc hp
      have bound : i < 2 := by simpa [ps] using hi
      interval_cases i <;> simp [ps] at hc <;>
        obtain ⟨rfl,rfl⟩ := hc
      · exact const_ok hp (by decide) (by omega)
      · exact const_ok hp (by decide) (by omega)) m pc pre
  exact ⟨m', run, agree, by simpa using reads 0 (by simp [ps]),
    by simpa using reads 1 (by simp [ps])⟩

/-- Concrete exact-alignment entry: decode both IEEE operands, align their
    signed coefficients and take the cancellation-aware magnitude. The other
    five words are emitted writes, rather than assumed initial memory. -/
def floatExactAddInitProducers (lo hi distance : Nat → Option (List II × Nat)) :
    List (Nat → Option (List II × Nat)) :=
  [fun dst => floatSumMagnitudeL dst
      (fun j => floatAlignSumL j (fun n => floatCoefficientL n lo)
        (fun n => floatCoefficientL n hi) distance)
      (fun j => some ([ci 1 j 0 0], j+1)),
   fun j => some ([ci 1 j 0 0], j+1),
   fun j => some ([ci 1 j 0 0], j+1),
   fun j => some (konstWL 4 (2^(Gleitkomma.f64.p - 1 + 3)) j),
   fun j => some ([ci 1 j (Gleitkomma.f64.p - 1 + 3) 0], j+1),
   fun j => some ([ci 1 j 0 0], j+1)]

/-- Source-word producers are instantiated through the actual decoder and
    alignment code. The normalization target includes the three bits consumed by field division.
    No hypothesis supplies any of the six initial reads.
    This exact-alignment entry is only the word-sized f64 branch. -/
theorem floatExactAddInit_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)}
    (a b : GFloat) (k : Nat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (hk : k < 64)
    (hr : -2^63 ≤ floatCoefficient a + floatCoefficient b * (2^k : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^k : Nat) < 2^63)
    (hlo : WordCode (L := L) ρ W lo (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)))
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofNat 64 (Gleitkomma.zuBits _ b)))
    (hd : WordCode (L := L) ρ W distance (BitVec.ofNat 64 k))
    {base top K : Nat} {code : List II} {m : Runner.Mem} {pc fp : Runner.W}
    (compiled : floatStateSlotsL base (floatExactAddInitProducers lo hi distance) =
      some (code,top)) (room : top ≤ K) (slots : base+6 ≤ K)
    (pre : Pre L m pc fp K base code ρ W) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) =
        some (BitVec.ofInt 64 (floatSumMagnitude
          (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some 0 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some 0 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofNat 64 (2^55)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some 55 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some 0 := by
  let q := BitVec.ofInt 64 (floatSumMagnitude
    (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)
  let values : Nat → Runner.W := fun i =>
    if i = 0 then q else if i = 3 then BitVec.ofNat 64 (2^55)
    else if i = 4 then 55 else 0
  obtain ⟨m', run, agree, reads⟩ := floatStateSlotsL_ok
    (floatExactAddInitProducers lo hi distance) values compiled room
    (by simpa [floatExactAddInitProducers] using slots) (by
      intro i hi' c t hc ht m pc hp
      have bound : i < 6 := by simpa [floatExactAddInitProducers] using hi'
      interval_cases i
      · exact floatCoefficientAlignMagnitudeL_ok a b k ha hb hk hr hlo hhi hd hc ht m pc hp
      · simp [floatExactAddInitProducers] at hc
        obtain ⟨rfl,rfl⟩ := hc
        exact const_ok hp (by decide) (by omega)
      · simp [floatExactAddInitProducers] at hc
        obtain ⟨rfl,rfl⟩ := hc
        exact const_ok hp (by decide) (by omega)
      · exact WordCode.konst (2^55) (by decide) hc ht m pc hp
      · simp [floatExactAddInitProducers] at hc
        obtain ⟨rfl,rfl⟩ := hc
        exact const_ok hp (by decide) (by omega)
      · simp [floatExactAddInitProducers] at hc
        obtain ⟨rfl,rfl⟩ := hc
        exact const_ok hp (by decide) (by omega)) m pc pre
  exact ⟨m', run, agree, by simpa [values, q] using reads 0 (by simp [floatExactAddInitProducers]),
    by simpa [values] using reads 1 (by simp [floatExactAddInitProducers]),
    by simpa [values] using reads 2 (by simp [floatExactAddInitProducers]),
    by simpa [values] using reads 3 (by simp [floatExactAddInitProducers]),
    by simpa [values] using reads 4 (by simp [floatExactAddInitProducers]),
    by simpa [values] using reads 5 (by simp [floatExactAddInitProducers])⟩

/-- Executed operand initialization establishes the actual loop head, including
    its fetch/frame precondition and the format's sufficient guard-precision transfer budget.
    The signed 61-bit bound identifies this exact-alignment branch explicitly. -/
theorem floatExactAddInit_head {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)}
    (a b : GFloat) (k : Nat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (hk : k < 64)
    (hr : -2^61 < floatCoefficient a + floatCoefficient b * (2^k : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^k : Nat) < 2^61)
    (hlo : WordCode (L := L) ρ W lo (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)))
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofNat 64 (Gleitkomma.zuBits _ b)))
    (hd : WordCode (L := L) ρ W distance (BitVec.ofNat 64 k))
    {base top K : Nat} {code loop : List II} {m : Runner.Mem} {pc fp : Runner.W}
    (compiled : floatStateSlotsL base (floatExactAddInitProducers lo hi distance) =
      some (code,top)) (room : top ≤ K) (slots : base+6 ≤ K)
    (pre : Pre L m pc fp K base (code ++ loop) ρ W) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W (pc + BitVec.ofNat 64 (16*code.length)) fp
        K base 0 loop
        (floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)
        0 55 (2^55) m' 55 0 0
        (floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0) 0 := by
  obtain ⟨m', run, agree, rq, rr, rd, rt, rf, rc⟩ :=
    floatExactAddInit_ok a b k ha hb hk (by constructor <;> omega)
      hlo hhi hd compiled room slots pre.left
  have next := pre.next agree (Nat.le_refl base) (by omega)
  have magnitude : 0 ≤ floatSumMagnitude
      (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0 ∧
      floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0 < 2^61 := by
    unfold floatSumMagnitude
    split <;> omega
  refine ⟨m', run, agree, ?_⟩
  simpa only [pow_zero, Int.ediv_one, Int.emod_one] using FloatNormalizeHead.of_numerator (target := (2^55 : Int))
    (floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)
    0 55 magnitude (by decide) (by decide) (by norm_num) next (by omega)
    (by simpa using rq) (by simpa using rr) rd (by norm_num at rt ⊢; exact rt) rf rc

/-- The actual decoded-operand prefix and the entire emitted normalization
    loop compose. Zero/cancellation is included; 55 transfers suffice on this
    zero-distance branch. No loop-head memory is assumed by the caller. -/
theorem floatExactAddNormalize_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)}
    (a b : GFloat) (k : Nat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (hk : k < 64)
    (hr : -2^61 < floatCoefficient a + floatCoefficient b * (2^k : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^k : Nat) < 2^61)
    (hlo : WordCode (L := L) ρ W lo (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)))
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofNat 64 (Gleitkomma.zuBits _ b)))
    (hd : WordCode (L := L) ρ W distance (BitVec.ofNat 64 k))
    {base top K : Nat} {code loop : List II} {loopTop : Nat} {m : Runner.Mem} {pc fp : Runner.W}
    (compiled : floatStateSlotsL base (floatExactAddInitProducers lo hi distance) =
      some (code,top)) (room : top ≤ K) (slots : base+6 ≤ K)
    (loopCompiled : floatNormalizeLoopL base = some (loop,loopTop))
    (loopRoom : loopTop ≤ K)
    (pre : Pre L m pc fp K base (code ++ loop) ρ W) :
    ∃ m' fuel count distance' q r,
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*(code ++ loop).length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W (pc + BitVec.ofNat 64 (16*code.length)) fp
        K base 0 loop
        (floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)
        0 55 (2^55) m' fuel count distance' q r ∧
      ((floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0 = 0 ∧
        q = 0 ∧ r = 0) ∨
       (0 < floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0 ∧
        (2^55 : Int) ≤ q)) ∧ count ≤ 55 ∧
      ∀ p : Nat,
        let nd := Gleitkomma.normQD p ((p : Int)-1-count)
          ((floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0).toNat *
            2^distance') (8 * 2^distance')
        nd.1 / nd.2 = (q/8).toNat ∧
        nd.1 % nd.2 = (q%8).toNat * 2^distance' + r.toNat ∧
        nd.2 = 8 * 2^distance' := by
  obtain ⟨m1, initRun, initAgree, head⟩ := floatExactAddInit_head a b k ha hb hk hr
    hlo hhi hd compiled room slots pre
  have nonnegative := head.quotient.1
  obtain ⟨m2, f, c, d, q, r, run, agree, finalHead, result, bound, _, _⟩ :=
    floatNormalizeLoopL_finite_magnitude loopCompiled loopRoom head nonnegative
      55 (by rfl) (by omega)
  refine ⟨m2, f, c, d, q, r, ?_, initAgree.trans agree, finalHead, result, bound, ?_⟩
  · rw [List.length_append, ← pc_add]
    exact initRun.trans run
  · intro p
    simpa using finalHead.normQD_output p

#print axioms floatExactAddNormalize_ok

#print axioms floatExactAddInit_head

#print axioms floatExactAddInit_ok
#print axioms floatStateSlotsL_ok_zeuge
#print axioms floatStateSlotsL_ok

/-- Execute the quotient output from the actual normalization slot. The
    source load is derived from memory; no movable fixed-slot producer or
    assumed output word is used. The original head and continuation may have
    different code addresses. The shared reserved prefix is arbitrary. -/
theorem FloatNormalizeHead.write_quotient
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp next : Runner.W}
    {K base reserved dst top : Nat} {code out : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (input : FB ≤ base) (retained : base < dst)
    (compiled : wordK 6 dst (some ([ci 2 dst base 0], dst+1)) 8 = some (out,top))
    (room : top ≤ K) (dstRoom : dst ≤ K)
    (pre : Pre L m next fp K dst out ρ W reserved) :
    Ok m next fp K dst out (· = BitVec.ofInt 64 (q / 8)) := by
  obtain ⟨env, envAt⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  have idx : base-FB < dst-FB := by omega
  have slotEq : FB + (base-FB) = base := by omega
  obtain ⟨w, hr, he⟩ := envAt _ (frameWordVar (dst-FB) (base-FB) idx)
  rw [frameWordVar_slot, slotEq, head.readQ] at hr
  cases hr
  change BitVec.ofInt 64 q =
    BitVec.ofInt 64 (env.get (frameWordVar (dst-FB) (base-FB) idx)).n at he
  have load : WordCode (L := L) env (fun _ => True)
      (fun j => some ([ci 2 j base 0], j+1)) (BitVec.ofInt 64 q) := by
    rw [he]
    have slotEqInt : (FB : Int) + ((base-FB : Nat) : Int) = base := by omega
    intro fp' K' j c t hc ht mm pp hp
    exact frameWordLoad (L := L) (dst-FB) (base-FB) idx env
      (by simpa only [slotEqInt] using hc) ht mm pp hp
  have div := sdiv_w (a := q) (b := 8)
    (by have := head.quotient; omega) (by have := head.quotient; omega)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg head.quotient.1] at div
  have result : WordCode (L := L) env (fun _ => True)
      (fun j => wordL 6 j (some ([ci 2 j base 0], j+1))
        (some ([ci 1 (j+1) 8 0], j+2)))
      (BitVec.ofInt 64 (q / 8)) := WordCode.bin load (WordCode.const 8 (by decide)) div
    (rfl : op 6 = bin sdiv) (by decide : 6 < 256)
  have pre' : Pre L m next fp K dst out env (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame, pre.code,
      pre.far, envAt, trivial, wstab_true _ _⟩
  exact result (by simpa [wordK] using compiled) room m next pre'

#print axioms FloatNormalizeHead.write_quotient

/-- The reached invariant supplies the rounding bounds, including the exact
    residual scale. No output-range premise is added to field execution. -/
theorem FloatNormalizeHead.output_ranges
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) :
    0 ≤ q/8 ∧ q/8 < 2^58 ∧ 0 ≤ q%8 ∧ q%8 < 8 ∧
      0 ≤ r * 2^originDistance ∧
      r * 2^originDistance < (2 : Int)^(distance+originDistance) := by
  have quotient := head.quotient
  have guardLow := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
  have guardHigh := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
  have positive : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  refine ⟨by omega, by omega, guardLow, guardHigh,
    mul_nonneg head.remainder.1 (le_of_lt positive), ?_⟩
  rw [pow_add]
  exact mul_lt_mul_of_pos_right head.remainder.2.2 positive

#print axioms FloatNormalizeHead.output_ranges

/-- Materialize all five output fields together. The signed sum and the initial
    biased exponent remain in retained input slots; normalization supplies the
    magnitude, exact tail, and completed transfer count. -/
def floatNormalizedFieldsL (base signedSum exponent signBit : Nat) :
    List (Nat → Option (List II × Nat)) :=
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  [fun j => wordL 5 j (wordK 13 j (load signedSum j) 0)
      (some (konstWL 4 (2^signBit) (j+1))),
   fun j => wordL 4 j (load exponent j) (load (base+5) (j+1)),
   fun j => wordK 6 j (load base j) 8,
   fun j => wordK 8 j (load base j) 7,
   fun j => wordL 4 j (some ([ci 1 j 1 0], j+1))
      (wordK 14 (j+1) (load (base+1) (j+1)) 0)]

set_option maxHeartbeats 2000000 in
/-- Execute the complete field materialization against actual retained memory.
    This proves the machine field expressions jointly, including preservation
    of every earlier output and the arbitrary reserved prefix. Identification
    of sign and exponent with the canonical IEEE result is a separate boundary. -/
theorem FloatNormalizeHead.write_fields
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp next : Runner.W}
    {K base reserved dst top signedSum exponent signBit : Nat} {code out : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (input : FB ≤ base) (sumInput : FB ≤ signedSum) (exInput : FB ≤ exponent)
    (retained : base+6 ≤ dst) (sumRetained : signedSum < dst)
    (exRetained : exponent < dst) (bitBound : signBit < 64)
    (sumWord exponentWord : Runner.W)
    (readSum : m.rd64 (slot fp (BitVec.ofNat 64 signedSum)) = some sumWord)
    (readExponent : m.rd64 (slot fp (BitVec.ofNat 64 exponent)) = some exponentWord)
    (compiled : floatStateSlotsL dst
      (floatNormalizedFieldsL base signedSum exponent signBit) = some (out,top))
    (room : top ≤ K) (slots : dst+5 ≤ K)
    (pre : Pre L m next fp K dst out ρ W reserved) :
    ∃ m', Star ⟨next,fp⟩ m ⟨next + BitVec.ofNat 64 (16*out.length),fp⟩ m' ∧
      Agree fp dst K m m' ∧
      ∀ i, (hi : i < 5) →
        m'.rd64 (slot fp (BitVec.ofNat 64 (dst+i))) = some
          (([Runner.IR.bool (sumWord.slt 0) * BitVec.ofNat 64 (2^signBit),
            exponentWord - BitVec.ofNat 64 count, BitVec.ofInt 64 (q/8),
            BitVec.ofInt 64 q &&& 7,
            1 - Runner.IR.bool (BitVec.ofInt 64 r == 0)] : List Runner.W)[i]'(by simpa using hi)) := by
  obtain ⟨env, envAt⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  have loads : ∀ s v, FB ≤ s → s < dst →
      m.rd64 (slot fp (BitVec.ofNat 64 s)) = some v →
      WordCode (L := L) env (fun _ => True)
        (fun j => some ([ci 2 j s 0],j+1)) v := by
    intro s v low high read
    have idx : s-FB < dst-FB := by omega
    have slotEq : FB+(s-FB) = s := by omega
    obtain ⟨w, hr, he⟩ := envAt _ (frameWordVar (dst-FB) (s-FB) idx)
    rw [frameWordVar_slot, slotEq, read] at hr
    cases hr
    change v = BitVec.ofInt 64 (env.get (frameWordVar (dst-FB) (s-FB) idx)).n at he
    rw [he]
    have slotInt : (FB : Int) + ((s-FB : Nat) : Int) = s := by omega
    intro fp' K' j c t hc ht mm pp hp
    exact frameWordLoad (L := L) (dst-FB) (s-FB) idx env
      (by simpa only [slotInt] using hc) ht mm pp hp
  have lq : WordCode (L := L) env (fun _ => True) _ _ := loads base _ input (by omega) head.readQ
  have lr : WordCode (L := L) env (fun _ => True) _ _ := loads (base+1) _ (by omega) (by omega) head.readR
  have lc : WordCode (L := L) env (fun _ => True) _ _ := loads (base+5) _ (by omega) (by omega) head.readCount
  have ls : WordCode (L := L) env (fun _ => True) _ _ := loads signedSum _ sumInput sumRetained readSum
  have le : WordCode (L := L) env (fun _ => True) _ _ := loads exponent _ exInput exRetained readExponent
  have zero : WordCode (L := L) env (fun _ => True) _ _ := WordCode.const (L := L) (ρ := env) (W := fun _ => True) 0 (by decide)
  have sign : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin ls zero
    (g := fun a b => some (Runner.IR.bool (a.slt b)))
    rfl rfl (by decide : 13 < 256)
  have signField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin sign
    (WordCode.konst (2^signBit) (by exact Nat.pow_lt_pow_right (by decide) bitBound))
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have exponentField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin le lc
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have div := sdiv_w (a := q) (b := 8)
    (by have := head.quotient; omega) (by have := head.quotient; omega)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg head.quotient.1] at div
  have quotientField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lq (WordCode.const 8 (by decide)) div
    (rfl : op 6 = bin sdiv) (by decide : 6 < 256)
  have guardField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lq (WordCode.const 7 (by decide))
    (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
  have same : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lr zero
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have stickyField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin (WordCode.const 1 (by decide)) same
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have pre' : Pre L m next fp K dst out env (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame, pre.code,
      pre.far, envAt, trivial, wstab_true _ _⟩
  let values : Nat → Runner.W := fun i =>
    if i = 0 then Runner.IR.bool (sumWord.slt 0) * BitVec.ofNat 64 (2^signBit)
    else if i = 1 then exponentWord - BitVec.ofNat 64 count
    else if i = 2 then BitVec.ofInt 64 (q/8)
    else if i = 3 then BitVec.ofInt 64 q &&& 7
    else 1 - Runner.IR.bool (BitVec.ofInt 64 r == 0)
  obtain ⟨m', run, agree, reads⟩ := floatStateSlotsL_ok (L := L) (ρ := env) (W := fun _ => True)
    (base := dst) (top := top) (code := out) (K := K) (reserved := 0) (fp := fp)
    (floatNormalizedFieldsL base signedSum exponent signBit) values compiled room (by simpa [floatNormalizedFieldsL] using slots)
    (by
      intro i hi c t hc ht mm pp hp
      have bound : i < 5 := by simpa [floatNormalizedFieldsL] using hi
      interval_cases i <;> dsimp only [values] <;>
        dsimp only [floatNormalizedFieldsL, List.getElem_cons_zero, List.getElem_cons_succ] at hc
      · exact signField hc ht mm pp hp
      · exact exponentField hc ht mm pp hp
      · exact quotientField hc ht mm pp hp
      · exact guardField hc ht mm pp hp
      · exact stickyField hc ht mm pp hp)
    m next pre'
  refine ⟨m', run, agree, ?_⟩
  intro i hi
  interval_cases i
  · simpa [values] using reads 0 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 1 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 2 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 3 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 4 (by simp [floatNormalizedFieldsL])

#print axioms FloatNormalizeHead.write_fields

/-- Carry a source dyadic denominator through the canonical normalizer.
    `scale + 3` is the source denominator exponent; three bits are consumed
    by the emitted guard split. The output exponent changes with that scale,
    while quotient and exact remainder follow from the executed loop head. -/
theorem FloatNormalizeHead.normQD_source_output
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    let nd := Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))
    nd.1 / nd.2 = (q/8).toNat ∧
    nd.1 % nd.2 = ((q%8).toNat * 2^(distance+originDistance) +
      r.toNat * 2^originDistance) * 2^scale ∧
    nd.2 = (8 * 2^(distance+originDistance)) * 2^scale := by
  have shift : (p : Int)-1-((p : Int)-1-count-scale) = (count+scale : Nat) := by
    push_cast; omega
  have pair := head.normQD_output p
  simp only [Gleitkomma.normQD, show (p : Int)-1-((p : Int)-1-count) = count by omega,
    shift, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast] at pair ⊢
  rw [pow_add (2:Nat) count scale, pow_add (2:Nat) (distance+originDistance) scale]
  simp only [← Nat.mul_assoc]
  rw [Nat.mul_div_mul_right _ _ (by positivity : 0 < (2:Nat)^scale),
    Nat.mul_mod_mul_right]
  exact ⟨pair.1, congrArg (· * 2^scale) pair.2.1, True.intro⟩

#print axioms FloatNormalizeHead.normQD_source_output

/-- A target derived from format precision supplies the hidden bit after
    the actual three-bit quotient split, for every precision. -/
theorem floatGuardTarget_hiddenBit (p : Nat) (q : Int)
    (reached : (2 : Int)^(p-1+3) ≤ q) :
    (2 : Int)^(p-1) ≤ q/8 := by
  have power : (2 : Int)^(p-1+3) = 8 * 2^(p-1) := by
    rw [pow_add]; ring
  rw [power] at reached
  omega

theorem floatGuardTarget_hiddenBit_zeuge :
    (2 : Int)^52 ≤ (2^55 : Int)/8 ∧
    (2 : Int)^23 ≤ (2^26 : Int)/8 := by
  exact ⟨floatGuardTarget_hiddenBit 53 (2^55) (by decide),
    floatGuardTarget_hiddenBit 24 (2^26) (by decide)⟩

#print axioms floatGuardTarget_hiddenBit
#print axioms floatGuardTarget_hiddenBit_zeuge

/-- Every reached head supplies bounded canonical output fields, for any
    precision and source scale. No output-field bounds are caller premises.
    This word bound does not assert the tighter format normalization bound. -/
theorem FloatNormalizeHead.normQD_source_bounds
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    let nd := Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))
    0 < nd.2 ∧ nd.1 / nd.2 < 2^58 ∧ nd.1 % nd.2 < nd.2 ∧
      (q%8).toNat < 8 := by
  dsimp only
  have fields := head.normQD_source_output p scale
  have positive : 0 < (8 * 2^(distance+originDistance) : Nat) * 2^scale := by
    positivity
  have denominator := fields.2.2
  have denPositive : 0 < (Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))).2 := by
    rw [denominator]
    exact positive
  refine ⟨denPositive, ?_, Nat.mod_lt _ denPositive, ?_⟩
  · rw [fields.1]
    have := head.quotient
    have : q / 8 < (2^58 : Int) := by omega
    omega
  · have lo := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
    have hi := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
    omega

#print axioms FloatNormalizeHead.normQD_source_bounds

/-- Canonical rounding of the source-scaled rational is exactly the emitted
    guard/sticky decision for every reached head. This includes both tie
    parities and arbitrarily large denominator distances, uniformly in p. -/
theorem FloatNormalizeHead.normQ_source_guard
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    Gleitkomma.normQ p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale)) =
      Gleitkomma.rundeInt (q/8).toNat
        (2 * (q%8).toNat + if r = 0 then 0 else 1) 16 := by
  have fields := head.normQD_source_output p scale
  have ranges := head.output_ranges
  let den : Nat := 2^(distance+originDistance) * 2^scale
  let rest : Nat := r.toNat * 2^originDistance * 2^scale
  have hd : 0 < den := by dsimp [den]; positivity
  have tail : r.toNat * 2^originDistance < (2 : Nat)^(distance+originDistance) := by
    apply Int.ofNat_lt.mp
    push_cast
    rw [Int.toNat_of_nonneg head.remainder.1]
    exact ranges.2.2.2.2.2
  have hr : rest < den := Nat.mul_lt_mul_of_pos_right tail (by positivity)
  have hg : (q%8).toNat < 8 := by
    have := ranges.2.2.1
    have := ranges.2.2.2.1
    omega
  have hz : rest = 0 ↔ r = 0 := by
    simp only [rest, Nat.mul_eq_zero, pow_ne_zero _ (by decide : (2 : Nat) ≠ 0),
      or_false]
    have := head.remainder.1
    omega
  unfold Gleitkomma.normQ
  rw [fields.1, fields.2.1, fields.2.2]
  have remEq : ((q%8).toNat * 2^(distance+originDistance) +
      r.toNat * 2^originDistance) * 2^scale = (q%8).toNat * den + rest := by
    dsimp [den, rest]; ring
  have denEq : (8 * 2^(distance+originDistance)) * 2^scale = 8 * den := by
    dsimp [den]; ring
  rw [remEq, denEq, floatGuardSticky_round _ _ _ _ hd hr hg]
  simp only [hz]

#print axioms FloatNormalizeHead.normQ_source_guard

/-- The emitted rounding fragment implements the canonical source-scaled
    normQ for every reached head. Field producers still carry their ordinary
    execution contracts; format-specific packing and operand entry are separate. -/
theorem FloatNormalizeHead.round_source_ok
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat)
    {quotient guard sticky : Nat → Option (List II × Nat)}
    (hq : WordCode (L := L) ρ W quotient (BitVec.ofNat 64 (q/8).toNat))
    (hg : WordCode (L := L) ρ W guard (BitVec.ofNat 64 (q%8).toNat))
    (hs : WordCode (L := L) ρ W sticky
      (BitVec.ofNat 64 (if r = 0 then 0 else 1))) :
    WordCode (L := L) ρ W (fun j => floatGuardRoundL j quotient guard sticky)
      (BitVec.ofNat 64 (Gleitkomma.normQ p ((p : Int)-1-count-scale)
        (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale)))) := by
  have hd : 0 < (2 : Nat)^distance := by positivity
  have hr : r.toNat < (2 : Nat)^distance := by
    have := head.remainder
    apply Int.ofNat_lt.mp
    push_cast
    rw [Int.toNat_of_nonneg this.1]
    exact this.2.2
  have hgBound : (q%8).toNat < 8 := by
    have lo := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
    have hi := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
    omega
  have hz : r.toNat = 0 ↔ r = 0 := by
    have := head.remainder.1
    omega
  have hs' : WordCode (L := L) ρ W sticky
      (BitVec.ofNat 64 (if r.toNat = 0 then 0 else 1)) := by
    intro fp' K' j c t hc ht mm pp hp
    simpa only [hz] using hs hc ht mm pp hp
  have rounded : WordCode (L := L) ρ W
      (fun j => floatGuardRoundL j quotient guard sticky)
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat
        ((q%8).toNat * 2^distance + r.toNat) (8 * 2^distance))) := by
    intro fp' K' j c t hc ht mm pp hp
    exact floatGuardRoundL_ok (q/8).toNat (q%8).toNat r.toNat
      (2^distance) hd hr hgBound hq hg hs' hc ht mm pp hp
  rw [floatGuardSticky_round _ _ _ _ hd hr hgBound] at rounded
  simp only [hz] at rounded
  rw [head.normQ_source_guard p scale]
  intro fp' K' j c t hc ht mm pp hp
  exact rounded hc ht mm pp hp

#print axioms FloatNormalizeHead.round_source_ok

omit [Kern] in
/-- Bounds for the actual finite candidate's decoded input words. They follow
    from the packed source operand, including either zero sign and subnormals;
    neither an exponent slot nor a magnitude slot is assumed correct. The
    three guard bits leave room for signed comparisons and a sum of two inputs. -/
theorem floatFiniteAdd_input_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a : Gleitkomma.GBits F) (valid : Gleitkomma.wf F a)
    (finite : a.bexp ≠ F.bexpMax) :
    let w := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
    let e := (floatFieldWord w F.fracBits F.ebits).toNat
    let m := (floatFieldWord w 0 F.fracBits).toNat +
      (if e = 0 then 0 else 2^F.fracBits)
    1 ≤ max e 1 ∧ max e 1 < F.bexpMax ∧
      8*m < 2^(F.fracBits+4) ∧ 8*m < 2^56 := by
  obtain ⟨fraction, exponent⟩ := floatFieldWord_canonical F dense width a valid
  dsimp only
  rw [fraction, exponent]
  have hb := valid.1
  have hf := valid.2
  have hp : 0 < (2^F.fracBits : Nat) := Nat.pow_pos (by decide)
  have magnitude : a.frac + (if a.bexp = 0 then 0 else 2^F.fracBits) <
      2 * 2^F.fracBits := by
    split <;> omega
  have scale : (2 : Nat)^(F.fracBits+4) = 16 * 2^F.fracBits := by
    rw [Nat.pow_add]; omega
  have cap : (2 : Nat)^(F.fracBits+4) ≤ 2^56 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨Nat.le_max_right _ _, ?_, ?_, ?_⟩
  · omega
  · rw [scale]; omega
  · rw [scale] at cap; omega

omit [Kern] in
/-- Canonical finite operands bound the ordered alignment distance and both
    guard-extended significands. The distance bound includes subnormals and
    either operand order; it is not a premise about a manually filled slot. -/
theorem floatFiniteAdd_ordered_input_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let wa := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
    let wb := BitVec.ofNat 64 (Gleitkomma.zuBits F b)
    let ea := max (floatFieldWord wa F.fracBits F.ebits).toNat 1
    let eb := max (floatFieldWord wb F.fracBits F.ebits).toNat 1
    let ma := 8*((floatFieldWord wa 0 F.fracBits).toNat +
      if (floatFieldWord wa F.fracBits F.ebits).toNat = 0 then 0 else 2^F.fracBits)
    let mb := 8*((floatFieldWord wb 0 F.fracBits).toNat +
      if (floatFieldWord wb F.fracBits F.ebits).toNat = 0 then 0 else 2^F.fracBits)
    max ea eb - min ea eb ≤ F.bexpMax-2 ∧
      ma + mb < 2^57 ∧ ma < 2^56 ∧ mb < 2^56 := by
  have ba := floatFiniteAdd_input_bounds F dense width precision exponents a ha fa
  have bb := floatFiniteAdd_input_bounds F dense width precision exponents b hb fb
  dsimp only at ba bb ⊢
  have hi : max
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits).toNat 1)
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) F.fracBits F.ebits).toNat 1)
      < F.bexpMax := max_lt ba.2.1 bb.2.1
  have lo : 1 ≤ min
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits).toNat 1)
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) F.fracBits F.ebits).toNat 1) :=
    le_min ba.1 bb.1
  omega

omit [Kern] in
/-- Joint finite fixtures attain the maximum distance in both formats: a
    negative minimum subnormal and a positive maximum finite operand. -/
theorem floatFiniteAdd_ordered_input_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨true,0,1⟩
      let b : Gleitkomma.GBits F := ⟨false,F.bexpMax-1,2^F.fracBits-1⟩
      let wa := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
      let wb := BitVec.ofNat 64 (Gleitkomma.zuBits F b)
      let ea := max (floatFieldWord wa F.fracBits F.ebits).toNat 1
      let eb := max (floatFieldWord wb F.fracBits F.ebits).toNat 1
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      max ea eb - min ea eb = F.bexpMax-2 := by
  intro F member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

#print axioms floatFiniteAdd_ordered_input_bounds_zeuge

#print axioms floatFiniteAdd_ordered_input_bounds

omit [Kern] in
/-- Both supported formats satisfy all generic decoding premises jointly.
    The operand fixture crosses the hidden-bit boundary without a normal
    exponent and retains a negative sign in its packed representation. -/
theorem floatFiniteAdd_input_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨true, 0, 1⟩
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
      let e := (floatFieldWord w F.fracBits F.ebits).toNat
      let m := (floatFieldWord w 0 F.fracBits).toNat +
        (if e = 0 then 0 else 2^F.fracBits)
      1 ≤ max e 1 ∧ max e 1 < F.bexpMax ∧
        8*m < 2^(F.fracBits+4) ∧ 8*m < 2^56 := by
  intro F member
  apply floatFiniteAdd_input_bounds
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals first | exact Gleitkomma.f32_dicht | exact Gleitkomma.f64_dicht | decide +kernel

#print axioms floatFiniteAdd_input_bounds
#print axioms floatFiniteAdd_input_bounds_zeuge

/-- Shared finite add candidate. Operands are decoded at runtime; alignment
    retains guard/round/sticky bits before signed cancellation. No validator
    hook is enabled until the complete source-to-bytes theorem is available. -/
def floatFiniteAddL (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) := do
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let branch := fun (c : Nat) (yes no : List II) =>
    [ci 19 c (16*(yes.length+2)) 0] ++ yes ++
      [ci 18 (16*(no.length+1)) 0 0] ++ no
  let x := dst+1; let y := dst+2
  let sx := dst+3; let sy := dst+4
  let ex := dst+5; let ey := dst+6
  let q := dst+7; let r := dst+8
  let t := dst+9; let u := dst+10; let v := dst+11
  let field := fun start width j p => floatFieldL start width j p
  let exponent := fun p j => wordL 3 j (field F.fracBits F.ebits j p)
    (wordK 14 (j+1) (field F.fracBits F.ebits (j+1) p) 0)
  let magnitude := fun p j => wordK 5 j
    (wordL 3 j (field 0 F.fracBits j p)
      (wordL 5 (j+1)
        (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
          (wordK 14 (j+2) (field F.fracBits F.ebits (j+2) p) 0))
        (some (konstWL 4 (2^F.fracBits) (j+2))))) 8
  let inputs ← floatStateSlotsL x [a,b,
    fun j => field (F.fracBits+F.ebits) 1 j (load x),
    fun j => field (F.fracBits+F.ebits) 1 j (load y),
    exponent (load x), exponent (load y), magnitude (load x), magnitude (load y)]
  let swap := [ci 2 t sx 0, ci 2 sx sy 0, ci 2 sy t 0,
    ci 2 t ex 0, ci 2 ex ey 0, ci 2 ey t 0,
    ci 2 t q 0, ci 2 q r 0, ci 2 r t 0]
  let sort := [ci 13 t ex ey, ci 14 u ex ey, ci 13 v q r,
    ci 5 u u v, ci 9 t t u] ++ branch t swap []
  let aligned ← floatShiftJamL (dst+16) (load r)
    (fun j => wordL 4 j (load ex j) (load ey (j+1)))
  let signed := [ci 2 r (dst+16) 0, ci 14 t sx sy] ++
    branch t [ci 3 q q r] [ci 4 q q r]
  let shift ← floatShiftJamL (dst+16) (load q)
    (fun j => some ([ci 1 j 1 0],j+1))
  let right := (konstWL 4 (2^(F.fracBits+4)) u).1 ++
    [ci 13 t q u, ci 1 u 1 0, ci 4 t u t] ++
    branch t (shift.1 ++ [ci 2 q (dst+16) 0, ci 3 ex ex u]) []
  let condition := (konstWL 4 (2^(F.fracBits+3)) u).1 ++
    [ci 13 t q u, ci 1 u 1 0, ci 13 v u ex, ci 5 t t v,
     ci 1 u 0 0, ci 14 v q u, ci 1 u 1 0, ci 4 v u v, ci 5 t t v]
  let body := [ci 1 u 2 0, ci 5 q q u, ci 1 u 1 0, ci 4 ex ex u]
  let left := condition ++ [ci 19 t (16*(body.length+2)) 0] ++ body ++
    [ci 18 (-(16*(condition.length+body.length+1) : Int)) 0 0]
  let rounded ← floatGuardRoundL (dst+16)
    (fun j => wordK 6 j (load q j) 8)
    (fun j => wordK 8 j (load q j) 7)
    (fun j => some ([ci 1 j 0 0],j+1))
  let carry := (konstWL 4 (2^(F.fracBits+1)) u).1 ++ [ci 14 t q u] ++
    branch t [ci 1 u 1 0, ci 12 q q u, ci 3 ex ex u] []
  let pack := (konstWL 4 (2^F.fracBits) u).1 ++ [ci 13 t q u] ++
    branch t [ci 1 ex 0 0] [ci 4 q q u] ++
    (konstWL 4 F.bexpMax u).1 ++ [ci 13 t ex u] ++
    branch t [] [ci 2 ex u 0, ci 1 q 0 0] ++
    (konstWL 4 (2^F.fracBits) u).1 ++ [ci 5 ex ex u, ci 3 q q ex]
  let sign := (konstWL 4 (2^(F.fracBits+F.ebits)) u).1 ++
    [ci 5 sx sx u, ci 3 dst sx q]
  let zero := [ci 5 sx sx sy, ci 1 q 0 0]
  let finish := [ci 1 u 0 0, ci 14 t q u] ++ branch t zero
    (right ++ left ++ rounded.1 ++ [ci 2 q (dst+16) 0] ++ carry ++ pack)
  pure (inputs.1 ++ sort ++ aligned.1 ++ signed ++ finish ++ sign,
    max inputs.2 (max aligned.2 (max shift.2 rounded.2)))

/-- Recover the actual operand-code prefix from successful compilation of the
    complete candidate. No separately supplied instruction-list decomposition
    is trusted by the execution theorem. -/
theorem floatFiniteAddL_operand_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code, top)) :
    ∃ ca ta cb tb tail, a (dst+1) = some (ca,ta) ∧
      b (dst+2) = some (cb,tb) ∧ code = (ca ++ cb) ++ tail ∧
      ta ≤ top ∧ tb ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨restCode,restTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq result
  refine ⟨av.1, av.2, bv.1, bv.2, code.drop (av.1.length + bv.1.length), hav, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hbv
  · rw [← result.1, ← inputEq.1, ← afterEq.1]
    simp [List.drop_append, List.append_assoc]
  · omega
  · omega

#print axioms floatFiniteAddL_operand_code

/-- Execute both operand producers inside the actual compiled finite candidate.
    The continuation is fetched from preserved code, with the environment,
    permissions and arbitrary reserved prefix carried through both writes.
    This stops before field decoding; it does not assert IEEE correctness of
    the subsequent sort, jam, normalization or packing instructions. -/
theorem floatFiniteAddL_read_operands {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (room : top ≤ K) (slots : dst+3 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ operandCode tail m', code = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K (dst+3)
        tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,tail,ha,hb,hcode,hta,htb⟩ :=
    floatFiniteAddL_operand_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agree := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  refine ⟨ca ++ cb,tail,m2,hcode,?_,agree,?_,readB,?_⟩
  · simpa only [List.length_append, pc_add] using runA.trans runB
  · exact slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  · exact pre.next agree (by omega) (by omega)

#print axioms floatFiniteAddL_read_operands

/-- Both IEEE formats compile and execute distinct operands jointly with a
    nonzero reserved environment prefix and an arbitrary enclosing frame. -/
theorem floatFiniteAddL_read_operands_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 19 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 19 tail ρ W 13 := by
  apply floatFiniteAddL_read_operands F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre

#print axioms floatFiniteAddL_read_operands_zeuge

/-- Lift a composed word proof through an environment reconstructed from the
    actual retained read. The fixed-slot load is never assumed universally sound
    under the caller's environment. -/
theorem retainedWordCode_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K dst input top reserved : Nat}
    {code : List II} (w result : Runner.W)
    (body : (Nat → Option (List II × Nat)) → Nat → Option (List II × Nat))
    (sound : ∀ {Δ : Ctx} (η : Env D Δ),
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j input 0],j+1)) w →
      WordCode (L := L) η (fun _ => True)
        (body (fun j => some ([ci 2 j input 0],j+1))) result)
    (compiled : body (fun j => some ([ci 2 j input 0],j+1)) dst = some (code,top))
    (room : top ≤ K) (dstRoom : dst ≤ K) (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w)
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code (· = result) := by
  obtain ⟨η, env⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  let x := frameWordVar (dst-FB) (input-FB) (by omega)
  have hx : vslot x = input := by
    dsimp only [x]
    rw [frameWordVar_slot]
    omega
  obtain ⟨v, rv, ev⟩ := env _ x
  rw [hx, read] at rv
  cases rv
  change w = BitVec.ofInt 64 (η.get x).n at ev
  have load' : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j input 0],j+1)) w := by
    intro fp' K' d c t hc ht mm pp hp
    have hc' : (fun (j : Nat) => some ([ci 2 j (FB+(input-FB)) 0],j+1)) d =
        some (c,t) := by
      have eq : (FB : Int) + ((input : Int) - FB) = input := by omega
      simpa only [eq] using hc
    have run := frameWordLoad (L := L) (dst-FB) (input-FB) (by omega) η
      (by simpa only [Nat.cast_add, Nat.cast_sub lower] using hc') ht mm pp hp
    simpa only [x, ← ev] using run
  have hp : Pre L m pc fp K dst code η (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame,
      pre.code, pre.far, env, trivial, wstab_true _ _⟩
  exact sound η load' compiled room m pc hp

#print axioms retainedWordCode_ok

/-- Execute the existing decoder on a retained word. The proof context is
    reconstructed from the actual frame; no decoded field or load contract is
    supplied. Arbitrary original reserved prefixes and outside-frame facts are
    recovered by the caller's continuation precondition. -/
theorem floatFieldL_retained {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K dst input top reserved : Nat}
    {code : List II} (offset width : Nat) (ho : offset < 64)
    (hm : 2^width - 1 < 2^64) (w : Runner.W)
    (compiled : floatFieldL offset width dst
      (fun j => some ([ci 2 j input 0],j+1)) = some (code,top))
    (room : top ≤ K) (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w)
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code (· = floatFieldWord w offset width) := by
  have dstRoom : dst ≤ K := by
    obtain ⟨output, shape, _⟩ := floatFieldL_shape offset width dst ho
      (fun j => some ([ci 2 j input 0],j+1)) _ _ rfl
    rw [compiled] at shape
    cases shape
    omega
  exact retainedWordCode_ok w (floatFieldWord w offset width)
    (fun load j => floatFieldL offset width j load)
    (fun η load => floatFieldL_ok offset width ho hm load)
    compiled room dstRoom lower retained read pre

#print axioms floatFieldL_retained

/-- Identify the first field decoder in the actual compiled continuation,
    including its ceiling. Neither the rest code nor a decoded field is assumed. -/
theorem floatFiniteAddL_first_field_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      code = (ca ++ cb) ++ (cf ++ tail) ∧ ta ≤ top ∧ tb ≤ top ∧ tf ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rw [floatStateSlotsL] at hc
  simp only [bind, pure, Option.bind_eq_some_iff] at hc
  obtain ⟨fv, hfv, afterF, hd, fieldEq⟩ := hc
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨aCode,aTop⟩
  rcases afterB with ⟨bCode,bTop⟩
  rcases afterF with ⟨fCode,fTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq fieldEq result
  refine ⟨av.1,av.2,bv.1,bv.2,fv.1,fv.2,
    fCode ++ code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1]
        simp only [List.append_assoc]
  all_goals omega

#print axioms floatFiniteAddL_first_field_code

/-- Extend the actual two-producer execution through its first field decoder.
    Both packed operands survive decoder temporaries; the remaining emitted code
    is fetchable under the original environment, world and reserved prefix. -/
theorem floatFiniteAddL_read_first_field {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (room : top ≤ K) (slots : dst+4 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail m', code = executed ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*executed.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) =
        some (floatFieldWord wa (F.fracBits+F.ebits) 1) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+4) tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,cf,tf,tail,ha,hb,hf,hcode,hta,htb,htf⟩ :=
    floatFiniteAddL_first_field_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agreeAB := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  have readA2 := slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  have preF := pre.next agreeAB (show dst+1 ≤ dst+3 by omega) (by omega)
  obtain ⟨m3,runF,agreeF,w,readF,valueF⟩ :=
    floatFieldL_retained (input := dst+1) (dst := dst+3) (F.fracBits+F.ebits) 1 width (by decide) wa hf
      (by omega) lower (by omega) readA2 preF.left
  subst w
  refine ⟨(ca++cb)++cf,tail,m3,by simpa [List.append_assoc] using hcode,
    ?_,agreeAB.trans (agreeF.mono (by omega)),
    slotRead_agree preF.frame agreeF (by omega) (by omega) readA2,
    slotRead_agree preF.frame agreeF (by omega) (by omega) readB,readF,?_⟩
  · simpa only [List.length_append, pc_add] using (runA.trans runB).trans (by simpa only [List.length_append, pc_add] using runF)
  · simpa only [List.length_append, pc_add] using
      preF.next agreeF (show dst+3 ≤ dst+4 by omega) (by omega)

#print axioms floatFiniteAddL_read_first_field

/-- Joint format witness with distinct operands and reserved prefix thirteen. -/
theorem floatFiniteAddL_read_first_field_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 20 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      m'.rd64 (slot fp 19) = some (floatFieldWord 7 (F.fracBits+F.ebits) 1) ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 20 tail ρ W 13 := by
  apply floatFiniteAddL_read_first_field F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> decide +kernel
  · decide +kernel
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_first_field_zeuge

/-- Recover both consecutive sign decoders from the actual emitted candidate. -/
theorem floatFiniteAddL_sign_fields_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf cg tg tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+4)
        (fun j => some ([ci 2 j (dst+2) 0],j+1)) = some (cg,tg) ∧
      code = (ca ++ cb) ++ (cf ++ (cg ++ tail)) ∧ ta ≤ top ∧ tb ≤ top ∧ tf ≤ top ∧ tg ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rw [floatStateSlotsL] at hc
  simp only [bind, pure, Option.bind_eq_some_iff] at hc
  obtain ⟨fv, hfv, afterF, hd, fieldEq⟩ := hc
  rw [floatStateSlotsL] at hd
  simp only [bind, pure, Option.bind_eq_some_iff] at hd
  obtain ⟨gv, hgv, afterG, he, signEq⟩ := hd
  rcases afterG with ⟨gCode,gTop⟩
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨aCode,aTop⟩
  rcases afterB with ⟨bCode,bTop⟩
  rcases afterF with ⟨fCode,fTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq fieldEq signEq result
  refine ⟨av.1,av.2,bv.1,bv.2,fv.1,fv.2,gv.1,gv.2,
    gCode ++ code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · simpa [Nat.add_assoc] using hgv
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1, ← signEq.1]
        simp only [List.append_assoc]
  all_goals omega

#print axioms floatFiniteAddL_sign_fields_code

/-- Execute both sign decoders while retaining both operands and the first result. -/
theorem floatFiniteAddL_read_sign_fields {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (room : top ≤ K) (slots : dst+5 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail m', code = executed ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*executed.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) =
        some (floatFieldWord wa (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) =
        some (floatFieldWord wb (F.fracBits+F.ebits) 1) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+5) tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,cf,tf,cg,tg,tail,ha,hb,hf,hg,hcode,hta,htb,htf,htg⟩ :=
    floatFiniteAddL_sign_fields_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agreeAB := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  have readA2 := slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  have preF := pre.next agreeAB (show dst+1 ≤ dst+3 by omega) (by omega)
  obtain ⟨m3,runF,agreeF,w,readF,valueF⟩ :=
    floatFieldL_retained (input := dst+1) (dst := dst+3) (F.fracBits+F.ebits) 1 width (by decide) wa hf
      (by omega) lower (by omega) readA2 preF.left
  subst w
  have preG := preF.next agreeF (show dst+3 ≤ dst+4 by omega) (by omega)
  have readB3 := slotRead_agree preF.frame agreeF (by omega) (by omega) readB
  obtain ⟨m4,runG,agreeG,w,readG,valueG⟩ :=
    floatFieldL_retained (input := dst+2) (dst := dst+4) (F.fracBits+F.ebits) 1 width
      (by decide) wb hg (by omega) (by omega) (by omega) readB3 preG.left
  subst w
  have agreeFG := agreeF.trans (agreeG.mono (show dst+3 ≤ dst+4 by omega))
  refine ⟨((ca++cb)++cf)++cg,tail,m4,by simpa [List.append_assoc] using hcode,
    ?_,agreeAB.trans (agreeFG.mono (by omega)),
    slotRead_agree preF.frame agreeFG (by omega) (by omega) readA2,
    slotRead_agree preF.frame agreeFG (by omega) (by omega) readB,
    slotRead_agree preG.frame agreeG (by omega) (by omega) readF,readG,?_⟩
  · simpa only [List.length_append, pc_add] using
      ((runA.trans runB).trans (by simpa only [List.length_append, pc_add] using runF)).trans
        (by simpa only [List.length_append, pc_add] using runG)
  · simpa only [List.length_append, pc_add] using
      preG.next agreeG (show dst+4 ≤ dst+5 by omega) (by omega)

#print axioms floatFiniteAddL_read_sign_fields

/-- Joint f32/f64 execution witness with distinct operands and reserved prefix. -/
theorem floatFiniteAddL_read_sign_fields_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 21 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      m'.rd64 (slot fp 19) = some (floatFieldWord 7 (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp 20) = some (floatFieldWord 11 (F.fracBits+F.ebits) 1) ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 21 tail ρ W 13 := by
  apply floatFiniteAddL_read_sign_fields F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> decide +kernel
  · decide +kernel
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_sign_fields_zeuge

/-- Execute a whole batch from retained frame reads in one reconstructed context.
    Every producer uses the same concrete input frame; later temporary writes are
    handled by the existing sequential slot theorem. -/
theorem retainedWordCodes_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base top reserved : Nat}
    {code tail : List II}
    (ps : List (Nat → Option (List II × Nat))) (values : Nat → Runner.W)
    (sound : ∀ {Δ : Ctx} (η : Env D Δ),
      (∀ input w, FB ≤ input → input < base →
        m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w →
        WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j input 0],j+1)) w) →
      ∀ i, (hi : i < ps.length) →
        WordCode (L := L) η (fun _ => True) ps[i] (values i))
    (compiled : floatStateSlotsL base ps = some (code,top))
    (room : top ≤ K) (lower : FB ≤ base) (slots : base+ps.length ≤ K)
    (pre : Pre L m pc fp K base (code++tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      (∀ i, i < ps.length →
        m'.rd64 (slot fp (BitVec.ofNat 64 (base+i))) = some (values i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*code.length)) fp K (base+ps.length) tail ρ W reserved := by
  obtain ⟨η, env⟩ := frameWordEnv (L := L) (n := base-FB) pre.frame (by omega)
  have loads : ∀ input w, FB ≤ input → input < base →
      m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w →
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j input 0],j+1)) w := by
    intro input w lo hi read
    let x := frameWordVar (base-FB) (input-FB) (by omega)
    have hx : vslot x = input := by
      dsimp only [x]
      rw [frameWordVar_slot]
      omega
    obtain ⟨v, rv, ev⟩ := env _ x
    rw [hx, read] at rv
    cases rv
    change w = BitVec.ofInt 64 (η.get x).n at ev
    intro fp' K' d c t hc ht mm pp hp
    have hc' : (fun (j : Nat) => some ([ci 2 j (FB+(input-FB)) 0],j+1)) d =
        some (c,t) := by
      have eq : (FB : Int) + ((input : Int) - FB) = input := by omega
      simpa only [eq] using hc
    have run := frameWordLoad (L := L) (base-FB) (input-FB) (by omega) η
      (by simpa only [Nat.cast_add, Nat.cast_sub lo] using hc') ht mm pp hp
    simpa only [x, ← ev] using run
  have hp : Pre L m pc fp K base code η (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.left.small, pre.frame,
      pre.left.code, pre.left.far, env, trivial, wstab_true _ _⟩
  obtain ⟨m',run,agree,reads⟩ := floatStateSlotsL_ok ps values compiled room slots
    (fun i hi c t hc ht mm pp hp => sound η loads i hi hc ht mm pp hp) m pc hp
  exact ⟨m',run,agree,reads,pre.next agree (by omega) (by omega)⟩

#print axioms retainedWordCodes_ok

/-- Four consecutive retained reads jointly witness the batch rule, with
    distinct operands, an arbitrary continuation and reserved prefix thirteen. -/
theorem retainedWordCodes_ok_zeuge {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {tail : List II}
    (room : 25 ≤ K)
    (readA : m.rd64 (slot fp 17) = some 7)
    (readB : m.rd64 (slot fp 18) = some 11)
    (pre : Pre L m pc fp K 21
      ([ci 2 21 17 0,ci 2 22 18 0,ci 2 23 17 0,ci 2 24 18 0]++tail) ρ W 13) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ m' ∧ Agree fp 21 K m m' ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (21+i))) =
        some (if i % 2 = 0 then 7 else 11)) ∧
      Pre L m' (pc+64) fp K 25 tail ρ W 13 := by
  let load := fun (input j : Nat) => some ([ci 2 j input 0],j+1)
  let ps := [load 17,load 18,load 17,load 18]
  let values := fun (i : Nat) => (if i % 2 = 0 then 7 else 11 : Runner.W)
  have compiled : floatStateSlotsL 21 ps =
      some ([ci 2 21 17 0,ci 2 22 18 0,ci 2 23 17 0,ci 2 24 18 0],25) := rfl
  have result := retainedWordCodes_ok (L := L) ps values (by
    intro Δ η loads i hi
    have bound : i < 4 := hi
    interval_cases i <;> norm_num [ps,values] <;>
      intro fp K d c top hc ht mm pp hp <;>
      first | exact loads 17 7 (by decide) (by decide) readA hc ht mm pp hp
            | exact loads 18 11 (by decide) (by decide) readB hc ht mm pp hp)
    compiled room (by decide) room pre
  simpa [ps,values] using result

#print axioms retainedWordCodes_ok_zeuge

/-- The four remaining producers, literally the exponent and magnitude
    expressions emitted by `floatFiniteAddL`. -/
def finiteAddRemaining (F : Gleitkomma.Format) (dst : Nat) :=
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let field := fun start width j p => floatFieldL start width j p
  let exponent := fun p j => wordL 3 j (field F.fracBits F.ebits j p)
    (wordK 14 (j+1) (field F.fracBits F.ebits (j+1) p) 0)
  let magnitude := fun p j => wordK 5 j
    (wordL 3 j (field 0 F.fracBits j p)
      (wordL 5 (j+1)
        (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
          (wordK 14 (j+2) (field F.fracBits F.ebits (j+2) p) 0))
        (some (konstWL 4 (2^F.fracBits) (j+2))))) 8
  [exponent (load (dst+1)), exponent (load (dst+2)),
    magnitude (load (dst+1)), magnitude (load (dst+2))]

def finiteAddRemainingValue (F : Gleitkomma.Format) (a b : Runner.W) (i : Nat) : Runner.W :=
  let w := if i % 2 = 0 then a else b
  let e := floatFieldWord w F.fracBits F.ebits
  if i < 2 then e + Runner.IR.bool (e == 0)
  else (floatFieldWord w 0 F.fracBits +
    (1 - Runner.IR.bool (e == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8

omit [Kern] in
/-- Exact canonical decoder values retain the exponent/significand correlation
    needed by unequal-exponent subtraction after the actual SORT. -/
theorem finiteAddRemainingValue_canonical (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax)
    (i : Nat) (hi : i < 4) :
    let x := if i % 2 = 0 then a else b
    (finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i).toNat =
      if i < 2 then max x.bexp 1
      else 8 * (x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
  have one (x : Gleitkomma.GBits F) (hx : Gleitkomma.wf F x)
      (fx : x.bexp ≠ F.bexpMax) :
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F x)
      let e := floatFieldWord w F.fracBits F.ebits
      let f := floatFieldWord w 0 F.fracBits
      (e + Runner.IR.bool (e == 0)).toNat = max x.bexp 1 ∧
      ((f + (1 - Runner.IR.bool (e == 0)) *
        BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat =
        8 * (x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
    obtain ⟨fraction, exponent⟩ := floatFieldWord_canonical F dense width x hx
    have bounds := floatFiniteAdd_input_bounds F dense width precision exponents x hx fx
    dsimp only at bounds ⊢
    rw [fraction, exponent] at bounds
    have cap : (2 : Nat)^F.fracBits < 2^64 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) precision) (by decide)
    have ecap : x.bexp < 2^64 := by
      have := (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x))
        F.fracBits F.ebits).isLt
      rw [exponent] at this
      exact this
    have fcap : x.frac < 2^64 := lt_trans hx.2 cap
    have ez : (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x))
        F.fracBits F.ebits == 0#64) = decide (x.bexp = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
        exponent, BitVec.toNat_zero]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [ez]
    norm_num only at cap ecap fcap
    by_cases hz : x.bexp = 0 <;>
      simp only [hz, ↓reduceIte] at bounds <;>
      simp only [hz, decide_true, decide_false, Runner.IR.bool, ↓reduceIte,
        Bool.false_eq_true, BitVec.ofNat_eq_ofNat, BitVec.sub_self,
        BitVec.sub_zero, BitVec.zero_mul, BitVec.one_mul, BitVec.add_zero,
        BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
        fraction, exponent] <;>
      norm_num only [BitVec.toNat_ofNat] <;>
      (try simp only [Nat.mod_eq_of_lt cap]) <;> omega
  have aa := one a ha fa
  have bb := one b hb fb
  interval_cases i <;> simp_all [finiteAddRemainingValue]

#print axioms finiteAddRemainingValue_canonical

omit [Kern] in
/-- Unequal exponents and nonzero fractions jointly witness the decoder
    correlation in both supported precisions, including a subnormal operand. -/
theorem finiteAddRemainingValue_canonical_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨false,2,1⟩
      let b : Gleitkomma.GBits F := ⟨true,0,2^F.fracBits-1⟩
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      ∀ i, i < 4 →
        let x := if i % 2 = 0 then a else b
        (finiteAddRemainingValue F
          (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
          (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i).toNat =
            if i < 2 then max x.bexp 1
            else 8*(x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
  intro F member
  have format : F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 := by simpa using member
  have dense : F.dicht := by
    rcases format with rfl | rfl
    · exact Gleitkomma.f32_dicht
    · exact Gleitkomma.f64_dicht
  have width : F.ebits + F.fracBits + 1 ≤ 64 := by
    rcases format with rfl | rfl <;> decide +kernel
  have precision : F.fracBits ≤ 52 := by rcases format with rfl | rfl <;> decide +kernel
  have exponents : 1 < F.bexpMax := by rcases format with rfl | rfl <;> decide +kernel
  have ha : Gleitkomma.wf F ⟨false,2,1⟩ := by
    rcases format with rfl | rfl <;> decide +kernel
  have hb : Gleitkomma.wf F ⟨true,0,2^F.fracBits-1⟩ := by
    rcases format with rfl | rfl <;> decide +kernel
  have fa : 2 ≠ F.bexpMax := by rcases format with rfl | rfl <;> decide +kernel
  have fb : 0 ≠ F.bexpMax := by omega
  exact ⟨ha,hb,fa,fb,fun i hi =>
    finiteAddRemainingValue_canonical F dense width precision exponents
      ⟨false,2,1⟩ ⟨true,0,2^F.fracBits-1⟩ ha hb fa fb i hi⟩

#print axioms finiteAddRemainingValue_canonical_zeuge

omit [Kern] in
/-- Bounds transfer through the literal decoder arithmetic without word wrap. -/
theorem finiteAddRemainingValue_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax)
    (i : Nat) (hi : i < 4) :
    let w := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i
    if i < 2 then 1 ≤ w.toNat ∧ w.toNat < F.bexpMax
    else w.toNat < 2^56 := by
  have one (x : Gleitkomma.GBits F) (hx : Gleitkomma.wf F x)
      (fx : x.bexp ≠ F.bexpMax) :
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F x)
      let e := floatFieldWord w F.fracBits F.ebits
      let f := floatFieldWord w 0 F.fracBits
      (1 ≤ (e + Runner.IR.bool (e == 0)).toNat ∧
        (e + Runner.IR.bool (e == 0)).toNat < F.bexpMax) ∧
      ((f + (1 - Runner.IR.bool (e == 0)) *
        BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat < 2^56 := by
    have bounds := floatFiniteAdd_input_bounds F dense width precision exponents x hx fx
    dsimp only at bounds ⊢
    let e := floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x)) F.fracBits F.ebits
    let f := floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x)) 0 F.fracBits
    change 1 ≤ max e.toNat 1 ∧ max e.toNat 1 < F.bexpMax ∧
      8*(f.toNat + if e.toNat = 0 then 0 else 2^F.fracBits) < 2^(F.fracBits+4) ∧
      8*(f.toNat + if e.toNat = 0 then 0 else 2^F.fracBits) < 2^56 at bounds
    have cap : (2 : Nat)^F.fracBits < 2^64 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) precision) (by decide)
    change (1 ≤ (e + Runner.IR.bool (e == 0)).toNat ∧
      (e + Runner.IR.bool (e == 0)).toNat < F.bexpMax) ∧
      ((f + (1 - Runner.IR.bool (e == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat < 2^56
    by_cases hz : e = 0
    · simp [hz, Runner.IR.bool, BitVec.toNat_mul] at bounds ⊢
      omega
    · have hn : e.toNat ≠ 0 := by
        intro h
        exact hz (BitVec.eq_of_toNat_eq h)
      have ep : 1 ≤ e.toNat := by omega
      have test : (e == 0#64) = false := by
        exact beq_eq_false_iff_ne.mpr hz
      simp only [Runner.IR.bool, BitVec.ofNat_eq_ofNat, test, Bool.false_eq_true, ↓reduceIte,
        BitVec.add_zero, BitVec.sub_zero, BitVec.one_mul]
      simp only [hn, ↓reduceIte, Nat.max_eq_left ep] at bounds
      constructor
      · exact ⟨ep,bounds.2.1⟩
      · simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
        norm_num only [BitVec.toNat_ofNat]
        rw [show 2^F.fracBits % 18446744073709551616 = 2^F.fracBits from Nat.mod_eq_of_lt cap, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
  have aa := one a ha fa
  have bb := one b hb fb
  interval_cases i
  · simpa [finiteAddRemainingValue] using aa.1
  · simpa [finiteAddRemainingValue] using bb.1
  · simpa [finiteAddRemainingValue] using aa.2
  · simpa [finiteAddRemainingValue] using bb.2

omit [Kern] in
theorem finiteAddRemainingValue_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ i < 4,
      let a : Gleitkomma.GBits F := ⟨true,0,1⟩
      let b : Gleitkomma.GBits F := ⟨false,F.bexpMax-1,2^F.fracBits-1⟩
      let w := finiteAddRemainingValue F
        (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i
      if i < 2 then 1 ≤ w.toNat ∧ w.toNat < F.bexpMax
      else w.toNat < 2^56 := by
  intro F member i hi
  apply finiteAddRemainingValue_bounds F
  all_goals try { simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with rfl | rfl
                  all_goals first | exact Gleitkomma.f32_dicht | exact Gleitkomma.f64_dicht | decide +kernel }
  exact hi

#print axioms finiteAddRemainingValue_bounds_zeuge

#print axioms finiteAddRemainingValue_bounds

omit [Kern] in
/-- A strictly larger decoded exponent supplies a normal significand. Even
    half of the smaller significand plus a sticky increment is strictly smaller.
    This is derived from encoded operands, including subnormal smaller inputs. -/
theorem finiteAddRemainingValue_unequal (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let v := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
    (v 1).toNat < (v 0).toNat → (v 3).toNat / 2 + 1 < (v 2).toNat := by
  dsimp only
  have eqs := finiteAddRemainingValue_canonical F dense width precision exponents
    a b ha hb fa fb
  have e0 := eqs 0 (by decide)
  have e1 := eqs 1 (by decide)
  have m0 := eqs 2 (by decide)
  have m1 := eqs 3 (by decide)
  norm_num only [Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] at e0 e1 m0 m1
  rw [e0,e1,m0,m1]
  intro order
  have normal : a.bexp ≠ 0 := by omega
  have af := ha.2
  have bf := hb.2
  simp only [normal, ↓reduceIte]
  split <;> omega

#print axioms finiteAddRemainingValue_unequal

omit [Kern] in
/-- Saturating alignment by a positive distance is bounded by half the input
    plus one sticky increment, with no premise about the discarded remainder. -/
theorem floatShiftJamWord_half_bound (a k : Runner.W) (positive : 0 < k.toNat) :
    (floatShiftJamWord a k).toNat ≤ a.toNat / 2 + 1 := by
  unfold floatShiftJamWord
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  let b := (Runner.IR.bool (!(a == ((a >>> k.toNat) <<< k.toNat)))).toNat
  change (a.toNat / 2^k.toNat ||| b) ≤ a.toNat / 2 + 1
  have bit : b ≤ 1 := by
    dsimp only [b]
    unfold Runner.IR.bool
    split <;> decide
  have halves : (a.toNat / 2^k.toNat ||| b) / 2 = (a.toNat / 2^k.toNat) / 2 := by
    rw [Nat.or_div_two, show b / 2 = 0 by omega, Nat.or_zero]
  have rem := Nat.mod_lt (a.toNat / 2^k.toNat ||| b) (by decide : 0 < 2)
  have division := Nat.mod_add_div (a.toNat / 2^k.toNat ||| b) 2
  have denominator : 2 ≤ 2^k.toNat := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) positive
    simpa using this
  have quotient := Nat.div_le_div_left (a := a.toNat) denominator (by decide)
  omega

#print axioms floatShiftJamWord_half_bound
omit [Kern] in
/-- Actual decoded word subtraction at unequal exponents is positive after
    saturating SHIFTJAM; no NONZERO or result-invariant premise is needed. -/
theorem finiteAddRemainingValue_unequal_positive (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let v := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
    (v 1).toNat < (v 0).toNat →
      0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt := by
  dsimp only
  let v := finiteAddRemainingValue F
    (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
    (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
  change (v 1).toNat < (v 0).toNat →
    0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt
  intro order
  have delta : 0 < (v 0-v 1).toNat := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using Nat.le_of_lt order)]
    omega
  have half := floatShiftJamWord_half_bound (v 3) (v 0-v 1) delta
  have gap := finiteAddRemainingValue_unequal F dense width precision exponents
    a b ha hb fa fb order
  change (v 3).toNat / 2 + 1 < (v 2).toNat at gap
  have bound := finiteAddRemainingValue_bounds F dense width precision exponents
    a b ha hb fa fb 2 (by decide)
  change (v 2).toNat < 2^56 at bound
  have qint : (v 2).toInt = ((v 2).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have jint : (floatShiftJamWord (v 3) (v 0-v 1)).toInt =
      ((floatShiftJamWord (v 3) (v 0-v 1)).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [BitVec.toInt_sub, qint, jint, Int.bmod_eq_of_le (by omega) (by omega)]
  omega

#print axioms finiteAddRemainingValue_unequal_positive

omit [Kern] in
/-- Both precisions jointly realize strict SORT order, opposite signs, a
    subnormal smaller input, nonzero discarded bits, and positive subtraction. -/
theorem finiteAddRemainingValue_unequal_positive_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨false,5,1⟩
      let b : Gleitkomma.GBits F := ⟨true,0,2^F.fracBits-1⟩
      let v := finiteAddRemainingValue F
        (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      (v 1).toNat < (v 0).toNat ∧
      (v 3).toNat % 2^(v 0-v 1).toNat ≠ 0 ∧
      0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt := by
  intro F member
  have format : F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 := by simpa using member
  rcases format with rfl | rfl <;> decide +kernel

#print axioms finiteAddRemainingValue_unequal_positive_zeuge


/-- All four actual decoder expressions are sound in the reconstructed frame. -/
theorem finiteAddRemaining_sound {Δ : Ctx} (η : Env D Δ)
    (F : Gleitkomma.Format) (dst : Nat) (a b : Runner.W)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (ha : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j (dst+1) 0],j+1)) a)
    (hb : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j (dst+2) 0],j+1)) b) :
    ∀ i, (hi : i < (finiteAddRemaining F dst).length) →
      WordCode (L := L) η (fun _ => True) (finiteAddRemaining F dst)[i]
        (finiteAddRemainingValue F a b i) := by
  have decoder : ∀ (p : Nat → Option (List II × Nat)) (w : Runner.W),
      WordCode (L := L) η (fun _ => True) p w →
      WordCode (L := L) η (fun _ => True)
        (fun j => wordL 3 j (floatFieldL F.fracBits F.ebits j p)
          (wordK 14 (j+1) (floatFieldL F.fracBits F.ebits (j+1) p) 0))
        (floatFieldWord w F.fracBits F.ebits + Runner.IR.bool (floatFieldWord w F.fracBits F.ebits == 0)) ∧
      WordCode (L := L) η (fun _ => True)
        (fun j => wordK 5 j
          (wordL 3 j (floatFieldL 0 F.fracBits j p)
            (wordL 5 (j+1)
              (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
                (wordK 14 (j+2) (floatFieldL F.fracBits F.ebits (j+2) p) 0))
              (some (konstWL 4 (2^F.fracBits) (j+2))))) 8)
        ((floatFieldWord w 0 F.fracBits +
          (1 - Runner.IR.bool (floatFieldWord w F.fracBits F.ebits == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8) := by
    intro p w hp
    have e : WordCode (L := L) η (fun _ => True) _ _ := floatFieldL_ok F.fracBits F.ebits frac mask hp
    have f : WordCode (L := L) η (fun _ => True) _ _ := floatFieldL_ok 0 F.fracBits (by decide) fracMask hp
    have z : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 0 (by decide)
    have one : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 1 (by decide)
    have eight : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 8 (by decide)
    have zero : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin e z (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
    have normal : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin one zero (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
    have hidden : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin normal (WordCode.konst (2^F.fracBits) hiddenBound)
      (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
    have mag : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin f hidden (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256)
    exact ⟨WordCode.bin e zero (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256),
      WordCode.bin mag eight (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)⟩
  intro i hi
  have bound : i < 4 := hi
  interval_cases i <;>
    intro fp K d c top hc ht mm pp hp
  all_goals simp only [finiteAddRemaining, List.getElem_cons_zero,
    List.getElem_cons_succ] at hc
  · simpa [finiteAddRemainingValue] using (decoder _ _ ha).1 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ hb).1 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ ha).2 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ hb).2 hc ht mm pp hp

#print axioms finiteAddRemaining_sound

theorem floatFiniteAddL_remaining_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf cg tg remaining rt tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+4)
        (fun j => some ([ci 2 j (dst+2) 0],j+1)) = some (cg,tg) ∧
      floatStateSlotsL (dst+5) (finiteAddRemaining F dst) = some (remaining,rt) ∧
      code = (ca ++ cb) ++ (cf ++ (cg ++ (remaining ++ tail))) ∧
      ta ≤ top ∧ tb ≤ top ∧ tf ≤ top ∧ tg ≤ top ∧ rt ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rw [floatStateSlotsL] at hc
  simp only [bind, pure, Option.bind_eq_some_iff] at hc
  obtain ⟨fv, hfv, afterF, hd, fieldEq⟩ := hc
  rw [floatStateSlotsL] at hd
  simp only [bind, pure, Option.bind_eq_some_iff] at hd
  obtain ⟨gv, hgv, afterG, he, signEq⟩ := hd
  rcases afterG with ⟨gCode,gTop⟩
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨aCode,aTop⟩
  rcases afterB with ⟨bCode,bTop⟩
  rcases afterF with ⟨fCode,fTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq fieldEq signEq result
  refine ⟨av.1,av.2,bv.1,bv.2,fv.1,fv.2,gv.1,gv.2,
    gCode,gTop,code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · simpa [Nat.add_assoc] using hgv
  · simpa [finiteAddRemaining, Nat.add_assoc] using he
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1, ← signEq.1]
        simp only [List.append_assoc]
  all_goals omega

#print axioms floatFiniteAddL_remaining_code

theorem floatFiniteAddL_read_fields {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (slots : dst+9 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail m', code = executed ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*executed.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) =
        some (floatFieldWord wa (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) =
        some (floatFieldWord wb (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (dst+5+i))) =
        some (finiteAddRemainingValue F wa wb i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+9) tail ρ W reserved ∧
      ∃ inputTop, floatStateSlotsL (dst+1)
        ([a,b,
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+2) 0],k+1))] ++
          finiteAddRemaining F dst) = some (executed,inputTop) := by
  obtain ⟨ca,ta,cb,tb,cf,tf,cg,tg,remaining,rt,tail,ha,hb,hf,hg,hr,hcode,hta,htb,htf,htg,htr⟩ :=
    floatFiniteAddL_remaining_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agreeAB := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  have readA2 := slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  have preF := pre.next agreeAB (show dst+1 ≤ dst+3 by omega) (by omega)
  obtain ⟨m3,runF,agreeF,w,readF,valueF⟩ :=
    floatFieldL_retained (input := dst+1) (dst := dst+3) (F.fracBits+F.ebits) 1 width (by decide) wa hf
      (by omega) lower (by omega) readA2 preF.left
  subst w
  have preG := preF.next agreeF (show dst+3 ≤ dst+4 by omega) (by omega)
  have readB3 := slotRead_agree preF.frame agreeF (by omega) (by omega) readB
  obtain ⟨m4,runG,agreeG,w,readG,valueG⟩ :=
    floatFieldL_retained (input := dst+2) (dst := dst+4) (F.fracBits+F.ebits) 1 width
      (by decide) wb hg (by omega) (by omega) (by omega) readB3 preG.left
  subst w
  have agreeFG := agreeF.trans (agreeG.mono (show dst+3 ≤ dst+4 by omega))
  have preR := preG.next agreeG (show dst+4 ≤ dst+5 by omega) (by omega)
  have readA4 := slotRead_agree preF.frame agreeFG (by omega) (by omega) readA2
  have readB4 := slotRead_agree preF.frame agreeFG (by omega) (by omega) readB
  obtain ⟨m5,runR,agreeR,reads,rest⟩ := retainedWordCodes_ok (L := L)
    (finiteAddRemaining F dst) (finiteAddRemainingValue F wa wb) (by
      intro Δ η loads
      exact finiteAddRemaining_sound η F dst wa wb frac mask fracMask hiddenBound
        (loads (dst+1) wa lower (by omega) readA4)
        (loads (dst+2) wb (by omega) (by omega) readB4))
    hr (by omega) (by omega) (by simpa [finiteAddRemaining] using slots) preR
  have runPrefix := ((runA.trans runB).trans
    (by simpa only [List.length_append, pc_add] using runF)).trans
      (by simpa only [List.length_append, pc_add] using runG)
  refine ⟨(((ca++cb)++cf)++cg)++remaining,tail,m5,
    by simpa [List.append_assoc] using hcode,?_,
    agreeAB.trans ((agreeFG.trans (agreeR.mono (by omega))).mono (by omega)),
    slotRead_agree preR.frame agreeR (by omega) (by omega) readA4,
    slotRead_agree preR.frame agreeR (by omega) (by omega) readB4,
    slotRead_agree preR.frame agreeR (by omega) (by omega)
      (slotRead_agree preG.frame agreeG (by omega) (by omega) readF),
    slotRead_agree preR.frame agreeR (by omega) (by omega) readG,?_,?_,?_⟩
  · simpa only [List.length_append, pc_add] using runPrefix.trans
      (by simpa only [List.length_append, pc_add] using runR)
  · simpa only [finiteAddRemaining, List.length_cons, List.length_nil,
      List.length_append, pc_add] using reads
  · simpa only [finiteAddRemaining, List.length_cons, List.length_nil,
      List.length_append, pc_add, Nat.add_assoc] using rest

  · refine ⟨max ta (max tb (max tf (max tg rt))), ?_⟩
    simp only [List.cons_append, List.nil_append]
    rw [floatStateSlotsL, ha]
    simp only [bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hb, bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hf, bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hg, bind, pure, Option.bind_some, hr,
      List.append_assoc]

#print axioms floatFiniteAddL_read_fields

theorem floatFiniteAddL_read_fields_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 25 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      m'.rd64 (slot fp 19) = some (floatFieldWord 7 (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp 20) = some (floatFieldWord 11 (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (21+i))) =
        some (finiteAddRemainingValue F 7 11 i)) ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 25 tail ρ W 13 ∧
      ∃ inputTop, floatStateSlotsL (16+1)
        ([ (fun (j : Nat) => some ([ci 1 j 7 0],j+1)), (fun (j : Nat) => some ([ci 1 j 11 0],j+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (16+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (16+2) 0],k+1))] ++
          finiteAddRemaining F 16) = some (operandCode,inputTop) := by
  apply floatFiniteAddL_read_fields F 16
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
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_fields_zeuge

/-- Successful whole compilation fixes the continuation after all eight input
    producers. In particular the ordering prefix uses the actual retained
    exponent and magnitude slots, and its three scratch slots start at dst+9.
    This is a code boundary only; it does not assert execution of the swap. -/
theorem floatFiniteAddL_order_continuation (F : Gleitkomma.Format) (dst : Nat)
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
          ci 9 (dst+9) (dst+9) (dst+10)] ++ tail) ∧
      inputTop ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  refine ⟨inputs.1,inputs.2,code.drop (inputs.1.length+5),?_,?_,?_⟩
  · simpa [finiteAddRemaining] using hi
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    rw [← result.1]
    simp [List.drop_append, List.append_assoc]
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    omega

#print axioms floatFiniteAddL_order_continuation

/-- The first ordering instruction consumes the two retained effective
    exponents and returns the actual continuation Pre, at the same scratch
    boundary. It makes no universally quantified fixed-slot WordCode claim. -/
theorem floatFiniteAddL_order_first {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {tail : List II} {ex ey : Runner.W}
    (room : dst+9 < K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+5) (dst+6)] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m' ∧
      Agree fp (dst+9) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (ex.slt ey)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
      Pre L m' (pc+16) fp K (dst+9) tail ρ W reserved := by
  obtain ⟨m',run,agree,w,read,value⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+9) pre.left room
    (by omega) (by omega) rx ry
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w
  refine ⟨m',?_,agree,read,
    slotRead_agree pre.frame agree (by omega) (by omega) rx,
    slotRead_agree pre.frame agree (by omega) (by omega) ry,?_⟩
  · simpa using run
  · simpa using pre.next agree (Nat.le_refl _) (by omega)

#print axioms floatFiniteAddL_order_first

theorem floatFiniteAddL_read_fields_to_order {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (slots : dst+9 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail m', code = executed ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*executed.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) =
        some (floatFieldWord wa (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) =
        some (floatFieldWord wb (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (dst+5+i))) =
        some (finiteAddRemainingValue F wa wb i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+9) tail ρ W reserved ∧
      ∃ orderingTail, tail =
        [ci 13 (dst+9) (dst+5) (dst+6),
         ci 14 (dst+10) (dst+5) (dst+6),
         ci 13 (dst+11) (dst+7) (dst+8),
         ci 5 (dst+10) (dst+10) (dst+11),
         ci 9 (dst+9) (dst+9) (dst+10)] ++ orderingTail := by
  obtain ⟨executed,tail,m',hc,run,agree,ra,rb,rsx,rsy,reads,rest,it,hi⟩ :=
    floatFiniteAddL_read_fields F dst a b wa wb compiled width lower frac mask
      fracMask hiddenBound room slots producerA producerB pre
  obtain ⟨inputs,inputTop,orderingTail,hinputs,hcode,_⟩ :=
    floatFiniteAddL_order_continuation F dst a b compiled
  have heq : inputs = executed := by
    rw [hi] at hinputs
    exact (Prod.mk.inj (Option.some.inj hinputs)).1.symm
  subst inputs
  have ht := List.append_cancel_left (hc.symm.trans hcode)
  exact ⟨executed,tail,m',hc,run,agree,ra,rb,rsx,rsy,reads,rest,orderingTail,ht⟩

#print axioms floatFiniteAddL_read_fields_to_order

theorem floatFiniteAddL_read_fields_to_order_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 25 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      m'.rd64 (slot fp 19) = some (floatFieldWord 7 (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp 20) = some (floatFieldWord 11 (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (21+i))) =
        some (finiteAddRemainingValue F 7 11 i)) ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 25 tail ρ W 13 ∧
      ∃ orderingTail, tail =
        [ci 13 25 21 22, ci 14 26 21 22, ci 13 27 23 24,
         ci 5 26 26 27, ci 9 25 25 26] ++ orderingTail := by
  apply floatFiniteAddL_read_fields_to_order F 16
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
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_fields_to_order_zeuge

/-- Exact read effect of a real frame write, including slots above the target. -/
theorem finiteAdd_write_reads {m : Runner.Mem} {fp : Runner.W} {K d : Nat}
    (frame : FrameOK m fp K) (hd : d < K) (v : Runner.W)
    (values : Nat → Runner.W)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i)) :
    ∀ i, i < K →
      (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat).rd64
        (slot fp (BitVec.ofNat 64 i)) = some (Function.update values d v i) := by
  intro i hi
  by_cases eq : i = d
  · subst i
    simpa using (wr_slot frame hd v).2.1
  · rw [Function.update_of_ne eq]
    rw [rd64_write_far]
    · exact reads i hi
    · unfold Far
      rw [slot_toNat frame.room hd, slot_toNat frame.room hi]
      constructor
      · have := frame.lt; omega
      constructor
      · have := frame.lt; omega
      · omega

/-- Execute real copies while retaining a simultaneous account of every frame
    word. The fold records writes; it is not an alternative runner semantics. -/
theorem finiteAdd_moves {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat}
    (moves : List (Nat × Nat)) (values : Nat → Runner.W) (tail : List II)
    (bounds : ∀ p ∈ moves, base ≤ p.1 ∧ p.1 < K ∧ p.2 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K base
      (moves.map (fun p => ci 2 p.1 p.2 0) ++ tail) ρ W reserved)
    (room : base ≤ K) :
    ∃ m', Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*moves.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) =
        some (moves.foldl (fun vs p => Function.update vs p.1 (vs p.2)) values i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*moves.length)) fp K base tail ρ W reserved := by
  induction moves generalizing m pc values with
  | nil => exact ⟨m, by simpa using (Star.refl ⟨pc,fp⟩ m), Agree.refl _ _ _ _, reads, by simpa using pre⟩
  | cons p ps ih =>
    obtain ⟨lower,hd,hs⟩ := bounds p (by simp)
    have hp : Pre L m pc fp K base
        ([ci 2 p.1 p.2 0] ++ (ps.map (fun p => ci 2 p.1 p.2 0) ++ tail)) ρ W reserved := by
      simpa using pre
    let next := write m (slot fp (BitVec.ofNat 64 p.1)) 8 (values p.2).toNat
    have wr := (wr_slot hp.frame hd (values p.2)).1
    have ag : Agree fp base K m next :=
      ((wr_slot hp.frame hd (values p.2)).2.2).mono lower
    have run : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ next := by
      apply star_ins hp.left.code (by simp [ci])
      have ins := hp.left.code 0 (by simp)
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
      simp only [ci, op]
      apply f2_run (t := ⟨pc,fp⟩) ins
      rw [sx_nat (by have := hp.small; omega)]
      apply run_rd64 (reads p.2 hs)
      simp only [ret1]
      apply f1_run (t := ⟨pc,fp⟩) ins
      rw [sx_nat (by have := hp.small; omega)]
      exact run_wr64 wr
    have rest := hp.next ag (Nat.le_refl _) room
    obtain ⟨out,run2,ag2,reads2,rest2⟩ := ih
      (Function.update values p.1 (values p.2))
      (fun q hq => bounds q (by simp [hq]))
      (finiteAdd_write_reads hp.frame hd (values p.2) values reads)
      (by simpa using rest)
    have pcEq : pc+16+BitVec.ofNat 64 (16*ps.length) =
        pc+BitVec.ofNat 64 (16*(ps.length+1)) := by
      rw [BitVec.add_assoc, BitVec.add_comm (16 : Runner.W), ← BitVec.add_assoc]
      exact pc_add16 pc ps.length
    refine ⟨out, ?_, ag.trans ag2, reads2, ?_⟩
    · rw [List.length_cons, ← pcEq]
      exact run.trans run2
    · rw [List.length_cons, ← pcEq]
      exact rest2

#print axioms finiteAdd_moves

/-- The actual nine-copy SWAP path exchanges all three operand fields jointly.
    Every other frame slot is retained, except the actual scratch slot whose
    final value is the original left significand. -/
theorem finiteAdd_moves_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II)
    (room : dst+9 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K (dst+3)
      ([ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
        ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
        ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+144,fp⟩ m' ∧ Agree fp (dst+3) K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if i = dst+3 then values (dst+4) else
         if i = dst+4 then values (dst+3) else
         if i = dst+5 then values (dst+6) else
         if i = dst+6 then values (dst+5) else
         if i = dst+7 then values (dst+8) else
         if i = dst+8 then values (dst+7) else
         if i = dst+9 then values (dst+7) else values i)) ∧
      Pre L m' (pc+144) fp K (dst+3) tail ρ W reserved := by
  have moves := finiteAdd_moves
    [(dst+9,dst+3),(dst+3,dst+4),(dst+4,dst+9),
     (dst+9,dst+5),(dst+5,dst+6),(dst+6,dst+9),
     (dst+9,dst+7),(dst+7,dst+8),(dst+8,dst+9)] values tail
    (L := L) (ρ := ρ) (W := W) (reserved := reserved)
    (m := m) (pc := pc) (fp := fp) (K := K) (base := dst+3)
  obtain ⟨out,run,ag,rd,rest⟩ := moves
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    reads (by simpa using pre) (by omega)
  refine ⟨out,by simpa using run,ag,?_,by simpa using rest⟩
  intro i hi
  have h := rd i hi
  simp [List.foldl, Function.update_apply] at h
  by_cases h3 : i = dst+3
  · subst i; simpa using h
  by_cases h4 : i = dst+4
  · subst i; simpa using h
  by_cases h5 : i = dst+5
  · subst i; simpa using h
  by_cases h6 : i = dst+6
  · subst i; simpa using h
  by_cases h7 : i = dst+7
  · subst i; simpa using h
  by_cases h8 : i = dst+8
  · subst i; simpa using h
  by_cases h9 : i = dst+9
  · subst i; simpa using h
  simpa [h3,h4,h5,h6,h7,h8,h9] using h

#print axioms finiteAdd_moves_zeuge

set_option maxHeartbeats 1200000 in
/-- Both emitted branch paths execute to their common continuation. The flag
    is read from real memory; the taken path executes all nine copies and the
    end jump, and the other path executes the conditional jump itself. -/
theorem floatFiniteAddL_swap_dispatch {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II) (swap : Bool)
    (room : dst+9 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (flag : values (dst+9) = Runner.IR.bool swap)
    (pre : Pre L m pc fp K (dst+3)
      ([ci 19 (dst+9) 176 0,
        ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
        ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
        ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0,
        ci 18 16 0 0] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+176,fp⟩ m' ∧ Agree fp (dst+3) K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if swap then
          if i = dst+3 then values (dst+4) else
          if i = dst+4 then values (dst+3) else
          if i = dst+5 then values (dst+6) else
          if i = dst+6 then values (dst+5) else
          if i = dst+7 then values (dst+8) else
          if i = dst+8 then values (dst+7) else
          if i = dst+9 then values (dst+7) else values i
         else values i)) ∧
      Pre L m' (pc+176) fp K (dst+3) tail ρ W reserved := by
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int)) (II.f 176) (II.f 0) := by
    simpa [ci] using pre.code 0 (by simp)
  have test := reads (dst+9) room
  rw [flag] at test
  have sxslot : sx (II.f ((dst+9 : Nat) : Int)) = BitVec.ofNat 64 (dst+9) :=
    sx_nat (by have := pre.small; omega)
  cases swap with
  | false =>
    have readZero : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some (0 : Runner.W) := by
      rw [sxslot]
      exact test
    have run := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_zero (t := ⟨pc,fp⟩) ins readZero)
    have endPre := pre.next (Agree.refl fp (dst+3) K m) (Nat.le_refl _) (by omega)
    refine ⟨m,?_,Agree.refl _ _ _ _,?_,?_⟩
    · apply Star.one
      have off : sx (II.f 176) = (176 : Runner.W) := by
        rw [sx_lit (by decide : lit32 176 = true)]; rfl
      rw [off] at run
      exact run
    · simpa using reads
    · simpa using endPre
  | true =>
    have readOne : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some (1 : Runner.W) := by
      rw [sxslot]
      exact test
    have run := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins readOne (by decide))
    have hp : Pre L m (pc+16) fp K (dst+3)
        ([ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
          ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
          ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0] ++
          ([ci 18 16 0 0] ++ tail)) ρ W reserved := by
      have h : Pre L m pc fp K (dst+3)
        ([ci 19 (dst+9) 176 0] ++ _) ρ W reserved := pre
      simpa using h.next (Agree.refl fp (dst+3) K m) (Nat.le_refl _) (by omega)
    obtain ⟨out,copies,ag,rd,rest⟩ := finiteAdd_moves_zeuge values
      ([ci 18 16 0 0] ++ tail) room reads hp
    have jumpIns : Runner.IR.InsAt out (pc+16+144) 18 (II.f 16) (II.f 0) (II.f 0) := by
      simpa [ci] using rest.code 0 (by simp)
    have jump := run_step (t := ⟨pc+16+144,fp⟩) jumpIns (by decide) (run_jmp (t := ⟨pc+16+144,fp⟩) jumpIns)
    have done := rest.next (Agree.refl fp (dst+3) K out) (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,by simpa using rd,?_⟩
    · have entry : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m := Star.one (by simpa only [nxt] using run)
      have finish : Star ⟨pc+16+144,fp⟩ out ⟨pc+176,fp⟩ out := Star.one (by
        have off : sx (II.f 16) = (16 : Runner.W) := by
          rw [sx_lit (by decide : lit32 16 = true)]; rfl
        rw [off] at jump
        simpa [BitVec.add_assoc] using jump)
      exact entry.trans (copies.trans finish)
    · simpa [BitVec.add_assoc] using done

#print axioms floatFiniteAddL_swap_dispatch

/-- Execute all five actual ordering instructions. The exponent comparison
    takes priority; the significand comparison breaks equal-exponent ties. -/
theorem floatFiniteAddL_order_compare {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {tail : List II} {ex ey q r : Runner.W}
    (room : dst+11 < K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+5) (dst+6), ci 14 (dst+10) (dst+5) (dst+6),
        ci 13 (dst+11) (dst+7) (dst+8), ci 5 (dst+10) (dst+10) (dst+11),
        ci 9 (dst+9) (dst+9) (dst+10)] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+80,fp⟩ m' ∧ Agree fp (dst+9) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (ex.slt ey || ((ex == ey) && q.slt r))) ∧
      Pre L m' (pc+80) fp K (dst+9) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+9)
    ([ci 13 (dst+9) (dst+5) (dst+6)] ++
     ([ci 14 (dst+10) (dst+5) (dst+6)] ++
      ([ci 13 (dst+11) (dst+7) (dst+8)] ++
       ([ci 5 (dst+10) (dst+10) (dst+11)] ++
        ([ci 9 (dst+9) (dst+9) (dst+10)] ++ tail))))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,e1⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+9) hp.left (by omega) (by omega) (by omega)
    rx ry (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w1
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  obtain ⟨m2,s2,a2,w2,r2,e2⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+10)
    {hp1.left with ctx := Nat.le_trans hp1.ctx (by omega : dst+9 ≤ dst+10)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+5) hp.frame a1 (by omega) (by omega) rx)
    (slotRead_agree (input := dst+6) hp.frame a1 (by omega) (by omega) ry)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst w2
  have hp2 := hp1.next (a2.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have ag2 := a1.trans (a2.mono (by omega : dst+9 ≤ dst+10))
  obtain ⟨m3,s3,a3,w3,r3,e3⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+11)
    {hp2.left with ctx := Nat.le_trans hp2.ctx (by omega : dst+9 ≤ dst+11)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+7) hp.frame ag2 (by omega) (by omega) rq)
    (slotRead_agree (input := dst+8) hp.frame ag2 (by omega) (by omega) rr)
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w3
  have hp3 := hp2.next (a3.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  obtain ⟨m4,s4,a4,w4,r4,e4⟩ := eng_bin_ok (a := dst+10) (b := dst+11) (d := dst+10)
    {hp3.left with ctx := Nat.le_trans hp3.ctx (by omega : dst+9 ≤ dst+10)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+10) hp2.frame a3 (by omega) (by omega) r2) r3
    (g := fun x y => some (x*y)) rfl (by decide) rfl
  subst w4
  have hp4 := hp3.next (a4.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have ag14 := (a2.trans (a3.mono (by omega : dst+10 ≤ dst+11))).trans a4
  obtain ⟨m5,s5,a5,w5,r5,e5⟩ := eng_bin_ok (a := dst+9) (b := dst+10) (d := dst+9) hp4.left (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+9) hp1.frame ag14 (by omega) (by omega) r1) r4
    (g := fun x y => some (x ||| y)) rfl (by decide) rfl
  subst w5
  have rest := hp4.next a5 (Nat.le_refl _) (by omega)
  refine ⟨m5,?_,(ag2.trans (a3.mono (by omega))).trans
    ((a4.mono (by omega)).trans a5),?_,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · convert r5 using 2
    cases hx : ex.slt ey <;> cases he : ex == ey <;> cases hq : q.slt r <;>
      simp [Runner.IR.bool, hx, he, hq]
  · simpa [BitVec.add_assoc] using rest

#print axioms floatFiniteAddL_order_compare

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

theorem floatFiniteAddL_read_fields_sort {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (sortRoom : dst+11 < K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail, ∃ values : Nat → Runner.W, ∃ out,
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
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256,fp⟩ out ∧
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
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256)
        fp K (dst+3) tail ρ W reserved := by
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
  refine ⟨executed,tail,values,out,hfull,run.trans sortRun,
    ag.trans (sortAgree.mono (by omega)),?_,sorted,finiteAdd_ordered_memory values sorted,done⟩
  have h0 : values (dst+1) = wa := by simp [values,ra]
  have h1 : values (dst+2) = wb := by simp [values,rb]
  have h2 : values (dst+3) = floatFieldWord wa (F.fracBits+F.ebits) 1 := by simp [values,rsx]
  have h3 : values (dst+4) = floatFieldWord wb (F.fracBits+F.ebits) 1 := by simp [values,rsy]
  have hf : ∀ i, i < 4 → values (dst+5+i) = finiteAddRemainingValue F wa wb i := by
    intro i hi
    simp [values,fields i hi]
  intro i hi
  interval_cases i
  · simpa using h0
  · simpa [Nat.add_assoc] using h1
  · simpa [Nat.add_assoc] using h2
  · simpa [Nat.add_assoc] using h3
  · simpa [Nat.add_assoc] using hf 0 (by omega)
  · simpa [Nat.add_assoc] using hf 1 (by omega)
  · simpa [Nat.add_assoc] using hf 2 (by omega)
  · simpa [Nat.add_assoc] using hf 3 (by omega)

#print axioms floatFiniteAddL_read_fields_sort

theorem floatFiniteAddL_read_fields_sort_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (sortRoom : 27 < K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ executed tail, ∃ values : Nat → Runner.W, ∃ out,
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
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256,fp⟩ out ∧
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
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256)
        fp K (16+3) tail ρ W 13 := by
  apply floatFiniteAddL_read_fields_sort F 16
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
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre



#print axioms floatFiniteAddL_read_fields_sort_zeuge

/-- Execute the actual alignment producer from retained ordered-state reads.
    Reification ties repeated loads to memory while scratch writes remain above
    every operand. The returned continuation keeps the original environment and
    arbitrary reserved prefix; no fixed-read WordCode is assumed. -/
theorem floatFiniteAddL_align_execute {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst top reserved : Nat} {code tail : List II} {ex ey r : Runner.W}
    (lower : FB ≤ dst+5) (room : top ≤ K) (slots : dst+17 ≤ K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (compiled : floatShiftJamL (dst+16)
      (fun j => some ([ci 2 j (dst+8) 0],j+1))
      (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
        (some ([ci 2 (j+1) (dst+6) 0],j+2))) = some (code,top))
    (pre : Pre L m pc fp K (dst+16) (code++tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ out ∧
      Agree fp (dst+16) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) =
        some (floatShiftJamWord r (ex-ey)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*code.length)) fp K (dst+17) tail ρ W reserved := by
  let producer := fun j => floatShiftJamL j
    (fun j => some ([ci 2 j (dst+8) 0],j+1))
    (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
      (some ([ci 2 (j+1) (dst+6) 0],j+2)))
  have batch : floatStateSlotsL (dst+16) [producer] = some (code,max top (dst+17)) := by
    simp [floatStateSlotsL, producer, compiled, Nat.add_assoc]
  obtain ⟨out,run,agree,reads,rest⟩ := retainedWordCodes_ok (L := L)
    [producer] (fun _ => floatShiftJamWord r (ex-ey)) (by
      intro Δ η loads i hi
      have iz : i = 0 := by have : i < 1 := hi; omega
      subst i
      change WordCode (L := L) η (fun _ => True) producer (floatShiftJamWord r (ex-ey))
      have a : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+8) 0],j+1)) r := loads (dst+8) r (by omega) (by omega) rr
      have x : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+5) 0],j+1)) ex := loads (dst+5) ex lower (by omega) rx
      have y : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+6) 0],j+1)) ey := loads (dst+6) ey (by omega) (by omega) ry
      have diff : WordCode (L := L) η (fun _ => True)
          (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
            (some ([ci 2 (j+1) (dst+6) 0],j+2))) (ex-ey) :=
        WordCode.bin x y (g := fun x y => some (x-y)) rfl rfl (by decide : 4 < 256)
      intro fp K d c top hc ht mm pp hp
      exact floatShiftJamL_ok a diff hc ht mm pp hp)
    batch (by omega) (by omega) (by simpa using slots) pre
  exact ⟨out,run,agree,by simpa using reads 0 (by simp),rest⟩

#print axioms floatFiniteAddL_align_execute

theorem floatFiniteAddL_align_execute_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K top : Nat} {code tail : List II}
    (room : top ≤ K) (slots : 16+17 ≤ K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some 5)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (16+6))) = some 2)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (16+8))) = some 97)
    (compiled : floatShiftJamL (16+16)
      (fun j => some ([ci 2 j (16+8) 0],j+1))
      (fun j => wordL 4 j (some ([ci 2 j (16+5) 0],j+1))
        (some ([ci 2 (j+1) (16+6) 0],j+2))) = some (code,top))
    (pre : Pre L m pc fp K (16+16) (code++tail) ρ W 13) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ out ∧
      Agree fp (16+16) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (16+16))) =
        some (13) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*code.length)) fp K (16+17) tail ρ W 13 := by
  have run := floatFiniteAddL_align_execute (L := L) (dst := 16)
    (ex := 5) (ey := 2) (r := 97) (by decide) room slots rx ry rr compiled pre
  simpa only [show floatShiftJamWord 97 (5-2) = 13 from by decide +kernel] using run

#print axioms floatFiniteAddL_align_execute_zeuge

/-- Execute the emitted signed arithmetic branch, including its conditional
    and unconditional jumps. The result is read from the same reached frame. -/
theorem floatFiniteAddL_signed_dispatch {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q r : Runner.W} (same : Bool) (tail : List II)
    (room : dst+9 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some (Runner.IR.bool same))
    (pre : Pre L m pc fp K (dst+7)
      ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
        ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+7) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (if same then q+r else q-r) ∧
      Pre L out (pc+64) fp K (dst+7) tail ρ W reserved := by
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int)) (II.f 48) (II.f 0) := by
    simpa [ci] using pre.code 0 (by simp)
  have test : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) =
      some (Runner.IR.bool same) := by
    rw [sx_nat (by have := pre.small; omega)]
    exact flag
  cases same with
  | false =>
    have jump := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_zero (t := ⟨pc,fp⟩) ins test)
    have off : sx (II.f 48) = (48 : Runner.W) := by
      rw [sx_lit (by decide : lit32 48 = true)]; rfl
    rw [off] at jump
    have hp : Pre L m (pc+48) fp K (dst+7)
        ([ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved := by
      have h : Pre L m pc fp K (dst+7)
          ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8), ci 18 32 0 0] ++
            ([ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := pre
      exact h.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    obtain ⟨out,run,ag,w,rd,eq⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+7) hp.left (by omega) (by omega) (by omega)
      rq rr (g := fun x y => some (x-y)) rfl (by decide) rfl
    subst w
    have rest := hp.next ag (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,rd,?_⟩
    · simpa [BitVec.add_assoc] using (Star.one jump).trans run
    · simpa [BitVec.add_assoc] using rest
  | true =>
    have step := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins test (by decide))
    have hp : Pre L m (pc+16) fp K (dst+7)
        ([ci 3 (dst+7) (dst+7) (dst+8)] ++
          ([ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := by
      have h : Pre L m pc fp K (dst+7) ([ci 19 (dst+9) 48 0] ++ _) ρ W reserved := pre
      exact h.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    obtain ⟨out,run,ag,w,rd,eq⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+7) hp.left (by omega) (by omega) (by omega)
      rq rr (g := fun x y => some (x+y)) rfl (by decide) rfl
    subst w
    have rest := hp.next ag (Nat.le_refl _) (by omega)
    have ji : Runner.IR.InsAt out (pc+16+16) 18 (II.f 32) (II.f 0) (II.f 0) := by
      simpa [ci] using rest.code 0 (by simp)
    have jump := run_step (t := ⟨pc+16+16,fp⟩) ji (by decide)
      (run_jmp (t := ⟨pc+16+16,fp⟩) ji)
    have off : sx (II.f 32) = (32 : Runner.W) := by
      rw [sx_lit (by decide : lit32 32 = true)]; rfl
    rw [off] at jump
    have done : Pre L out (pc+16+16+32) fp K (dst+7) tail ρ W reserved :=
      rest.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,rd,?_⟩
    · have first : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m := Star.one (by simpa [nxt] using step)
      simpa [BitVec.add_assoc] using first.trans (run.trans (Star.one jump))
    · simpa [BitVec.add_assoc] using done

#print axioms floatFiniteAddL_signed_dispatch

/-- Copy the actual jam result, compare the retained signs, and execute
    ADD/SUB in one Runner execution. No intermediate frame is supplied. -/
theorem floatFiniteAddL_signed_execute {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II)
    (room : dst+16 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K (dst+7)
      ([ci 2 (dst+8) (dst+16) 0, ci 14 (dst+9) (dst+3) (dst+4),
        ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
        ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+96,fp⟩ out ∧
      Agree fp (dst+7) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) =
        some (if values (dst+3) == values (dst+4) then
          values (dst+7)+values (dst+16) else values (dst+7)-values (dst+16)) ∧
      Pre L out (pc+96) fp K (dst+7) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+7)
      ([ci 2 (dst+8) (dst+16) 0] ++
        ([ci 14 (dst+9) (dst+3) (dst+4)] ++
          ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
            ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,rd1,hp1⟩ := finiteAdd_moves (base := dst+7) [(dst+8,dst+16)] values _
    (by simp; omega) reads (by simpa using hp) (by omega)
  have hp1 : Pre L m1 (pc+16) fp K (dst+7)
      ([ci 14 (dst+9) (dst+3) (dst+4)] ++
        ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
          ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := by
    simpa using hp1
  have r1 (i : Nat) (hi : i < dst+8) :
      m1.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i) := by
    simpa [Function.update_of_ne (show i ≠ dst+8 by omega)] using rd1 i (by omega)
  obtain ⟨m2,s2,a2,w,rd2,eq⟩ := eng_bin_ok (a := dst+3) (b := dst+4) (d := dst+9) (o := 14)
    {hp1.left with ctx := Nat.le_trans hp1.ctx (by omega : dst+7 ≤ dst+9)}
    (by omega) (by omega) (by omega) (r1 (dst+3) (by omega)) (r1 (dst+4) (by omega))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst w
  have hp2 := hp1.next (a2.mono (by omega : dst+7 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rq := slotRead_agree (input := dst+7) hp1.frame a2 (by omega) (by omega)
    (r1 (dst+7) (by omega))
  have rr : m2.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some (values (dst+16)) := by
    apply slotRead_agree hp1.frame a2 (by omega) (by omega)
    simpa using rd1 (dst+8) (by omega)
  obtain ⟨out,s3,a3,rd3,hp3⟩ := floatFiniteAddL_signed_dispatch
    (values (dst+3) == values (dst+4)) tail (by omega) rq rr rd2 hp2
  refine ⟨out,?_,a1.trans ((a2.mono (by omega)).trans a3),rd3,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans s3)
  · simpa [BitVec.add_assoc] using hp3

#print axioms floatFiniteAddL_signed_execute

set_option maxHeartbeats 2400000 in
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
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 1 else 4) := by
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
        | _ => finiteAddRemainingValue F wa wb (i-4) := by
    have h0 : values (dst+1) = wa := by simp [values,ra]
    have h1 : values (dst+2) = wb := by simp [values,rb]
    have h2 : values (dst+3) = floatFieldWord wa (F.fracBits+F.ebits) 1 := by simp [values,rsx]
    have h3 : values (dst+4) = floatFieldWord wb (F.fracBits+F.ebits) 1 := by simp [values,rsy]
    have hf : ∀ i, i < 4 → values (dst+5+i) = finiteAddRemainingValue F wa wb i := by
      intro i hi
      simp [values,fields i hi]
    intro i hi
    interval_cases i
    · simpa using h0
    · simpa [Nat.add_assoc] using h1
    · simpa [Nat.add_assoc] using h2
    · simpa [Nat.add_assoc] using h3
    · simpa [Nat.add_assoc] using hf 0 (by omega)
    · simpa [Nat.add_assoc] using hf 1 (by omega)
    · simpa [Nat.add_assoc] using hf 2 (by omega)
    · simpa [Nat.add_assoc] using hf 3 (by omega)
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
          else vs (dst+7)-vs (dst+16)) == 0) then 1 else 4) := by
    cases hz : ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
      else vs (dst+7)-vs (dst+16)) == 0) with
    | false =>
      rw [hz] at branchRead
      have step := run_step (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns (by decide) (run_brz_zero (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns branchRead)
      have off : sx (II.f 64) = (64 : Runner.W) := by
        rw [sx_lit (by decide : lit32 64 = true)]; rfl
      rw [off] at step
      have rest := bp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      refine ⟨normalRest,?_,?_,?_⟩
      · simpa [hz, BitVec.add_assoc] using
          (wholeRun.trans (signedRun.trans (zeroRun.trans testRun))).trans (Star.one step)
      · simpa [hz, BitVec.add_assoc] using rest
      · simp [branchEq, hz]
    | true =>
      rw [hz] at branchRead
      have step := run_step (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns (by decide)
        (run_brz_ne (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) (v := 1) branchIns branchRead (by decide))
      have short : Pre L tested _ fp K (dst+7)
          ([ci 19 (dst+9) 64 0] ++
            ([ci 5 (dst+3) (dst+3) (dst+4), ci 1 (dst+7) 0 0,endJump] ++ normalRest))
          ρ W reserved := bp
      have rest := short.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      refine ⟨[ci 5 (dst+3) (dst+3) (dst+4), ci 1 (dst+7) 0 0,endJump] ++ normalRest,?_,?_,?_⟩
      · simpa [hz, nxt, BitVec.add_assoc] using
          (wholeRun.trans (signedRun.trans (zeroRun.trans testRun))).trans (Star.one step)
      · simpa [hz, BitVec.add_assoc] using rest
      · simp [branchEq, hz]
  refine ⟨executed,tail,aligned.1,continuation,aligned.2,values,final,hfull,
    tailEq,ha,run.trans (sortRun.trans alignRun),
    ag.trans ((sortAgree.mono (by omega)).trans (alignAgree.mono (by omega))),
    fieldValues,?_,?_,finalPre,signedOut,vs (dst+3),vs (dst+4),vs (dst+7),vs (dst+16),
    vreads _ (by omega),vreads _ (by omega),vreads _ (by omega),vreads _ (by omega),
    wholeRun.trans signedRun,wholeAgree.trans (signedAgree.mono (by omega)),
    signedRead,?_,signedTail,signedEq,signedRest,normalization,normalizationEq,
    tested,?_,?_,testRead,?_,?_,?_,branchDone⟩
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


  · intro bounds
    have hfield (i : Nat) (hi : i < 4) :
        values (dst+5+i) = finiteAddRemainingValue F wa wb i := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fieldValues (i+4) (by omega)
    have h5 := hfield 0 (by omega)
    have h6 := hfield 1 (by omega)
    have h7 := hfield 2 (by omega)
    have h8 := hfield 3 (by omega)
    simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h5 h6 h7 h8
    have b0 := bounds 0 (by omega)
    have b1 := bounds 1 (by omega)
    have b2 := bounds 2 (by omega)
    have b3 := bounds 3 (by omega)
    simp only [Nat.reduceLT, ↓reduceIte] at b0 b1 b2 b3
    have orderedBounds (i : Nat) (hi : i = dst+5 ∨ i = dst+6 ∨ i = dst+7 ∨ i = dst+8) :
        if i < dst+7 then 1 ≤ (vs i).toNat ∧ (vs i).toNat < F.bexpMax
        else (vs i).toNat < 2^56 := by
      have rd := (keep i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).trans
        (sorted i (by rcases hi with rfl | rfl | rfl | rfl <;> omega))
      have eq := Option.some.inj ((vreads i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).symm.trans rd)
      rw [eq]
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [h5,h6,h7,h8] <;> split <;> assumption
    have bx := orderedBounds (dst+5) (by omega)
    have byy := orderedBounds (dst+6) (by omega)
    have bq := orderedBounds (dst+7) (by omega)
    have br := orderedBounds (dst+8) (by omega)
    simp only [show dst+5 < dst+7 by omega, show dst+6 < dst+7 by omega,
      show ¬dst+8 < dst+7 by omega, Nat.lt_irrefl, ↓reduceIte] at bx byy bq br
    have req : vs (dst+8) = r := Option.some.inj
      ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rr))
    have jeq : vs (dst+16) = floatShiftJamWord r (ex-ey) :=
      Option.some.inj ((vreads _ (by omega)).symm.trans jammed)
    have bj : (vs (dst+16)).toNat < 2^56 := by
      rw [jeq, floatShiftJamWord, BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight]
        exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (req ▸ br)
      · unfold Runner.IR.bool
        split <;> decide
    have iq : (vs (dst+7)).toInt = ((vs (dst+7)).toNat : Int) :=
      BitVec.toInt_eq_toNat_of_lt (by omega)
    have ij : (vs (dst+16)).toInt = ((vs (dst+16)).toNat : Int) :=
      BitVec.toInt_eq_toNat_of_lt (by omega)
    have resultBounds :
        -2^57 < (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt ∧
        (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt < 2^57 := by
      split
      · rw [BitVec.toInt_add, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      · rw [BitVec.toInt_sub, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
        omega
    have exactResult :
        (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt =
        (if vs (dst+3) == vs (dst+4) then
          ((vs (dst+7)).toNat : Int)+(vs (dst+16)).toNat else
          ((vs (dst+7)).toNat : Int)-(vs (dst+16)).toNat) := by
      split
      · rw [BitVec.toInt_add, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
      · rw [BitVec.toInt_sub, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
    -- Equal signs and equal exponents use only the retained word bounds.
    -- Canonical decoded inputs below also discharge unequal-exponent subtraction.
    have positiveResult : (vs (dst+3) = vs (dst+4) ∨ vs (dst+5) = vs (dst+6)) →
        (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)) ≠ 0 →
        0 < (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt := by
      intro cases nonzero
      have nz : (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt ≠ 0 := by
        simpa [← BitVec.toInt_inj] using nonzero
      rw [exactResult] at nz ⊢
      rcases cases with same | equal
      · simp only [same, beq_self_eq_true, ↓reduceIte] at nz ⊢
        omega
      · have eqx : vs (dst+5) = ex := Option.some.inj
          ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rx))
        have eqy : vs (dst+6) = ey := Option.some.inj
          ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans ry))
        have eqq : vs (dst+7) = q := Option.some.inj
          ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rq))
        have ee : ex = ey := eqx.symm.trans (equal.trans eqy)
        have jr : vs (dst+16) = r := by
          rw [jeq, ee]
          simp [floatShiftJamWord, Runner.IR.bool]
        have order := dominance.2 ee.symm
        have ir : r.toInt = (r.toNat : Int) :=
          BitVec.toInt_eq_toNat_of_lt (by rw [← req]; omega)
        rw [← eqq, iq, ir] at order
        rw [jr] at nz ⊢
        by_cases hs : vs (dst+3) = vs (dst+4) <;>
          simp [hs] at nz ⊢ <;> omega
    have canonicalPositive : ∀ (x y : Gleitkomma.GBits F), F.dicht →
        F.ebits + F.fracBits + 1 ≤ 64 → F.fracBits ≤ 52 → 1 < F.bexpMax →
        Gleitkomma.wf F x → Gleitkomma.wf F y →
        x.bexp ≠ F.bexpMax → y.bexp ≠ F.bexpMax →
        wa = BitVec.ofNat 64 (Gleitkomma.zuBits F x) →
        wb = BitVec.ofNat 64 (Gleitkomma.zuBits F y) →
        (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)) ≠ 0 →
        0 < (if vs (dst+3) == vs (dst+4) then
          vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt := by
      intro x y dense wide precision expmax hx hy fx fy ax ay nz
      by_cases same : vs (dst+3) = vs (dst+4)
      · exact positiveResult (Or.inl same) nz
      by_cases equal : vs (dst+5) = vs (dst+6)
      · exact positiveResult (Or.inr equal) nz
      have eqx : vs (dst+5) = ex := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rx))
      have eqy : vs (dst+6) = ey := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans ry))
      have eqq : vs (dst+7) = q := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rq))
      have expcap : F.bexpMax < 2^63 := by
        have cap := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat))
          (show F.ebits ≤ 63 by omega)
        have hd := dense
        unfold Gleitkomma.Format.dicht at hd
        omega
      have order : (vs (dst+6)).toNat < (vs (dst+5)).toNat := by
        have ix : ex.toInt = (ex.toNat : Int) :=
          BitVec.toInt_eq_toNat_of_lt (by rw [← eqx]; omega)
        have iy : ey.toInt = (ey.toNat : Int) :=
          BitVec.toInt_eq_toNat_of_lt (by rw [← eqy]; omega)
        have ne : (vs (dst+5)).toNat ≠ (vs (dst+6)).toNat := by
          intro h
          exact equal (BitVec.eq_of_toNat_eq h)
        have dom := dominance.1
        rw [ix,iy,← eqx,← eqy] at dom
        omega
      have selected (i : Nat) (hi : i = dst+5 ∨ i = dst+6 ∨ i = dst+7 ∨ i = dst+8) :=
        Option.some.inj ((vreads i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).symm.trans
          ((keep i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).trans
            (sorted i (by rcases hi with rfl | rfl | rfl | rfl <;> omega))))
      have s5 := selected (dst+5) (by omega)
      have s6 := selected (dst+6) (by omega)
      have s7 := selected (dst+7) (by omega)
      have s8 := selected (dst+8) (by omega)
      have jamEq : vs (dst+16) =
          floatShiftJamWord (vs (dst+8)) (vs (dst+5)-vs (dst+6)) := by
        rw [jeq,req,eqx,eqy]
      simp only [same, beq_iff_eq, ↓reduceIte]
      rw [jamEq]
      by_cases swap : ((values (dst+5)).slt (values (dst+6)) ||
        ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8)))) = true
      · simp only [swap, ↓reduceIte] at s5 s6 s7 s8
        simp [h5,h6,h7,h8] at s5 s6 s7 s8
        rw [s5,s6] at order
        rw [s5,s6,s7,s8]
        simpa [finiteAddRemainingValue,ax,ay] using
          (finiteAddRemainingValue_unequal_positive F dense wide precision expmax
            y x hy hx fy fx (by simpa [finiteAddRemainingValue,ax,ay] using order))
      · simp only [swap, ↓reduceIte] at s5 s6 s7 s8
        simp [h5,h6,h7,h8] at s5 s6 s7 s8
        rw [s5,s6] at order
        rw [s5,s6,s7,s8]
        simpa [ax,ay] using (finiteAddRemainingValue_unequal_positive F dense wide precision expmax
          x y hx hy fx fy (by simpa [ax,ay] using order))
    refine ⟨vs (dst+5),vs (dst+6),?_,?_,bx.1,bx.2,byy.1,byy.2,bq,bj,
      resultBounds.1,resultBounds.2,positiveResult,canonicalPositive, r, (keep _ (by omega)).trans rr, ?_⟩
    · exact slotRead_agree finalPre.frame signedAgree (by omega) (by omega)
        (vreads _ (by omega))
    · exact slotRead_agree finalPre.frame signedAgree (by omega) (by omega)
        (vreads _ (by omega))
    · dsimp only
      let den : Int := (2^(vs (dst+5)-vs (dst+6)).toNat : Nat)
      let n : Int := if vs (dst+3) == vs (dst+4) then
        ((vs (dst+7)).toNat : Int)*den + r.toNat else
        ((vs (dst+7)).toNat : Int)*den - r.toNat
      have hd : 0 < den := by
        dsimp only [den]
        exact_mod_cast (Nat.pow_pos (n := (vs (dst+5)-vs (dst+6)).toNat)
          (by decide : 0 < 2))
      have remBounds : 0 ≤ n%den ∧ n%den < den :=
        ⟨Int.emod_nonneg _ (ne_of_gt hd), Int.emod_lt_of_pos _ hd⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [exactResult]
        split <;> ring
      · have h := floatSumMagnitude_reconstruct (n/den) (n%den) den hd remBounds
        have eq : n/den*den+n%den = n := by
          simpa [Int.mul_comm] using Int.mul_ediv_add_emod n den
        simpa only [eq] using h
      · have h := floatSumSign_exact (n/den) (n%den) den hd remBounds
        have eq : n/den*den+n%den = n := by
          simpa [Int.mul_comm] using Int.mul_ediv_add_emod n den
        simpa only [eq] using h
      · constructor
        · intro h
          simp only [h, Int.zero_ediv, Int.zero_emod, and_self]
        · rintro ⟨hq, hr⟩
          have h := Int.mul_ediv_add_emod n den
          rw [hq, hr] at h
          change n = 0
          simpa only [Int.mul_zero, Int.zero_add] using h.symm

  · simpa [BitVec.add_assoc] using
      wholeRun.trans (signedRun.trans (zeroRun.trans testRun))
  · exact wholeAgree.trans ((signedAgree.trans
      ((zeroAgree.mono (by omega)).trans (testAgree.mono (by omega)))).mono (by omega))
  · simpa [BitVec.add_assoc] using testedPre
  · exact (zeroAgree.mono (by omega : dst+9 ≤ dst+10)).trans testAgree
  · exact slotRead_agree cmpPre.frame testAgree (by omega) (by omega) qr

#print axioms floatFiniteAddL_read_fields_align

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
                  (if ((if sx == sy then q+jam else q-jam) == 0) then 1 else 4) := by
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

#print axioms floatFiniteAddL_left_body_exact

/-- Nonzero magnitude, positive exponent and a negative exact correction
    jointly exercise the actual body and its reconstruction equation. -/
theorem floatFiniteAddL_left_body_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (tail : List II) (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    (∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 26 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 3 ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved) ∧
    (205 : Int)*2 = 26*16 + 2*(-3) := by
  constructor
  · simpa using floatFiniteAddL_left_body tail room rq re pre
  · decide

#print axioms floatFiniteAddL_left_body_zeuge

/-- Exact reconstruction at the actual left-loop head. The signed jam
    correction scales with the emitted doubling; the exponent records that scale. -/
structure FiniteLeftInvariant (numerator den correction initialExponent : Int)
    (steps : Nat) (q ex : Int) : Prop where
  positive : 0 < q
  bounded : q < 2^57
  exponent : 1 ≤ ex
  exponentBound : ex < 2^63
  scale : ex + steps = initialExponent
  exactValue : numerator * 2^steps = q*den + correction * 2^steps

/-- Preservation uses the actual body arithmetic, including its correction.
    The left condition supplies the tighter bound before doubling. -/
theorem FiniteLeftInvariant.step
    {n d c e q ex : Int} {steps : Nat}
    (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex) :
    FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  constructor
  · refine ⟨by have := inv.positive; omega, by omega, by omega,
      by have := inv.exponentBound; omega, ?_, ?_⟩
    · push_cast
      have := inv.scale
      omega
    · rw [pow_succ]
      have h := congrArg (fun x : Int => x*2) inv.exactValue
      nlinarith
  · omega

/-- One reached Runner state carries execution, frame, both updated reads,
    exact reconstruction and the decreasing loop measure together. This is
    the literal left body, without asserting execution of its back edge. -/
theorem floatFiniteAddL_left_body_invariant {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved steps : Nat} {n d c e q ex : Int} (tail : List II)
    (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 q))
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 ex))
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 (2*q)) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 (ex-1)) ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved ∧
      FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  obtain ⟨out,run,agree,readQ,readE,next⟩ :=
    floatFiniteAddL_left_body tail room rq re pre
  have arithmetic := floatFiniteAddL_left_body_exact q ex d 0 (q*d)
    (by have := inv.positive; omega) guard running inv.exponentBound (by ring)
  have eqQ : BitVec.ofInt 64 q * 2 = BitVec.ofInt 64 (2*q) := by
    rw [← arithmetic.1, BitVec.ofInt_toInt]
  have eqE : BitVec.ofInt 64 ex - 1 = BitVec.ofInt 64 (ex-1) := by
    rw [← arithmetic.2.1, BitVec.ofInt_toInt]
  rw [eqQ] at readQ
  rw [eqE] at readE
  exact ⟨out,run,agree,readQ,readE,next,inv.step guard running⟩

/-- A negative jam correction and a nonzero mantissa satisfy all invariant
    fields jointly, and remain so after an actual body's arithmetic. -/
theorem finiteLeftInvariant_zeuge :
    FiniteLeftInvariant 205 16 (-3) 4 0 13 4 ∧
    FiniteLeftInvariant 205 16 (-3) 4 1 26 3 ∧
    (3 : Int).toNat < (4 : Int).toNat := by
  have initial : FiniteLeftInvariant 205 16 (-3) 4 0 13 4 := by
    constructor <;> norm_num
  exact ⟨initial, initial.step (by norm_num) (by norm_num)⟩

#print axioms FiniteLeftInvariant.step
#print axioms floatFiniteAddL_left_body_invariant
#print axioms finiteLeftInvariant_zeuge

/-- The execution witness shares its reads, frame and exact invariant;
    the correction is negative and the significand is nonzero. -/
theorem floatFiniteAddL_left_body_invariant_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (tail : List II) (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 26 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 3 ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved ∧
      FiniteLeftInvariant 205 16 (-3) 4 1 26 3 ∧
      (3 : Int).toNat < (4 : Int).toNat := by
  exact floatFiniteAddL_left_body_invariant tail finiteLeftInvariant_zeuge.1
    (by norm_num) (by norm_num) room rq re pre

#print axioms floatFiniteAddL_left_body_invariant_zeuge

/-- Initialize the scaled invariant from the retained exact ADD/SUB equation.
    Positivity is deliberately explicit: NONZERO alone does not imply it. -/
theorem FiniteLeftInvariant.of_retained
    {n d c q ex : Int} (positive : 0 < q) (bound : q < 2^57)
    (exponent : 1 ≤ ex) (exponentBound : ex < 2^63)
    (exactValue : n = q*d+c) :
    FiniteLeftInvariant n d c ex 0 q ex := by
  refine ⟨positive,bound,exponent,exponentBound,by simp,?_⟩
  simpa using exactValue

/-- The actual BRZ after the left condition enters the literal body on a
    nonzero flag. Execution of the condition itself is a separate obligation. -/
theorem floatFiniteAddL_left_test_enter {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (body tail : List II)
    (room : dst+9 < K)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some 1)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 19 (dst+9) 96 0] ++ body ++ tail) ρ W reserved) :
    Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m ∧
    Pre L m (pc+16) fp K (dst+5) (body++tail) ρ W reserved := by
  have hp : Pre L m pc fp K (dst+5)
      ([ci 19 (dst+9) 96 0] ++ (body++tail)) ρ W reserved := by
    simpa only [List.append_assoc] using pre
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int))
      (II.f 96) (II.f 0) := by
    simpa [ci] using hp.code 0 (by simp)
  have rd : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some 1 := by
    rw [sx_nat (by have := hp.small; omega)]
    exact flag
  constructor
  · exact Star.one (by simpa [nxt] using
      (run_step (t := ⟨pc,fp⟩) ins (by decide)
        (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins rd (by decide))))
  · simpa using hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)

/-- Connect the literal left body to its actual backedge. The offset is
    determined by the condition length, as in floatFiniteAddL. -/
theorem floatFiniteAddL_left_body_backedge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {head fp : Runner.W}
    {K dst reserved steps conditionLength : Nat} {n d c e q ex : Int}
    (tail : List II) (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex)
    (offsetRange : lit32 (-(16*((conditionLength+5 : Nat) : Int))) = true)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 q))
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 ex))
    (pre : Pre L m (head+BitVec.ofNat 64 (16*(conditionLength+1))) fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++
       [ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨head+BitVec.ofNat 64 (16*(conditionLength+1)),fp⟩ m ⟨head,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 (2*q)) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 (ex-1)) ∧
      FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  obtain ⟨out,run,agree,readQ,readE,next,updated,decreasing⟩ :=
    floatFiniteAddL_left_body_invariant
      ([ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail)
      inv guard running room rq re (by simpa only [List.append_assoc] using pre)
  have ins := next.code 0 (by simp)
  simp only [List.getElem_append_left (by simp : 0 < [ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0].length),
    List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  simp only [ci] at ins
  have jump := run_step (t := ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) ins (by decide) (run_jmp (t := ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) ins)
  have off : sx (II.f (-(16*((conditionLength+5 : Nat) : Int)))) =
      -BitVec.ofNat 64 (16*(conditionLength+5)) := by
    rw [sx_lit offsetRange, BitVec.ofInt_neg]
    congr 1
  have pcEq : head+BitVec.ofNat 64 (16*(conditionLength+1))+64 =
      head+BitVec.ofNat 64 (16*(conditionLength+5)) := by
    change head+BitVec.ofNat 64 (16*(conditionLength+1))+BitVec.ofNat 64 64 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2 <;> omega
  have finish : Star ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩ out
      ⟨head,fp⟩ out := by
    apply Star.one
    change Run (step ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) out
      ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64+sx (II.f (-(16*((conditionLength+5 : Nat) : Int)))),fp⟩ out at jump
    rw [off,pcEq] at jump
    simpa only [pcEq,← BitVec.sub_eq_add_neg,BitVec.add_sub_cancel] using jump
  exact ⟨out,run.trans finish,agree,readQ,readE,updated,decreasing⟩

#print axioms FiniteLeftInvariant.of_retained
#print axioms floatFiniteAddL_left_test_enter
#print axioms floatFiniteAddL_left_body_backedge

/-- Execute all nine scalar instructions of the actual left test after its
    threshold constant. The retained significand and exponent share the run. -/
theorem floatFiniteAddL_left_condition_scalar {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex threshold : Runner.W} (tail : List II)
    (room : dst+11 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (dst+10))) = some threshold)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0,
        ci 13 (dst+11) (dst+10) (dst+5),
        ci 5 (dst+9) (dst+9) (dst+11),
        ci 1 (dst+10) 0 0,
        ci 14 (dst+11) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0,
        ci 4 (dst+11) (dst+10) (dst+11),
        ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+144,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (q.slt threshold) * Runner.IR.bool ((1 : Runner.W).slt ex) *
          (1-Runner.IR.bool (q == 0))) ∧
      Pre L out (pc+144) fp K (dst+9) tail ρ W reserved := by
  have p0 : Pre L m pc fp K (dst+9) ([ci 13 (dst+9) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))))))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+7) (b := dst+10)
    {p0.left with ctx := by have := p0.ctx; omega} (by omega) (by omega) (by omega)
    rq rt (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h1 := p0.next (a1.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd1_7 := slotRead_agree p0.frame a1 (by omega) (by omega) rq
  have rd1_5 := slotRead_agree p0.frame a1 (by omega) (by omega) re
  have p1 : Pre L m1 (pc+16) fp K (dst+9) ([ci 1 (dst+10) 1 0] ++ ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))))))) ρ W reserved := h1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (1 : Runner.W).toNat
  obtain ⟨wr2,r2,a2⟩ := wr_slot p1.frame (by omega : dst+10 < K) (1 : Runner.W)
  have s2 : Star ⟨pc+16,fp⟩ m1 ⟨pc+16+16,fp⟩ m2 := by
    apply star_ins p1.left.code (by simp [ci])
    have ins := p1.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p1.small; omega))
    rw [sd,sx_lit (by decide : lit32 1 = true)]
    exact run_wr64 wr2
  have h2 := p1.next (a2.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd2_7 := slotRead_agree p1.frame a2 (by omega) (by omega) rd1_7
  have rd2_5 := slotRead_agree p1.frame a2 (by omega) (by omega) rd1_5
  have rd2_9 := slotRead_agree p1.frame a2 (by omega) (by omega) r1
  have p2 : Pre L m2 (pc+16+16) fp K (dst+9) ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))))) ρ W reserved := h2
  obtain ⟨m3,s3,a3,w3,r3,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+10) (b := dst+5)
    {p2.left with ctx := by have := p2.ctx; omega} (by omega) (by omega) (by omega)
    r2 rd2_5 (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h3 := p2.next (a3.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd3_7 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_7
  have rd3_5 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_5
  have rd3_9 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_9
  have rd3_10 := slotRead_agree p2.frame a3 (by omega) (by omega) r2
  have p3 : Pre L m3 (pc+16+16+16) fp K (dst+9) ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))))) ρ W reserved := h3
  obtain ⟨m4,s4,a4,w4,r4,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+9) (b := dst+11)
    {p3.left with ctx := by have := p3.ctx; omega} (by omega) (by omega) (by omega)
    rd3_9 r3 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h4 := p3.next (a4.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd4_7 := slotRead_agree p3.frame a4 (by omega) (by omega) rd3_7
  have rd4_5 := slotRead_agree p3.frame a4 (by omega) (by omega) rd3_5
  have p4 : Pre L m4 (pc+16+16+16+16) fp K (dst+9) ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))) ρ W reserved := h4
  let m5 := write m4 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (0 : Runner.W).toNat
  obtain ⟨wr5,r5,a5⟩ := wr_slot p4.frame (by omega : dst+10 < K) (0 : Runner.W)
  have s5 : Star ⟨pc+16+16+16+16,fp⟩ m4 ⟨pc+16+16+16+16+16,fp⟩ m5 := by
    apply star_ins p4.left.code (by simp [ci])
    have ins := p4.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16+16+16+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16+16+16+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p4.small; omega))
    rw [sd,sx_lit (by decide : lit32 0 = true)]
    exact run_wr64 wr5
  have h5 := p4.next (a5.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd5_7 := slotRead_agree p4.frame a5 (by omega) (by omega) rd4_7
  have rd5_5 := slotRead_agree p4.frame a5 (by omega) (by omega) rd4_5
  have rd5_9 := slotRead_agree p4.frame a5 (by omega) (by omega) r4
  have p5 : Pre L m5 (pc+16+16+16+16+16) fp K (dst+9) ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))) ρ W reserved := h5
  obtain ⟨m6,s6,a6,w6,r6,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+7) (b := dst+10)
    {p5.left with ctx := by have := p5.ctx; omega} (by omega) (by omega) (by omega)
    rd5_7 r5 (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  have h6 := p5.next (a6.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd6_7 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_7
  have rd6_5 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_5
  have rd6_9 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_9
  have rd6_10 := slotRead_agree p5.frame a6 (by omega) (by omega) r5
  have p6 : Pre L m6 (pc+16+16+16+16+16+16) fp K (dst+9) ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))) ρ W reserved := h6
  let m7 := write m6 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (1 : Runner.W).toNat
  obtain ⟨wr7,r7,a7⟩ := wr_slot p6.frame (by omega : dst+10 < K) (1 : Runner.W)
  have s7 : Star ⟨pc+16+16+16+16+16+16,fp⟩ m6 ⟨pc+16+16+16+16+16+16+16,fp⟩ m7 := by
    apply star_ins p6.left.code (by simp [ci])
    have ins := p6.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16+16+16+16+16+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16+16+16+16+16+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p6.small; omega))
    rw [sd,sx_lit (by decide : lit32 1 = true)]
    exact run_wr64 wr7
  have h7 := p6.next (a7.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd7_7 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_7
  have rd7_5 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_5
  have rd7_9 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_9
  have rd7_11 : m7.rd64 (slot fp (BitVec.ofNat 64 (dst+11))) = some (Runner.IR.bool (q == 0)) := by
    change (write _ _ 8 _).rd64 _ = _
    rw [rd64_write_far]
    · exact r6
    · unfold Far
      rw [slot_toNat p6.frame.room (by omega : dst+10 < K),slot_toNat p6.frame.room (by omega : dst+11 < K)]
      have := p6.frame.lt
      omega
  have p7 : Pre L m7 (pc+16+16+16+16+16+16+16) fp K (dst+9) ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)) ρ W reserved := h7
  obtain ⟨m8,s8,a8,w8,r8,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+10) (b := dst+11)
    {p7.left with ctx := by have := p7.ctx; omega} (by omega) (by omega) (by omega)
    r7 rd7_11 (g := fun x y => some (x-y)) rfl (by decide) rfl
  have h8 := p7.next (a8.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd8_7 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_7
  have rd8_5 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_5
  have rd8_9 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_9
  have rd8_10 := slotRead_agree p7.frame a8 (by omega) (by omega) r7
  have p8 : Pre L m8 (pc+16+16+16+16+16+16+16+16) fp K (dst+9) ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved := h8
  obtain ⟨m9,s9,a9,w9,r9,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+9) (b := dst+11)
    {p8.left with ctx := by have := p8.ctx; omega} (by omega) (by omega) (by omega)
    rd8_9 r8 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h9 := p8.next (a9.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd9_7 := slotRead_agree p8.frame a9 (by omega) (by omega) rd8_7
  have rd9_5 := slotRead_agree p8.frame a9 (by omega) (by omega) rd8_5
  refine ⟨m9,?_,?_,rd9_7,rd9_5,?_,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans (s9))))))))
  · exact (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans ((a5.mono (by omega)).trans ((a6.mono (by omega)).trans ((a7.mono (by omega)).trans ((a8.mono (by omega)).trans ((a9.mono (by omega))))))))))
  · simpa using r9
  · simpa [BitVec.add_assoc] using h9

#print axioms floatFiniteAddL_left_condition_scalar

/-- Run the actual threshold constant followed by the scalar left condition.
    The returned flag and retained words refer to the same final memory. -/
theorem floatFiniteAddL_left_condition {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex : Runner.W} (F : Gleitkomma.Format)
    (tail : List II) (thresholdRange : 2^(F.fracBits+3) < 65536^4)
    (room : dst+12 ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (pre : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+3)) (dst+10)).1 ++
        [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 13 (dst+11) (dst+10) (dst+5), ci 5 (dst+9) (dst+9) (dst+11),
          ci 1 (dst+10) 0 0, ci 14 (dst+11) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+11) (dst+10) (dst+11),
          ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+3)) (dst+10)).1.length)+144,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (q.slt (BitVec.ofNat 64 (2^(F.fracBits+3)))) *
          Runner.IR.bool ((1 : Runner.W).slt ex) * (1-Runner.IR.bool (q == 0))) ∧
      Pre L out
        (pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+3)) (dst+10)).1.length)+144)
        fp K (dst+9) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+3)) (dst+10)).1 ++
        ([ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 13 (dst+11) (dst+10) (dst+5), ci 5 (dst+9) (dst+9) (dst+11),
          ci 1 (dst+10) 0 0, ci 14 (dst+11) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+11) (dst+10) (dst+11),
          ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)) ρ W reserved := by
    simpa only [List.append_assoc] using pre
  obtain ⟨m1,run,agree,w,rd,rfl⟩ := konstWL_ok 4 (2^(F.fracBits+3)) thresholdRange
    (by omega) {hp.left with ctx := by have := hp.ctx; omega}
  have rest := hp.next (agree.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  obtain ⟨out,run2,agree2,rq2,re2,flag,done⟩ := floatFiniteAddL_left_condition_scalar tail
    (by omega) (slotRead_agree hp.frame agree (by omega) (by omega) rq)
    (slotRead_agree hp.frame agree (by omega) (by omega) re) rd rest
  exact ⟨out,run.trans run2,(agree.mono (by omega)).trans agree2,rq2,re2,flag,done⟩

#print axioms floatFiniteAddL_left_condition

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

end Gabbro.Stage0.Senke
