/- Executed slot initialization, retaining each earlier result across temporaries. -/
import Stage0.Senke.Ausdruck.Arithmetik.Simulation

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

end Gabbro.Stage0.Senke
