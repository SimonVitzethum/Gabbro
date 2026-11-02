module

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil5

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatOfIntContinuationL_first_output (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ jump tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: ci 5 (input + 1) (input + 1) (input + 2) :: ci 1 (input + 2) 0 0 :: ci 14 (input + 1) (input + 1) (input + 2) :: ci 19 (input + 1) jump 0 :: ci 1 (input + 1) 0 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, floatPackZeroL, konstWL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, hzero, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := hb'
  obtain ⟨u, hu, z, hz, huz⟩ := hy
  obtain ⟨q, hq, r, hr, hqr⟩ := hz
  cases hr
  cases hq
  cases hqr
  cases hu
  cases huz
  cases hx
  cases hxy
  cases hab'
  cases hb
  cases hab
  cases hzero
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, _, rfl⟩
  · cases he

/-- The end jump and its displacement are recovered from the generated list. -/
theorem floatOfIntContinuationL_zero_jump_encoding (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ normal : List II,
      code[29]? = some (ci 18 ((16 * (normal.length + 1) : Nat) : Int) 0 0) ∧
      code.length = 31 + normal.length ∧
      lit32 ((16 * (normal.length + 1) : Nat) : Int) = true := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, floatPackZeroL, konstWL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, hzero, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := hb'
  obtain ⟨u, hu, z, hz, huz⟩ := hy
  obtain ⟨q, hq, r, hr, hqr⟩ := hz
  cases hr
  cases hq
  cases hqr
  cases hu
  cases huz
  cases hx
  cases hxy
  cases hab'
  cases hb
  cases hab
  cases hzero
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    refine ⟨_, rfl, by simp [bin2]; omega, ?_⟩
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  · cases he

/-- The entire zero constant lies between the comparison branch and the end jump. -/
theorem floatOfIntContinuationL_zero_constant_parts (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ precode tail, code = precode ++ (konstWL 4 0 (input + 1)).1 ++ tail ∧
      precode.length = 12 := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, floatPackZeroL, konstWL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, hzero, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := hb'
  obtain ⟨u, hu, z, hz, huz⟩ := hy
  obtain ⟨q, hq, r, hr, hqr⟩ := hz
  cases hr
  cases hq
  cases hqr
  cases hu
  cases huz
  cases hx
  cases hxy
  cases hab'
  cases hb
  cases hab
  cases hzero
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨[ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3),
    ci 5 (input + 1) (input + 1) (input + 2), ci 1 (input + 2) 0 0,
    ci 14 (input + 1) (input + 1) (input + 2), ci 19 (input + 1) _ 0], _, rfl, rfl⟩
  · cases he


/-- The encoded displacement lands exactly on the canonical final copy. -/
theorem floatOfIntContinuationL_zero_jump_position (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ normal : List II,
      code[29]? = some (ci 18 ((16 * (normal.length + 1) : Nat) : Int) 0 0) ∧
      464 + 16 * (normal.length + 1) = 16 * (code.length - 1) := by
  obtain ⟨normal, hi, hn, _⟩ := floatOfIntContinuationL_zero_jump_encoding F input h
  exact ⟨normal, hi, by omega⟩

/-- Execute the emitted equality from the concrete magnitude and zero reads. -/
theorem floatOfIntContinuationL_zero_comparison (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63)
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 z)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 176, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) =
        some (Runner.IR.bool (BitVec.ofNat 64 z.natAbs == 0)) := by
  obtain ⟨m1, s1, a1, r1, r2⟩ := floatOfIntContinuationL_zero_operand F z hz hc h hk hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_eleven F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3),
    ci 5 (input + 1) (input + 1) (input + 2), ci 1 (input + 2) 0 0]) h a1
    (show input + 1 ≤ input + 1 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, r, hw⟩ := eng_bin_ok hp.left
    (by omega) (by omega) (by omega) r1 r2
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst w
  refine ⟨m2, ?_, a1.trans a2, r⟩
  have ss := s1.trans s2
  simpa [BitVec.add_assoc] using ss

/-- The concrete zero comparison makes the actual branch fall through. -/
theorem floatOfIntContinuationL_zero_fallthrough (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 192, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 1 := by
  obtain ⟨m1, s1, a1, r1⟩ := floatOfIntContinuationL_zero_comparison F 0 (by constructor <;> decide) hc h hk hr
  have r : m1.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 1 := by
    simpa [Runner.IR.bool] using r1
  obtain ⟨jump, tail, he⟩ := floatOfIntContinuationL_first_branch F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3),
    ci 5 (input + 1) (input + 1) (input + 2), ci 1 (input + 2) 0 0,
    ci 14 (input + 1) (input + 1) (input + 2)]) h a1
    (show input + 1 ≤ input + 1 by omega) (by omega)
  have hi := hp.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have sb := star_ins (fp := fp) (m' := m1) (codeAt_left hp.code) (by simp [ci])
    (by
      simp only [ci]
      exact run_brz_ne (t := ⟨_, fp⟩)
        hi
        (by
          change m1.rd64 (slot fp (sx (II.f ((input + 1 : Nat) : Int)))) = some (1 : Runner.W)
          rw [sx_nat (by have := hp.small; omega)]
          exact r) (by decide))
  refine ⟨m1, ?_, a1, r⟩
  simpa [BitVec.add_assoc] using s1.trans sb


end Gabbro.Stage0.Senke
