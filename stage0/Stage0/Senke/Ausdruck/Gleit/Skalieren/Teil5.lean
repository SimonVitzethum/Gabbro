module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil5a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil4

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Connected execution through the emitted zero constant and signed comparison. -/
theorem floatOfIntContinuationL_magnitude_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 144, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) =
        some (floatMagnitudeWord v) := by
  obtain ⟨m1, s1, a1, r1, r2, r3, r4, r5⟩ :=
    floatOfIntContinuationL_fourth_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_nine F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0]) h a1
    (show input + 1 ≤ input + 5 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, rz, hw⟩ := const_ok hp.left (by decide) hk
  subst w
  have hv := slotRead_agree hp.frame a2 (by omega) (by omega) r5
  have hp4 := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0]) h
    (a1.trans (a2.mono (by omega))) (show input + 1 ≤ input + 4 by omega) (by omega)
  obtain ⟨m3, s3, a3, w, rw, hw⟩ := floatMagnitude_sign_instruction (Pre.left (a := [ci 13 (input + 4) (input + 4) (input + 5)]) hp4) (by omega) hv rz
  subst w
  have ag := (a1.trans (a2.mono (by omega))).trans (a3.mono (by omega))
  have rt := slotRead_agree hp.frame a2 (by omega) (by omega) r4
  have rt' := slotRead_agree hp4.frame a3 (by omega) (by omega) rt
  have hp5 := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5)]) h ag
    (show input + 1 ≤ input + 3 by omega) (by omega)
  obtain ⟨m4, s4, a4, w, rw4, hw4⟩ := eng_bin_ok hp5.left
    (by omega) (by omega) (by omega) rt' rw
    (g := fun x y => some (x * y)) rfl (by decide) rfl
  subst w
  have ag4 := ag.trans (a4.mono (by omega))
  have one2 := slotRead_agree hp.frame a2 (by omega) (by omega) r3
  have one3 := slotRead_agree hp4.frame a3 (by omega) (by omega) one2
  have one4 := slotRead_agree hp5.frame a4 (by omega) (by omega) one3
  have hp6 := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4)]) h ag4
    (show input + 1 ≤ input + 2 by omega) (by omega)
  obtain ⟨m5, s5, a5, w, rw5, hw5⟩ := eng_bin_ok hp6.left
    (by omega) (by omega) (by omega) one4 rw4
    (g := fun x y => some (x - y)) rfl (by decide) rfl
  subst w
  have ag5 := ag4.trans (a5.mono (by omega))
  have input2 := slotRead_agree hp.frame a2 (by omega) (by omega) r2
  have input3 := slotRead_agree hp4.frame a3 (by omega) (by omega) input2
  have input4 := slotRead_agree hp5.frame a4 (by omega) (by omega) input3
  have input5 := slotRead_agree hp6.frame a5 (by omega) (by omega) input4
  have hp7 := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3)]) h ag5
    (show input + 1 ≤ input + 1 by omega) (by omega)
  obtain ⟨m6, s6, a6, w, rw6, hw6⟩ := eng_bin_ok hp7.left
    (by omega) (by omega) (by omega) input5 rw5
    (g := fun x y => some (x * y)) rfl (by decide) rfl
  subst w
  refine ⟨m6, ?_, ag5.trans a6, rw6⟩
  simp only [List.length_cons, List.length_nil] at s2 s3 s4 s5
  have s12 := s1.trans s2
  simp only [BitVec.add_assoc] at s12 s3 s4
  have s123 := s12.trans s3
  have ss := s123.trans s4
  have ss5 := ss.trans s5
  simp only [List.length_cons, List.length_nil] at s6
  have ss5' : Star ⟨pc, fp⟩ m ⟨pc + 128, fp⟩ m5 := by
    simpa [BitVec.add_assoc] using ss5
  have ss6 := ss5'.trans s6
  simpa [BitVec.add_assoc] using ss6

/-- Actual connected execution computes the unsigned absolute value, including zero
    and the minimum signed input. -/
theorem floatOfIntContinuationL_magnitude_model (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} (z : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63)
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 z)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 144, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) =
        some (BitVec.ofNat 64 z.natAbs) := by
  obtain ⟨m', hs, ha, hr'⟩ := floatOfIntContinuationL_magnitude_step F hc h hk hr
  rw [floatMagnitudeWord_model z hz] at hr'
  exact ⟨m', hs, ha, hr'⟩

theorem floatOfIntContinuationL_first_ten (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: ci 5 (input + 1) (input + 1) (input + 2) :: ci 1 (input + 2) 0 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
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
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

/-- Execute the actual zero operand load immediately after magnitude production. -/
theorem floatOfIntContinuationL_zero_operand (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63)
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 z)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 160, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some (BitVec.ofNat 64 z.natAbs) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 2))) = some 0 := by
  obtain ⟨m1, s1, a1, r1⟩ := floatOfIntContinuationL_magnitude_model F z hz hc h hk hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_ten F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3),
    ci 5 (input + 1) (input + 1) (input + 2)]) h a1
    (show input + 1 ≤ input + 2 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, r2, hw⟩ := const_ok hp.left (by decide) (by omega)
  subst w
  refine ⟨m2, ?_, a1.trans (a2.mono (by omega)),
    slotRead_agree hp.frame a2 (by omega) (by omega) r1, r2⟩
  have ss := s1.trans s2
  simpa [BitVec.add_assoc] using ss

theorem floatOfIntContinuationL_first_eleven (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: ci 5 (input + 1) (input + 1) (input + 2) :: ci 1 (input + 2) 0 0 :: ci 14 (input + 1) (input + 1) (input + 2) :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
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
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

theorem floatOfIntContinuationL_first_branch (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ jump tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: ci 5 (input + 1) (input + 1) (input + 2) :: ci 1 (input + 2) 0 0 :: ci 14 (input + 1) (input + 1) (input + 2) :: ci 19 (input + 1) jump 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
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
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, _, rfl⟩
  · cases he

end Gabbro.Stage0.Senke
