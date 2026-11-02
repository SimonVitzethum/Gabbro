module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil4a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_two (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := hb'
  cases hx
  cases hxy
  cases hab'
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

/-- Connected execution through the actual constant-one instruction at entry + 16. -/
theorem floatOfIntContinuationL_second_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 2 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 32, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 input)) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 2))) = some 1 := by
  obtain ⟨m1, s1, a1, r1, r2⟩ :=
    floatOfIntContinuationL_first_step_retained F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_two F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0]) h a1
    (show input + 1 ≤ input + 2 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, rw2, hw⟩ := const_ok hp.left (by decide) hk
  subst w
  refine ⟨m2, ?_, a1.trans (a2.mono (by omega)), ?_, ?_, rw2⟩
  · have ss := s1.trans s2
    simpa [BitVec.add_assoc] using ss
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r1
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r2

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_three (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  obtain ⟨x, hx, y, hy, hxy⟩ := hb'
  obtain ⟨u, hu, z, hz, huz⟩ := hy
  cases hu
  cases huz
  cases hx
  cases hxy
  cases hab'
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

/-- Execute the next actual magnitude constant, preserving both input reads. -/
theorem floatOfIntContinuationL_third_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 3 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 48, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 input)) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 2))) = some 1 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 3))) = some 2 := by
  obtain ⟨m1, s1, a1, r1, r2, r3⟩ :=
    floatOfIntContinuationL_second_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_three F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0]) h a1
    (show input + 1 ≤ input + 3 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, rw2, hw⟩ := const_ok hp.left (by decide) hk
  subst w
  refine ⟨m2, ?_, a1.trans (a2.mono (by omega)), ?_, ?_, ?_, rw2⟩
  · have ss := s1.trans s2
    simpa [BitVec.add_assoc] using ss
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r1
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r2
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r3

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_four (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: tail := by
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
  cases hq
  cases hqr
  cases hu
  cases huz
  cases hx
  cases hxy
  cases hab'
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_six (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: tail := by
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
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_seven (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: tail := by
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
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_eight (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: tail := by
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
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

end Gabbro.Stage0.Senke
