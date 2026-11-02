module

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil4

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxRecDepth 4096 in
theorem floatOfIntContinuationL_first_nine (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: ci 1 (input + 2) 1 0 :: ci 1 (input + 3) 2 0 :: ci 2 (input + 4) input 0 :: ci 1 (input + 5) 0 0 :: ci 13 (input + 4) (input + 4) (input + 5) :: ci 5 (input + 3) (input + 3) (input + 4) :: ci 4 (input + 2) (input + 2) (input + 3) :: ci 5 (input + 1) (input + 1) (input + 2) :: tail := by
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

/-- Execute the next actual magnitude constant, preserving both input reads. -/
theorem floatOfIntContinuationL_fourth_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 4 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 64, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 input)) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 2))) = some 1 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 3))) = some 2 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 4))) = some v := by
  obtain ⟨m1, s1, a1, r1, r2, r3, r4⟩ :=
    floatOfIntContinuationL_third_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_four F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0, ci 1 (input + 3) 2 0]) h a1
    (show input + 1 ≤ input + 4 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, rw2, hw⟩ := mov_ok hp.left (by omega) hk r1
  subst w
  refine ⟨m2, ?_, a1.trans (a2.mono (by omega)), ?_, ?_, ?_, ?_, rw2⟩
  · have ss := s1.trans s2
    simpa [BitVec.add_assoc] using ss
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r1
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r2
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r3
  · exact slotRead_agree hp.frame a2 (by omega) (by omega) r4


/-- Connected execution through the emitted zero constant and signed comparison. -/
theorem floatOfIntContinuationL_sign_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 96, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 4))) =
        some (Runner.IR.bool (v.slt 0)) := by
  obtain ⟨m1, s1, a1, r1, r2, r3, r4, r5⟩ :=
    floatOfIntContinuationL_fourth_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_six F input hc
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
  refine ⟨m3, ?_, (a1.trans (a2.mono (by omega))).trans (a3.mono (by omega)), rw⟩
  simp only [List.length_cons, List.length_nil] at s2 s3
  have s12 := s1.trans s2
  simp only [BitVec.add_assoc] at s12 s3
  have ss := s12.trans s3
  simpa [BitVec.add_assoc] using ss

/-- Connected execution through the emitted zero constant and signed comparison. -/
theorem floatOfIntContinuationL_twice_sign_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 112, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 3))) =
        some (2 * Runner.IR.bool (v.slt 0)) := by
  obtain ⟨m1, s1, a1, r1, r2, r3, r4, r5⟩ :=
    floatOfIntContinuationL_fourth_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_seven F input hc
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
  refine ⟨m4, ?_, ag.trans (a4.mono (by omega)), rw4⟩
  simp only [List.length_cons, List.length_nil] at s2 s3 s4
  have s12 := s1.trans s2
  simp only [BitVec.add_assoc] at s12 s3 s4
  have s123 := s12.trans s3
  have ss := s123.trans s4
  simpa [BitVec.add_assoc] using ss

/-- Connected execution through the emitted zero constant and signed comparison. -/
theorem floatOfIntContinuationL_factor_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 128, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 2))) =
        some (1 - 2 * Runner.IR.bool (v.slt 0)) := by
  obtain ⟨m1, s1, a1, r1, r2, r3, r4, r5⟩ :=
    floatOfIntContinuationL_fourth_step F hc h (by omega) hr
  obtain ⟨tail, he⟩ := floatOfIntContinuationL_first_eight F input hc
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
  refine ⟨m5, ?_, ag4.trans (a5.mono (by omega)), rw5⟩
  simp only [List.length_cons, List.length_nil] at s2 s3 s4 s5
  have s12 := s1.trans s2
  simp only [BitVec.add_assoc] at s12 s3 s4
  have s123 := s12.trans s3
  have ss := s123.trans s4
  have ss5 := ss.trans s5
  simpa [BitVec.add_assoc] using ss5


end Gabbro.Stage0.Senke
