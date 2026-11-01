module

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Joint minimum-integer, tie, carry and shift-zero fixtures discharge every outer-right premise and execute the
    emitted assembly with the canonical conversion result. -/
theorem floatOfIntAssemblyL_right_ofInt_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ z ∈ ([-9223372036854775808, 9007199254740993, 18014398509481983, 4503599627370496] : List Int),
      F ∈ [Gleitkomma.f32, Gleitkomma.f64] ∧
      (-2^63 ≤ z ∧ z < 2^63) ∧ z ≠ 0 ∧
      ((F.p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1 ∧
      WordCode (L := L) ρ W
        (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)) (BitVec.ofInt 64 z) ∧
      WordCode (L := L) ρ W
        (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d
          (fun j => some (konstWL 4 (BitVec.ofInt 64 z).toNat j)))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  intro F hF z hz
  have bounds : -2^63 ≤ z ∧ z < 2^63 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> decide
  have nonzero : z ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> decide
  have left : ((F.p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hF
    rcases hF with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;> decide +kernel
  have input : WordCode (L := L) ρ W
      (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)) (BitVec.ofInt 64 z) := by
    have h : WordCode (L := L) ρ W
        (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d))
        (BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat) := WordCode.konst (L := L) (ρ := ρ) (W := W)
      (BitVec.ofInt 64 z).toNat (BitVec.isLt _)
    have eq : BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat = BitVec.ofInt 64 z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> decide
    rw [eq] at h
    intro fp K d c top hc ht m pc pre
    exact h hc ht m pc pre
  exact ⟨hF, bounds, nonzero, left, input,
    floatOfIntAssemblyL_right_ofInt F hF z bounds nonzero input left⟩

/-- The emitted conversion is correct for every supported signed input. -/
theorem floatOfIntAssemblyL_ofInt {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z)) :
    WordCode (L := L) ρ W
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d input)
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  by_cases hn : z = 0
  · subst z
    have h : WordCode (L := L) ρ W
        (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d input)
        (BitVec.ofNat 64 0) := floatOfIntAssemblyL_zero hi F.p F.bias (2^(F.ebits + F.fracBits))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · have eq : BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f32 (Gleitkomma.ofInt Gleitkomma.f32 0)) = BitVec.ofNat 64 0 := by decide +kernel
      rw [eq]
      exact h
    · have eq : BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 (Gleitkomma.ofInt Gleitkomma.f64 0)) = BitVec.ofNat 64 0 := by decide +kernel
      rw [eq]
      exact h
  · by_cases hl : Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat)
    · exact floatOfIntAssemblyL_left_ofInt F hF z hz hn hi hl
    · exact floatOfIntAssemblyL_right_ofInt F hF z hz hn hi (by omega)

/-- A constant producer jointly witnesses every supported signed input. -/
theorem floatOfIntAssemblyL_ofInt_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) :
    let input := fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)
    WordCode (L := L) ρ W input (BitVec.ofInt 64 z) ∧
    WordCode (L := L) ρ W
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d input)
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  dsimp only
  have hi : WordCode (L := L) ρ W
      (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)) (BitVec.ofInt 64 z) := by
    have h : WordCode (L := L) ρ W
        (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d))
        (BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat) := WordCode.konst (L := L) (ρ := ρ) (W := W)
      (BitVec.ofInt 64 z).toNat (BitVec.isLt _)
    have eq : BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat = BitVec.ofInt 64 z := by
      exact (BitVec.ofNat_toNat 64 (BitVec.ofInt 64 z)).trans (BitVec.setWidth_eq _)
    rw [eq] at h
    intro fp K d c top hc ht m pc pre
    exact h hc ht m pc pre
  exact ⟨hi, floatOfIntAssemblyL_ofInt F hF z hz hi⟩

#print axioms floatOfIntAssemblyL_ofInt_zeuge

#print axioms floatOfIntAssemblyL_ofInt

#print axioms floatOfIntAssemblyL_right_ofInt
#print axioms floatOfIntAssemblyL_right_ofInt_zeuge

#print axioms floatOfIntAssemblyL_left_ofInt
#print axioms floatOfIntAssemblyL_left_ofInt_zeuge

/-- Canonical continuation after a producer has stored its result in `input`.
    All conversion temporaries start at `input + 1`; the final copy restores
    the public destination. The input slot is read explicitly by the assembly. -/
def floatOfIntContinuationL (F : Gleitkomma.Format) (input : Nat) :
    Option (List II × Nat) := do
  let ca ← floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) (input + 1)
    (fun j => some ([ci 2 j input 0], j + 1))
  pure (ca.1 ++ [ci 2 input (input + 1) 0], ca.2)

/-- Recover the actual assembly and final copy without a universal input producer. -/
theorem floatOfIntContinuationL_parts (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ assembly,
      floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) (input + 1)
        (fun j => some ([ci 2 j input 0], j + 1)) = some (assembly, top) ∧
      code = assembly ++ [ci 2 input (input + 1) 0] := by
  simp only [floatOfIntContinuationL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h
  obtain ⟨⟨assembly, ceiling⟩, ha, he⟩ := h
  cases he
  exact ⟨assembly, ha, rfl⟩

set_option maxRecDepth 4096 in
/-- The continuation really starts with the input-slot load. -/
theorem floatOfIntContinuationL_first (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (h : floatOfIntContinuationL F input = some (code, top)) :
    ∃ tail, code = ci 2 (input + 1) input 0 :: tail := by
  obtain ⟨assembly, ha, rfl⟩ := floatOfIntContinuationL_parts F input h
  simp only [floatOfIntAssemblyL, wennL, wordK, floatMagnitudeL, wordL,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ha
  obtain ⟨cc, hc, ca, ha, cb, hb, he⟩ := ha
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  obtain ⟨a', ha', b', hb', hab'⟩ := ha
  cases ha'
  cases hab'
  cases hab
  split at he
  · cases he
    simp only [wennC, bin2, List.cons_append, List.nil_append, List.append_assoc]
    exact ⟨_, rfl⟩
  · cases he

/-- Execute the input load with an explicit memory premise. The result includes
    the next PC and preservation outside the destination frame suffix. -/
theorem floatOfIntContinuationL_load {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K input : Nat} {v : Runner.W}
    (h : Pre L m pc fp K (input + 1) [ci 2 (input + 1) input 0] ρ W reserved)
    (hk : input + 1 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v := by
  obtain ⟨m', hs, hf, w, hw, rfl⟩ := mov_ok h (by omega) hk hr
  exact ⟨m', by simpa using hs, hf, hw⟩

/-- Execute the first instruction of the exact emitted continuation. -/
theorem floatOfIntContinuationL_first_step (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 1 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v := by
  obtain ⟨tail, rfl⟩ := floatOfIntContinuationL_first F input hc
  exact floatOfIntContinuationL_load (Pre.left (a := [_]) (b := tail) h) hk hr

/-- The actual first step preserves the retained input as well as loading the
    first magnitude temporary. Both reads concern the same executed memory. -/
theorem floatOfIntContinuationL_first_step_retained (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {v : Runner.W}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 1 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 input)) = some v ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some v := by
  obtain ⟨m', hs, ha, hd⟩ := floatOfIntContinuationL_first_step F hc h hk hr
  exact ⟨m', hs, ha, slotRead_agree h.frame ha (by omega) (by omega) hr, hd⟩

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
