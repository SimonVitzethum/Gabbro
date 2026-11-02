module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil6a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil5

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatOfIntContinuationL_zero_output (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 208, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 0 := by
  obtain ⟨m1, s1, a1, r1⟩ := floatOfIntContinuationL_zero_fallthrough F hc h hk hr
  obtain ⟨jump, tail, he⟩ := floatOfIntContinuationL_first_output F input hc
  rw [he] at h
  have hp := Pre.next (a := [ci 2 (input + 1) input 0, ci 1 (input + 2) 1 0,
    ci 1 (input + 3) 2 0, ci 2 (input + 4) input 0, ci 1 (input + 5) 0 0,
    ci 13 (input + 4) (input + 4) (input + 5),
    ci 5 (input + 3) (input + 3) (input + 4),
    ci 4 (input + 2) (input + 2) (input + 3),
    ci 5 (input + 1) (input + 1) (input + 2), ci 1 (input + 2) 0 0,
    ci 14 (input + 1) (input + 1) (input + 2), ci 19 (input + 1) jump 0]) h a1
    (show input + 1 ≤ input + 1 by omega) (by omega)
  obtain ⟨m2, s2, a2, w, r, hw⟩ := const_ok hp.left (by decide) (by omega)
  subst w
  refine ⟨m2, ?_, a1.trans a2, r⟩
  simpa [BitVec.add_assoc] using s1.trans s2

/-- Execute all seventeen emitted instructions of the zero constant. -/
theorem floatOfIntContinuationL_zero_constant (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 464, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 0 := by
  obtain ⟨m1, s1, a1, _⟩ := floatOfIntContinuationL_zero_fallthrough F hc h hk hr
  obtain ⟨precode, tail, he, hl⟩ := floatOfIntContinuationL_zero_constant_parts F input hc
  rw [he, List.append_assoc] at h
  have hp := Pre.next (a := precode) h a1 (Nat.le_refl _) (by omega)
  have hp' : Pre L m1 (pc + 192) fp K (input + 1)
      (konstWL 4 0 (input + 1)).1 ρ W reserved := by
    simpa [hl] using hp.left
  obtain ⟨m2, s2, a2, w, r, hw⟩ := konstWL_ok 4 0 (by decide) (by omega) hp'
  subst w
  refine ⟨m2, ?_, a1.trans a2, r⟩
  simpa [konstWL, bin2, BitVec.add_assoc] using s1.trans s2

/-- The public destination copy is the actual last instruction, at the
    penultimate machine boundary of the continuation. -/
theorem floatOfIntContinuationL_final_copy (F : Gleitkomma.Format) (input : Nat)
    {code : List II} {top : Nat}
    (hc : floatOfIntContinuationL F input = some (code, top)) :
    ∃ assembly, code = assembly ++ [ci 2 input (input + 1) 0] ∧
      code.length = assembly.length + 1 ∧
      code[ assembly.length ]? = some (ci 2 input (input + 1) 0) := by
  obtain ⟨assembly, _, he⟩ := floatOfIntContinuationL_parts F input hc
  refine ⟨assembly, he, ?_, ?_⟩ <;> simp [he]

/-- Execute the end jump after the zero write, fetching from the emitted code. -/
theorem floatOfIntContinuationL_zero_endjump (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II} {offset : Int}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0))
    (encoded : code[29]? = some (ci 18 offset 0 0))
    (hl : lit32 offset = true) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 464 + BitVec.ofInt 64 offset, fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 0 := by
  obtain ⟨m', hs, ha, hr'⟩ := floatOfIntContinuationL_zero_constant F hc h hk hr
  have bound : 29 < code.length := by
    by_cases hb : 29 < code.length
    · exact hb
    · have he : code[29]? = none := List.getElem?_eq_none (by omega)
      rw [he] at encoded
      cases encoded
  have hi := (h.code.agree ha h.far) 29 bound
  have entry : code[29] = ci 18 offset 0 0 := by
    simpa only [List.getElem?_eq_getElem bound, Option.some.injEq] using encoded
  rw [entry] at hi
  simp only [ci] at hi
  have sj := Star.one (run_step (t := ⟨pc + 464, fp⟩) hi (by decide)
    (run_jmp (t := ⟨pc + 464, fp⟩) hi))
  refine ⟨m', hs.trans ?_, ha, hr'⟩
  simpa only [sx_lit hl] using sj

/-- The generated zero jump reaches the exact final-copy boundary without
    an encoding or displacement assumption supplied by the caller. -/
theorem floatOfIntContinuationL_zero_finalcopyPC (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top : Nat}
    {code : List II}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K (input + 1) code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0)) :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (code.length - 1)), fp⟩ m' ∧
      Agree fp (input + 1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some 0 := by
  obtain ⟨normal, hi, hn, hl⟩ := floatOfIntContinuationL_zero_jump_encoding F input hc
  obtain ⟨m', hs, ha, hr'⟩ := floatOfIntContinuationL_zero_endjump F hc h hk hr hi hl
  refine ⟨m', ?_, ha, hr'⟩
  have pos : 464 + 16 * (normal.length + 1) = 16 * (code.length - 1) := by omega
  have wp := congrArg (BitVec.ofNat 64) pos
  rw [BitVec.ofNat_add] at wp
  change (464 : Runner.W) + BitVec.ofNat 64 (16 * (normal.length + 1)) =
    BitVec.ofNat 64 (16 * (code.length - 1)) at wp
  simpa only [BitVec.ofInt_natCast, BitVec.add_assoc, wp] using hs

/-- Execute the final emitted move after the concrete zero jump. -/
theorem floatOfIntContinuationL_zero_ok (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top reserved : Nat}
    {code : List II}
    (hc : floatOfIntContinuationL F input = some (code, top))
    (h : Pre L m pc fp K input code ρ W reserved)
    (hk : input + 5 < K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 0)) :
    Ok m pc fp K input code (· = 0) := by
  have ht : Pre L m pc fp K (input + 1) code ρ W reserved :=
    { h with ctx := Nat.le_trans h.ctx (Nat.le_succ _) }
  obtain ⟨m1, s1, a1, r1⟩ := floatOfIntContinuationL_zero_finalcopyPC F hc ht hk hr
  obtain ⟨assembly, he, hl, _⟩ := floatOfIntContinuationL_final_copy F input hc
  have hp := h
  rw [he] at hp
  have hp1 := hp.next (a1.mono (Nat.le_succ input)) (Nat.le_refl _) (by omega)
  obtain ⟨m2, s2, a2, w, r2, hw⟩ := mov_ok (s := input + 1) (d := input) hp1 (by omega) (by omega) r1
  subst w
  refine ⟨m2, ?_, (a1.mono (Nat.le_succ input)).trans a2, 0, r2, rfl⟩
  have sl : code.length - 1 = assembly.length := by omega
  rw [sl] at s1
  have endpc := pc_add16 pc assembly.length
  simpa only [List.length_singleton, Nat.mul_one, BitVec.ofNat_eq_ofNat,
    endpc, hl] using s1.trans s2

#print axioms floatOfIntContinuationL_zero_ok

#print axioms floatOfIntContinuationL_zero_endjump

#print axioms floatOfIntContinuationL_final_copy

/-- Candidate composition: evaluate the child once, retain its word below all
    conversion temporaries, then place the converted word in the destination.
    This helper is deliberately not accepted by `lowE` before its simulation proof. -/
def computedFloatOfL (F : Gleitkomma.Format) (d : Nat)
    (child : Nat → Option (List II × Nat)) : Option (List II × Nat) := do
  let ce ← child d
  let suffix ← floatOfIntContinuationL F d
  pure (ce.1 ++ suffix.1, max ce.2 suffix.2)

/-- Child and assembly ceilings both contribute to the candidate's frame bound. -/
theorem computedFloatOfL_parts (F : Gleitkomma.Format) (d : Nat)
    (child : Nat → Option (List II × Nat)) {c : List II} {top : Nat}
    (h : computedFloatOfL F d child = some (c, top)) :
    ∃ ce ca, child d = some ce ∧
      floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) (d + 1)
        (fun j => some ([ci 2 j d 0], j + 1)) = some ca ∧
      c = ce.1 ++ ca.1 ++ [ci 2 d (d + 1) 0] ∧
      top = max ce.2 ca.2 := by
  simp only [computedFloatOfL, floatOfIntContinuationL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h
  obtain ⟨ce, he, ca, ha, hc⟩ := h
  obtain ⟨assembly, ha, rfl⟩ := ha
  cases hc
  exact ⟨ce, assembly, he, ha, (List.append_assoc _ _ _).symm, rfl⟩

/-- A successful composition preserves both independently computed ceilings. -/
theorem computedFloatOfL_ceiling (F : Gleitkomma.Format) (d : Nat)
    (child : Nat → Option (List II × Nat)) {c : List II} {top K : Nat}
    (h : computedFloatOfL F d child = some (c, top)) (ht : top ≤ K) :
    ∃ ce ca, child d = some ce ∧
      floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) (d + 1)
        (fun j => some ([ci 2 j d 0], j + 1)) = some ca ∧
      ce.2 ≤ K ∧ ca.2 ≤ K := by
  obtain ⟨ce, ca, he, ha, _, htop⟩ := computedFloatOfL_parts F d child h
  exact ⟨ce, ca, he, ha, by omega, by omega⟩

/-- Recover the signed assembly input from the child's actual encoding. -/
theorem computedFloatOfL_encodedInput {lo hi : Int} (v : Zahl lo hi)
    (hlo : -2^63 ≤ lo) (hhi : hi < 2^63) (w : Runner.W)
    (hw : Enc L (.int lo hi) v w) :
    w = BitVec.ofInt 64 v.n ∧ -2^63 ≤ v.n ∧ v.n < 2^63 := by
  have hvl := v.lo_le
  have hvh := v.le_hi
  exact ⟨hw, by omega, by omega⟩

end Gabbro.Stage0.Senke
