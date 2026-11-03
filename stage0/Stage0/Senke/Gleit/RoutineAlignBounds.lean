/- Emission and slot bounds for ordered finite magnitude arithmetic. -/
module
public import Stage0.Senke.Gleit.RoutineAlign
public import Stage0.Senke.Gleit.RoutineBounds
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable [Runner.IR.Kern]

/-- Saturating alignment repeats producers but uses a bounded scratch suffix.
    This counts the existing quotient and sticky fragments without expansion
    of any encoded instruction bytes. -/
theorem routineJam_emission {a k : Nat → Option (List II × Nat)}
    {na nk wa wk : Nat} (ha : FloatEmission a na wa) (hk : FloatEmission k nk wk) :
    FloatEmission (fun d => alignShiftL d a k)
      (3 * na + 5 * nk + 17) (wa + wk + 10) := by
  let q := FloatEmission.quotient ha hk
  let back := FloatEmission.bin q hk 11 (by decide)
  let same := FloatEmission.bin ha back 14 (by decide)
  let lost := FloatEmission.bin (FloatEmission.literal 1) same 4 (by decide)
  exact FloatEmission.bounds (FloatEmission.bin q lost 9 (by decide))
    (by omega) (by omega)

theorem routineMagnitudeL_emission {a : Nat → Option (List II × Nat)} {n w : Nat}
    (ha : FloatEmission a n w) :
    FloatEmission (fun d => routineMagnitudeL d a) (n + 18) (w + 4) :=
  FloatEmission.bounds
    (FloatEmission.bin ha (FloatEmission.konst 4 9223372036854775807) 8 (by decide))
    (by omega) (by omega)

/-- Both hidden-bit cases and the zero-exponent scale are statically bounded. -/
theorem routineSigIndex_emission {a : Nat → Option (List II × Nat)} {n w : Nat}
    (ha : FloatEmission a n w) (bound : 16 * (3 * n + 62) < 2 ^ 31) :
    FloatEmission (fun d => routineSigL d a) (3 * n + 62) (w + 6) ∧
    FloatEmission (fun d => routineIndexL d a) (2 * n + 11) (w + 6) := by
  obtain ⟨_, exp, frac⟩ := routineUnpack_emission ha
  let zero := FloatEmission.imm exp 14 (by decide) 0
  let normal := FloatEmission.bin frac (FloatEmission.konst 4 4503599627370496) 3 (by decide)
  refine ⟨?_, ?_⟩
  · exact FloatEmission.bounds (routineChooseL_emission zero frac normal (by omega))
      (by omega) (by omega)
  · exact FloatEmission.bounds (FloatEmission.bin exp zero 3 (by decide))
      (by omega) (by omega)

/-- The directional add and subtract branches have equal instruction counts.
    All operand results live below the temporaries used by the other operand. -/
theorem routineDirectionalL_emission
    {large small : Nat → Option (List II × Nat)} {nl ns wl ws : Nat}
    (hl : FloatEmission large nl wl) (hs : FloatEmission small ns ws)
    (bound : 16 * (27 * nl + 39 * ns + 787) < 2 ^ 31) :
    FloatEmission (fun d => routineDirectionalL d large small)
      (27 * nl + 39 * ns + 787) (wl + 2 * ws + 40) := by
  obtain ⟨ls, li⟩ := routineSigIndex_emission hl (by omega)
  obtain ⟨ss, si⟩ := routineSigIndex_emission hs (by omega)
  obtain ⟨sl, _, _⟩ := routineUnpack_emission hl
  obtain ⟨sr, _, _⟩ := routineUnpack_emission hs
  let gap := FloatEmission.bin li si 4 (by decide)
  let lm := FloatEmission.imm ls 11 (by decide) 3
  let sm := routineJam_emission (FloatEmission.imm ss 11 (by decide) 3) gap
  let xor := FloatEmission.bin sl sr 10 (by decide)
  let same := FloatEmission.imm xor 14 (by decide) 0
  let add := FloatEmission.bin lm sm 3 (by decide)
  let sub := FloatEmission.bin lm sm 4 (by decide)
  exact FloatEmission.bounds (routineChooseL_emission same add sub (by omega))
    (by omega) (by omega)

/-- Sorting emits both directional paths but executes exactly one. The jump
    displacement bound also covers every nested branch and hidden-bit test. -/
theorem routineAlignL_emission
    {a b : Nat → Option (List II × Nat)} {na nb wa wb : Nat}
    (ha : FloatEmission a na wa) (hb : FloatEmission b nb wb)
    (bound : 16 * (67 * na + 67 * nb + 1613) < 2 ^ 31) :
    FloatEmission (fun d => routineAlignL d a b)
      (67 * na + 67 * nb + 1613) (2 * wa + 2 * wb + 40) := by
  let order := routineLessL_emission (routineMagnitudeL_emission ha) (routineMagnitudeL_emission hb)
  have left : FloatEmission (fun d => routineDirectionalL d b a)
      (27 * nb + 39 * na + 787) (wb + 2 * wa + 40) :=
    routineDirectionalL_emission hb ha (by omega)
  have right : FloatEmission (fun d => routineDirectionalL d a b)
      (27 * na + 39 * nb + 787) (wa + 2 * wb + 40) :=
    routineDirectionalL_emission ha hb (by omega)
  exact FloatEmission.bounds (routineChooseL_emission order left right (by omega))
    (by omega) (by omega)

/-- The runtime operand words are read from retained slots; their values do
    not affect either emission success or the scratch ceiling. -/
theorem routineAlignL_emission_zeuge (left right : Nat) :
    FloatEmission (fun d => routineAlignL d
      (fun j => some ([ci 2 j left 0], j + 1))
      (fun j => some ([ci 2 j right 0], j + 1))) 1747 44 :=
  routineAlignL_emission (FloatEmission.copy left) (FloatEmission.copy right) (by decide)

/-- The ordered branch has a smaller standalone ceiling than the complete
    two-direction selection, for the same retained input slots. -/
theorem routineDirectionalL_emission_zeuge (large small : Nat) :
    FloatEmission (fun d => routineDirectionalL d
      (fun j => some ([ci 2 j large 0], j + 1))
      (fun j => some ([ci 2 j small 0], j + 1))) 853 43 :=
  routineDirectionalL_emission (FloatEmission.copy large) (FloatEmission.copy small) (by decide)

#print axioms routineDirectionalL_emission_zeuge
#print axioms routineAlignL_emission
#print axioms routineAlignL_emission_zeuge
end Gabbro.Stage0.Senke
