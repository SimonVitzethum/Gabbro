/- Static resource bounds for the binary64 special dispatcher. -/
module
public import Stage0.Senke.Gleit.RoutineSpecial
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Unpacking has input-independent instruction counts and uses only the
    following temporary slots, including the two-slot constant builder. -/
theorem routineUnpack_emission {a : Nat → Option (List II × Nat)} {n w : Nat}
    (ha : FloatEmission a n w) :
    FloatEmission (fun d => unpackSignL d a) (n + 2) (w + 2) ∧
    FloatEmission (fun d => unpackBexpL d a) (n + 4) (w + 4) ∧
    FloatEmission (fun d => unpackFracL d a) (n + 18) (w + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · exact FloatEmission.bounds (FloatEmission.imm ha 12 (by decide) 63)
      (by omega) (by omega)
  · exact FloatEmission.bounds
      (FloatEmission.imm (FloatEmission.imm ha 12 (by decide) 52) 8 (by decide) 2047)
      (by omega) (by omega)
  · exact FloatEmission.bounds
      (FloatEmission.bin ha (FloatEmission.konst 4 4503599627370495) 8 (by decide))
      (by omega) (by omega)

/-- All three classifications reuse unpacking; only NaN needs a negation. -/
theorem routineClass_emission {a : Nat → Option (List II × Nat)} {n w : Nat}
    (ha : FloatEmission a n w) :
    FloatEmission (fun d => isNanL d (fun j => unpackBexpL j a)
      (fun j => unpackFracL j a)) (2 * n + 29) (w + 8) ∧
    FloatEmission (fun d => isInfL d (fun j => unpackBexpL j a)
      (fun j => unpackFracL j a)) (2 * n + 27) (w + 8) ∧
    FloatEmission (fun d => isZeroL d (fun j => unpackBexpL j a)
      (fun j => unpackFracL j a)) (2 * n + 27) (w + 8) := by
  obtain ⟨_, he, hf⟩ := routineUnpack_emission ha
  let eMax := FloatEmission.imm he 14 (by decide) 2047
  let eZero := FloatEmission.imm he 14 (by decide) 0
  let fZero := FloatEmission.imm hf 14 (by decide) 0
  let fNonzero := FloatEmission.bin (FloatEmission.literal 1) fZero 4 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · exact FloatEmission.bounds (FloatEmission.bin eMax fNonzero 8 (by decide))
      (by omega) (by omega)
  · exact FloatEmission.bounds (FloatEmission.bin eMax fZero 8 (by decide))
      (by omega) (by omega)
  · exact FloatEmission.bounds (FloatEmission.bin eZero fZero 8 (by decide))
      (by omega) (by omega)

/-- No path reserves input-dependent space or emits an unchecked displacement.
    The finite continuation's bound is explicit; its instructions contribute
    exactly once to the static code size, although only one branch executes. -/
theorem routineSpecialL_emission
    {a b finite : Nat → Option (List II × Nat)} {na nb nf wa wb wf : Nat}
    (ha : FloatEmission a na wa) (hb : FloatEmission b nb wb)
    (hf : FloatEmission finite nf wf)
    (bound : 16 * (11 * na + 12 * nb + nf + 243) < 2 ^ 31) :
    FloatEmission (fun d => routineSpecialL d a b finite)
      (11 * na + 12 * nb + nf + 243) (wa + wb + wf + 24) := by
  obtain ⟨sa, _, _⟩ := routineUnpack_emission ha
  obtain ⟨sb, _, _⟩ := routineUnpack_emission hb
  obtain ⟨nanA, infA, zeroA⟩ := routineClass_emission ha
  obtain ⟨nanB, infB, zeroB⟩ := routineClass_emission hb
  let sameSign := FloatEmission.bin sa sb 14 (by decide)
  let bothZero := FloatEmission.bin zeroA zeroB 8 (by decide)
  let zeroSign := FloatEmission.bin sa sb 8 (by decide)
  let zero := FloatEmission.literal 0
  let signField := FloatEmission.imm zeroSign 11 (by decide) 63
  let expField := FloatEmission.imm zero 11 (by decide) 52
  let upper := FloatEmission.bin signField expField 9 (by decide)
  have signedZero : FloatEmission (fun d => packL d
      (fun j => wordL 8 j (unpackSignL j a) (unpackSignL (j + 1) b))
      (fun j => some ([ci 1 j 0 0], j + 1))
      (fun j => some ([ci 1 j 0 0], j + 1)))
      (na + nb + 13) (wa + wb + 12) := by
    exact FloatEmission.bounds (FloatEmission.bin upper zero 9 (by decide))
      (by omega) (by omega)
  let nan := FloatEmission.konst 4 9218868437227405313
  have infPair := routineChooseL_emission sameSign ha nan (by omega)
  have infLeft := routineChooseL_emission infB infPair ha (by omega)
  have finiteOrZero := routineChooseL_emission bothZero signedZero hf (by omega)
  have infRight := routineChooseL_emission infB hb finiteOrZero (by omega)
  have infinities := routineChooseL_emission infA infLeft infRight (by omega)
  have rightNan := routineChooseL_emission nanB hb infinities (by omega)
  have result := routineChooseL_emission nanA ha rightNan (by omega)
  exact FloatEmission.bounds result (by omega) (by omega)

/-- The dispatcher emits for nonconstant operand sources, including the
    finite-continuation placeholder. These counts do not evaluate input data. -/
theorem routineSpecialL_emission_zeuge (left right finite : Nat) :
    FloatEmission (fun d => routineSpecialL d
      (fun j => some ([ci 2 j left 0], j + 1))
      (fun j => some ([ci 2 j right 0], j + 1))
      (fun j => some ([ci 2 j finite 0], j + 1))) 267 27 := by
  exact routineSpecialL_emission (FloatEmission.copy left) (FloatEmission.copy right)
    (FloatEmission.copy finite) (by decide)

#print axioms routineUnpack_emission
#print axioms routineClass_emission
#print axioms routineSpecialL_emission
#print axioms routineSpecialL_emission_zeuge
end Gabbro.Stage0.Senke
