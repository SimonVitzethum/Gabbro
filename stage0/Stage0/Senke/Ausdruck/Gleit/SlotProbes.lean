/- Concrete slot-bound conversion fixtures and child composition. -/
import Stage0.Senke.BildLese
import Stage0.Senke.Ausdruck.Gleit.Emission
import Stage0.Senke.Ausdruck.Gleit.SlotContext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

namespace SlotProbe

def memory (code : List II) : Runner.Mem where
  b a := if a.toNat < 4294967296 then ((code.flatMap encII)[a.toNat]?).getD 0 else 0
  rd _ := true
  wr _ := true

theorem pre (code : List II) (hlen : code.length ≤ 64001)
    (hops : code.all (fun i => decide (i.o < 256)) = true)
    (K : Nat) (hk : 8 ≤ K ∧ K < 2^30) :
    Pre L (memory code) 0 4294967296 K 8 code (Env.nil : Env D []) (fun _ => True) 4 := by
  have bound : (code.flatMap encII).length < 4294967296 := by
    rw [flatMap_enc_len]; omega
  refine ⟨by decide, by omega, ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · change 4294967296 + 8 * K < 2^64
    omega
  · apply codeAt_bytes code 0 hops
    intro i hi
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega),
      if_pos (show i < 4294967296 by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · change 0 + 16 * code.length < 2^64 ∧ 4294967296 + 8 * K ≤ 2^64 ∧
      0 + 16 * code.length ≤ 4294967296
    omega
  · intro _ x
    nomatch x

end SlotProbe

namespace ZeroContinuationProbe

noncomputable def code : List II :=
  Classical.choose (FloatEmission.continuation Gleitkomma.f64 8)
noncomputable def top : Nat :=
  Classical.choose (Classical.choose_spec (FloatEmission.continuation Gleitkomma.f64 8))

theorem emitted : floatOfIntContinuationL Gleitkomma.f64 8 = some (code, top) ∧
    code.length = 63984 ∧ top ≤ 123 ∧
    code.all (fun i => decide (i.o < 256)) = true :=
  Classical.choose_spec (Classical.choose_spec (FloatEmission.continuation Gleitkomma.f64 8))

noncomputable def memory : Runner.Mem := SlotProbe.memory code

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pre : Pre L memory 0 4294967296 64 8 code (Env.nil : Env D [])
    (fun _ => True) 4 := by
  exact SlotProbe.pre code (by rw [emitted.2.1]; decide) emitted.2.2.2 64 (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Emitted code, writable disjoint memory, reserved prefix and zero input
    jointly inhabit the premises of the complete concrete continuation. -/
theorem floatOfIntContinuationL_zero_ok_zeuge :
    floatOfIntContinuationL Gleitkomma.f64 8 = some (code, top) ∧
    code ≠ [] ∧
    Pre L memory 0 4294967296 64 8 code (Env.nil : Env D []) (fun _ => True) 4 ∧
    memory.rd64 (slot 4294967296 (BitVec.ofNat 64 8)) = some (BitVec.ofInt 64 0) ∧
    Ok memory 0 4294967296 64 8 code (· = 0) := by
  have hc : floatOfIntContinuationL Gleitkomma.f64 8 = some (code, top) := emitted.1
  have hr : memory.rd64 (slot 4294967296 (BitVec.ofNat 64 8)) = some (BitVec.ofInt 64 0) := by
    decide +kernel
  exact ⟨hc, (by intro he; have hl := emitted.2.1; simp [he] at hl), pre, hr,
    floatOfIntContinuationL_zero_ok (L := L) Gleitkomma.f64 hc (pre (L := L)) (by decide) hr⟩

#print axioms floatOfIntContinuationL_zero_ok_zeuge
end ZeroContinuationProbe

namespace ComputedConversionProbe

def child (z : Int) (d : Nat) : Option (List II × Nat) :=
  some (konstWL 4 (BitVec.ofInt 64 z).toNat d)

theorem output (F : Gleitkomma.Format) (z : Int) :
    ∃ c t, computedFloatOfL F 8 (child z) = some (c, t) ∧
      c.length = 64001 ∧ t ≤ 123 ∧ c.all (fun i => decide (i.o < 256)) = true := by
  obtain ⟨suffix, st, hs, ls, ts, os⟩ := FloatEmission.continuation F 8
  obtain ⟨cc, ct, hc, lc, tc, oc⟩ := FloatEmission.konst 4 (BitVec.ofInt 64 z).toNat 8
  refine ⟨cc ++ suffix, max ct st, ?_, ?_, by omega, ?_⟩
  · change child z 8 = some (cc, ct) at hc
    unfold computedFloatOfL
    rw [hc, hs]
    rfl
  · simp [lc, ls]
  · simp [List.all_append, oc, os]

noncomputable def code (F : Gleitkomma.Format) (z : Int) : List II :=
  Classical.choose (output F z)
noncomputable def top (F : Gleitkomma.Format) (z : Int) : Nat :=
  Classical.choose (Classical.choose_spec (output F z))

theorem emitted (F : Gleitkomma.Format) (z : Int) :
    computedFloatOfL F 8 (child z) = some (code F z, top F z) ∧
    (code F z).length = 64001 ∧ top F z ≤ 123 ∧
    (code F z).all (fun i => decide (i.o < 256)) = true :=
  Classical.choose_spec (Classical.choose_spec (output F z))

noncomputable def memory (F : Gleitkomma.Format) (z : Int) : Runner.Mem := SlotProbe.memory (code F z)

theorem pre (F : Gleitkomma.Format) (z : Int) :
    Pre L (memory F z) 0 4294967296 256 8 (code F z)
      (Env.nil : Env D []) (fun _ => True) 4 :=
  SlotProbe.pre (code F z) (Nat.le_of_eq (emitted F z).2.1) (emitted F z).2.2.2 256 (by decide)

/-- The real constant-producing child and emitted continuation jointly execute
    in disjoint concrete code/frame memory, for every supported signed word. -/
theorem computedFloatOfL_ok_zeuge (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64]) (z : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) :
    computedFloatOfL F 8 (child z) = some (code F z, top F z) ∧
    (code F z).length = 64001 ∧
    Pre L (memory F z) 0 4294967296 256 8 (code F z)
      (Env.nil : Env D []) (fun _ => True) 4 ∧
    Ok (memory F z) 0 4294967296 256 8 (code F z)
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  have emitted := emitted F z
  have hp := pre (L := L) F z
  refine ⟨emitted.1, emitted.2.1, hp, ?_⟩
  let v : Zahl (-2^63) (2^63 - 1) := ⟨z, hz.1, by omega⟩
  apply computedFloatOfL_ok F hF v (by omega) (by decide) emitted.1 hp (by omega)
  intro ce he
  have ceEq : ce = konstWL 4 (BitVec.ofInt 64 z).toNat 8 := (Option.some.inj he).symm
  subst ce
  obtain ⟨actualChild, assembly, hec, _, codeEq, _⟩ :=
    computedFloatOfL_parts F 8 (child z) emitted.1
  have childEq : actualChild = konstWL 4 (BitVec.ofInt 64 z).toNat 8 :=
    (Option.some.inj hec).symm
  rw [childEq] at codeEq
  rw [codeEq, List.append_assoc] at hp
  have run := konstWL_ok 4 (BitVec.ofInt 64 z).toNat (BitVec.isLt _) (by decide) hp.left
  simpa only [Enc, v, BitVec.ofNat_toNat, BitVec.setWidth_eq] using run

/-- Zero, both signs, minInt, tie, carry and shift-zero runs in both formats. -/
theorem computedFloatOfL_ok_samples (L : Lay D) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
    ∀ z ∈ ([0, 37, -37, -9223372036854775808, 9007199254740993,
      18014398509481983, 4503599627370496] : List Int),
    Ok (memory F z) 0 4294967296 256 8 (code F z)
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  intro F hF z hz
  have bounds : -2^63 ≤ z ∧ z < 2^63 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact (computedFloatOfL_ok_zeuge (L := L) F hF z bounds).2.2.2

#print axioms computedFloatOfL_ok_samples
#print axioms computedFloatOfL_ok_zeuge
end ComputedConversionProbe

end Gabbro.Stage0.Senke
