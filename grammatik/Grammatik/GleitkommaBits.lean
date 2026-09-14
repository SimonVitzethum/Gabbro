/-
  File:      Grammatik/GleitkommaBits.lean
  Subject:   Bit patterns back to values, and well-formedness of every
             result of the IEEE-754 model (`Gleitkomma.lean`) -- what the C
             side of the float correspondence (`CFormenF.lean`) reads.

  Kept apart from `Gleitkomma.lean` so the model file (imported by
  `Typen.lean`, hence by everything) does not change for the C side.
-/
import Grammatik.Gleitkomma

namespace Gabbro.Grammatik.Gleitkomma

/-! ## Bits back to values, and every result well-formed

  The C side (`CFormenF.lean`) holds a float as its bit pattern
  (`zuBits`); `ausBits` reads it back. The two are inverse on well-formed
  triples of a format whose exponent field is exactly full (`dicht`:
  `2 ^ ebits = bexpMax + 1`, true for binary32 and binary64), and every op
  of the model returns a well-formed triple from well-formed inputs
  (`add_wf` … `ofInt_wf`) -- so a value the model computes is always the
  value its bits denote. -/

/-- A bit pattern as a value (the inverse of `zuBits`, `ausBits_zuBits`). -/
def ausBits (F : Format) (n : Nat) : GBits F :=
  ⟨(n / 2 ^ (F.ebits + F.fracBits)) % 2 == 1, (n / 2 ^ F.fracBits) % 2 ^ F.ebits,
    n % 2 ^ F.fracBits⟩

/-- The exponent field holds exactly the biased exponents `0 .. bexpMax`. -/
def Format.dicht (F : Format) : Prop := 2 ^ F.ebits = F.bexpMax + 1

theorem f32_dicht : f32.dicht := by unfold Format.dicht; decide
theorem f64_dicht : f64.dicht := by unfold Format.dicht; decide

/-- Splitting a packed triple back into its fields (pure `Nat` arithmetic). -/
theorem zerlege (S b fr e f : Nat) (hb : b < 2 ^ e) (hf : fr < 2 ^ f) :
    (S * 2 ^ (e + f) + b * 2 ^ f + fr) % 2 ^ f = fr ∧
    ((S * 2 ^ (e + f) + b * 2 ^ f + fr) / 2 ^ f) % 2 ^ e = b ∧
    (S * 2 ^ (e + f) + b * 2 ^ f + fr) / 2 ^ (e + f) = S := by
  have hpf : 0 < 2 ^ f := Nat.pow_pos (by decide)
  have hpe : 0 < 2 ^ e := Nat.pow_pos (by decide)
  have hn : S * 2 ^ (e + f) + b * 2 ^ f + fr = fr + (b + S * 2 ^ e) * 2 ^ f := by
    rw [Nat.pow_add, Nat.add_mul, ← Nat.mul_assoc]; omega
  rw [hn]
  have h1 : (fr + (b + S * 2 ^ e) * 2 ^ f) / 2 ^ f = b + S * 2 ^ e := by
    rw [Nat.add_mul_div_right _ _ hpf, Nat.div_eq_of_lt hf, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  · rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.pow_add, Nat.mul_comm (2 ^ e) (2 ^ f), ← Nat.div_div_eq_div_mul, h1,
      Nat.add_mul_div_right _ _ hpe, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem zuBits_zerlegt (F : Format) (g : GBits F) :
    zuBits F g = (if g.sign then 1 else 0) * 2 ^ (F.ebits + F.fracBits)
      + g.bexp * 2 ^ F.fracBits + g.frac := by
  unfold zuBits; cases g.sign <;> simp

/-- Reading back the bits of a well-formed triple gives the triple. -/
theorem ausBits_zuBits (F : Format) (hF : F.dicht) (g : GBits F) (hw : wf F g) :
    ausBits F (zuBits F g) = g := by
  obtain ⟨hb, hf⟩ := hw
  have hb' : g.bexp < 2 ^ F.ebits := by unfold Format.dicht at hF; omega
  obtain ⟨z1, z2, z3⟩ := zerlege (if g.sign then 1 else 0) g.bexp g.frac F.ebits F.fracBits hb' hf
  unfold ausBits
  rw [zuBits_zerlegt, z1, z2, z3]
  cases g with
  | mk s b fr => cases s <;> rfl

/-- The bits of a well-formed triple fit `1 + ebits + fracBits` bits (64 for
    binary64, 32 for binary32). -/
theorem zuBits_lt (F : Format) (hF : F.dicht) (g : GBits F) (hw : wf F g) :
    zuBits F g < 2 ^ (F.ebits + F.fracBits + 1) := by
  obtain ⟨hb, hf⟩ := hw
  have hb' : g.bexp + 1 ≤ 2 ^ F.ebits := by unfold Format.dicht at hF; omega
  rw [zuBits_zerlegt]
  have h1 : g.bexp * 2 ^ F.fracBits + g.frac < 2 ^ (F.ebits + F.fracBits) := by
    have hm := Nat.mul_le_mul hb' (Nat.le_refl (2 ^ F.fracBits))
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add] at hm
    omega
  have h2 : (if g.sign then 1 else 0) * 2 ^ (F.ebits + F.fracBits) ≤ 2 ^ (F.ebits + F.fracBits) := by
    cases g.sign <;> simp
  rw [Nat.pow_succ]
  omega

theorem wf_null (F : Format) (s : Bool) : wf F ⟨s, 0, 0⟩ :=
  ⟨Nat.zero_le _, Nat.pow_pos (by decide)⟩

theorem wf_unendlich (F : Format) (s : Bool) : wf F ⟨s, F.bexpMax, 0⟩ :=
  ⟨Nat.le_refl _, Nat.pow_pos (by decide)⟩

theorem nanQ_wf (F : Format) (hp : 2 ≤ F.p) : wf F (nanQ F) := by
  refine ⟨Nat.le_refl _, ?_⟩
  show 1 < 2 ^ (F.p - 1)
  have : 2 ^ 1 ≤ 2 ^ (F.p - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem neg_wf (F : Format) (a : GBits F) (h : wf F a) : wf F (neg F a) := h

/-- The rounding kernel returns a well-formed triple (case analysis only:
    no bound on `findeExp` is needed -- every branch is guarded). -/
theorem rundeBruchKern_wf (F : Format) (hp : 1 ≤ F.p) (s : Bool) (n d : Nat) (E : Int) :
    wf F (rundeBruchKern F s n d E) := by
  have hemin : F.emin = 1 - (F.emax : Int) := rfl
  have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
  have hfb : F.fracBits = F.p - 1 := rfl
  have hpp : 2 ^ F.p = 2 * 2 ^ (F.p - 1) := by
    have e : F.p = (F.p - 1) + 1 := by omega
    conv => lhs; rw [e]
    rw [Nat.pow_succ, Nat.mul_comm]
  unfold rundeBruchKern
  by_cases h1 : (F.emax : Int) < E
  · rw [if_pos h1]; exact wf_unendlich F s
  · rw [if_neg h1]
    by_cases h2 : E < F.emin - (F.p : Int)
    · rw [if_pos h2]; exact wf_null F s
    · rw [if_neg h2]
      by_cases h3 : F.emin ≤ E
      · rw [if_pos h3]
        by_cases h4 : normQ F.p E n d < 2 ^ F.p
        · rw [if_pos h4]
          refine ⟨?_, ?_⟩
          · show (E - F.emin + 1).toNat ≤ F.bexpMax
            omega
          · show normQ F.p E n d - 2 ^ (F.p - 1) < 2 ^ F.fracBits
            rw [hfb]; omega
        · rw [if_neg h4]
          by_cases h5 : E < (F.emax : Int)
          · rw [if_pos h5]
            refine ⟨?_, Nat.pow_pos (by decide)⟩
            show (E - F.emin + 2).toNat ≤ F.bexpMax
            omega
          · rw [if_neg h5]; exact wf_unendlich F s
      · rw [if_neg h3]
        by_cases h6 : subQ F n d < 2 ^ (F.p - 1)
        · rw [if_pos h6]
          exact ⟨Nat.zero_le _, by rw [hfb]; exact h6⟩
        · rw [if_neg h6]
          exact ⟨show 1 ≤ F.bexpMax by omega, Nat.pow_pos (by decide)⟩

theorem rundeBruch_wf (F : Format) (hp : 2 ≤ F.p) (b : Bruch) : wf F (rundeBruch F b) := by
  unfold rundeBruch rundeBruchBei
  by_cases hd : b.nenner = 0
  · rw [if_pos hd]; exact nanQ_wf F hp
  · rw [if_neg hd]
    by_cases hn : b.zaehler.natAbs = 0
    · rw [if_pos hn]; exact wf_null F _
    · rw [if_neg hn]; exact rundeBruchKern_wf F (by omega) _ _ _ _

theorem rundeExakt_wf (F : Format) (hp : 2 ≤ F.p) (v : Exakt) : wf F (rundeExakt F v) :=
  rundeBruch_wf F hp _

theorem ofInt_wf (F : Format) (hp : 2 ≤ F.p) (z : Int) : wf F (ofInt F z) :=
  rundeExakt_wf F hp _

theorem ofRat_wf (F : Format) (hp : 2 ≤ F.p) (z : Int) (n : Nat) : wf F (ofRat F z n) :=
  rundeBruch_wf F hp _

theorem add_wf (F : Format) (hp : 2 ≤ F.p) (a b : GBits F) (ha : wf F a) (hb : wf F b) :
    wf F (add F a b) := by
  unfold add
  split
  all_goals first
    | exact ha
    | exact hb
    | exact wf_null F _
    | (split <;> first | exact ha | exact nanQ_wf F hp)
    | (split <;> first | exact rundeExakt_wf F hp _ | exact nanQ_wf F hp)

theorem sub_wf (F : Format) (hp : 2 ≤ F.p) (a b : GBits F) (ha : wf F a) (hb : wf F b) :
    wf F (sub F a b) :=
  add_wf F hp a (neg F b) ha (neg_wf F b hb)

theorem mul_wf (F : Format) (hp : 2 ≤ F.p) (a b : GBits F) (ha : wf F a) (hb : wf F b) :
    wf F (mul F a b) := by
  unfold mul
  split
  all_goals first
    | exact ha
    | exact hb
    | exact wf_null F _
    | exact wf_unendlich F _
    | exact nanQ_wf F hp
    | (split <;> first | exact rundeExakt_wf F hp _ | exact nanQ_wf F hp)

theorem div_wf (F : Format) (hp : 2 ≤ F.p) (a b : GBits F) (ha : wf F a) (hb : wf F b) :
    wf F (div F a b) := by
  unfold div
  split
  all_goals first
    | exact ha
    | exact hb
    | exact wf_null F _
    | exact wf_unendlich F _
    | exact nanQ_wf F hp
    | (split <;> first | exact rundeBruch_wf F hp _ | exact nanQ_wf F hp)
    | (split
       · split
         · exact nanQ_wf F hp
         · exact wf_unendlich F _
       · exact nanQ_wf F hp)

theorem f32_p : 2 ≤ f32.p := by decide
theorem f64_p : 2 ≤ f64.p := by decide

/-- The class test behind `isfinite`, on the class alone (one function for
    both sides, so no two matchers ever have to be compared: the KERNEL,
    comparing two different `match`es over a stuck float, evaluates the
    discriminant and recursed out of its stack -- measured 2026-09-14). -/
def endlichK : Klasse → Bool
  | .unendlich => false
  | .nan => false
  | _ => true

/-- IEEE equality: NaN is unequal to everything (itself included), signed
    zeros are equal. -/
def feq (F : Format) (a b : GBits F) : Bool := fle F a b && fle F b a


#print axioms ausBits_zuBits
#print axioms zuBits_lt
#print axioms add_wf
#print axioms mul_wf
#print axioms div_wf
#print axioms rundeBruch_wf

end Gabbro.Grammatik.Gleitkomma
