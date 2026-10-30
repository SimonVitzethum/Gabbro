/- Compositional emission bounds without expanding encoded instruction bytes. -/
import Stage0.Senke.Ausdruck.Gleit.Skalieren

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- A generator's static size, temporary ceiling and byte-sized opcodes. -/
def FloatEmission (a : Nat → Option (List II × Nat)) (size width : Nat) : Prop :=
  ∀ d, ∃ code top, a d = some (code, top) ∧ code.length = size ∧
    top ≤ d + width ∧ code.all (fun i => decide (i.o < 256)) = true

namespace FloatEmission

theorem literal (v : Int) :
    FloatEmission (fun d => some ([ci 1 d v 0], d + 1)) 1 1 := by
  intro d
  exact ⟨_, _, rfl, rfl, Nat.le_refl _, by simp [ci]⟩

theorem copy (input : Nat) :
    FloatEmission (fun d => some ([ci 2 d input 0], d + 1)) 1 1 := by
  intro d
  exact ⟨_, _, rfl, rfl, Nat.le_refl _, by simp [ci]⟩

theorem bin {a b : Nat → Option (List II × Nat)} {na nb wa wb : Nat}
    (ha : FloatEmission a na wa) (hb : FloatEmission b nb wb)
    (o : Nat) (ho : o < 256) :
    FloatEmission (fun d => wordL o d (a d) (b (d + 1)))
      (na + nb + 1) (max (max wa (wb + 1)) 2) := by
  intro d
  obtain ⟨ca, ta, ea, la, ba, oa⟩ := ha d
  obtain ⟨cb, tb, eb, lb, bb, ob⟩ := hb (d + 1)
  refine ⟨(bin2 o d (ca, ta) (cb, tb)).1, max (max ta tb) (d + 2),
    by simp [wordL, ea, eb], ?_, ?_, ?_⟩
  · simp [bin2, la, lb, Nat.add_assoc]
  · omega
  · simp [bin2, List.all_append, oa, ob, ci, ho]

theorem imm {a : Nat → Option (List II × Nat)} {n w : Nat}
    (ha : FloatEmission a n w) (o : Nat) (ho : o < 256) (v : Int) :
    FloatEmission (fun d => wordK o d (a d) v) (n + 2) (max (max w 2) 2) := by
  exact bin ha (literal v) o ho

theorem branch {c a b : Nat → Option (List II × Nat)} {nc na nb wc wa wb : Nat}
    (hc : FloatEmission c nc wc) (ha : FloatEmission a na wa)
    (hb : FloatEmission b nb wb) (bound : 16 * (na + nb + 2) < 2^31) :
    FloatEmission (fun d => wennL d (c d) (a d) (b d))
      (nc + na + nb + 2) (max wc (max wa wb)) := by
  intro d
  obtain ⟨cc, tc, ec, lc, bc, oc⟩ := hc d
  obtain ⟨ca, ta, ea, la, ba, oa⟩ := ha d
  obtain ⟨cb, tb, eb, lb, bb, ob⟩ := hb d
  refine ⟨wennC d cc ca cb, max tc (max ta tb),
    by simp [wennL, ec, ea, eb, la, lb, bound], ?_, ?_, ?_⟩
  · simp [wennC, lc, la, lb]; omega
  · omega
  · simp [wennC, List.all_append, oc, oa, ob, ci]

theorem konst (k n : Nat) :
    FloatEmission (fun d => some (konstWL k n d)) (1 + 4 * k) 2 := by
  induction k generalizing n with
  | zero =>
    intro d
    exact ⟨_, _, rfl, rfl, by omega, by simp [ci]⟩
  | succ k ih =>
    intro d
    obtain ⟨c, t, he, hl, ht, ho⟩ := ih (n / 65536) d
    have he' := Option.some.inj he
    refine ⟨_, _, rfl, ?_, ?_, ?_⟩
    · simp only [konstWL, he', bin2, List.length_append, List.length_singleton]
      simp only [hl]
      omega
    · simp only [konstWL, he', bin2]
      omega
    · simp [konstWL, he', bin2, List.all_append, ho, ci]

theorem bounds {a : Nat → Option (List II × Nat)} {n w n' w' : Nat}
    (h : FloatEmission a n w) (hn : n = n') (hw : w ≤ w') : FloatEmission a n' w' := by
  intro d
  obtain ⟨c, t, he, hl, ht, ho⟩ := h d
  exact ⟨c, t, he, hl.trans hn, by omega, ho⟩

theorem magnitude {a : Nat → Option (List II × Nat)} {n w : Nat}
    (h : FloatEmission a n w) :
    FloatEmission (fun d => floatMagnitudeL d a) (2 * n + 7) (w + 5) := by
  let sign := imm h 13 (by decide) 0
  let twice := bin (literal 2) sign 5 (by decide)
  let factor := bin (literal 1) twice 4 (by decide)
  apply bounds (bin h factor 5 (by decide)) <;> omega

theorem exponentAux {a : Nat → Option (List II × Nat)} {n w : Nat}
    (h : FloatEmission a n w) (fuel : Nat) :
    FloatEmission (floatExponentAuxL a fuel) (1 + fuel * (n + 7)) (w + 8) := by
  induction fuel with
  | zero => exact bounds (literal 0) (by omega) (by omega)
  | succ fuel ih =>
    let shifted := imm h 12 (by decide) (fuel + 1)
    let zero := imm shifted 14 (by decide) 0
    let nonzero := bin (literal 1) zero 4 (by decide)
    apply bounds (bin ih nonzero 3 (by decide))
    · simp [Nat.succ_mul]; omega
    · omega

theorem exponent {a : Nat → Option (List II × Nat)} {n w : Nat}
    (h : FloatEmission a n w) :
    FloatEmission (fun d => floatExponentL d a) (64 * n + 445) (w + 12) := by
  apply bounds (bin (exponentAux h 63) (imm h 14 (by decide) 0) 4 (by decide)) <;> omega

theorem quotient {a k : Nat → Option (List II × Nat)} {na nk wa wk : Nat}
    (ha : FloatEmission a na wa) (hk : FloatEmission k nk wk) :
    FloatEmission (fun d => floatShiftQuotL d a k)
      (na + 2 * nk + 6) (wa + wk + 6) := by
  let q := bin ha hk 12 (by decide)
  let small := imm (imm hk 12 (by decide) 6) 14 (by decide) 0
  apply bounds (bin q small 5 (by decide)) <;> omega

theorem rounding {q r den : Nat → Option (List II × Nat)}
    {nq nr nd wq wr wd : Nat}
    (hq : FloatEmission q nq wq) (hr : FloatEmission r nr wr)
    (hd : FloatEmission den nd wd) :
    FloatEmission (fun d => floatRoundL d q r den)
      (2 * nq + 4 * nr + 2 * nd + 9) (wq + wr + wd + 8) := by
  let gap := bin hd hr 4 (by decide)
  let above := bin gap hr 13 (by decide)
  let tie := bin hr gap 14 (by decide)
  let odd := imm hq 8 (by decide) 1
  apply bounds (bin hq (bin above (bin tie odd 8 (by decide)) 9 (by decide)) 3 (by decide)) <;> omega

theorem roundShift {a k : Nat → Option (List II × Nat)} {na nk wa wk : Nat}
    (ha : FloatEmission a na wa) (hk : FloatEmission k nk wk) :
    FloatEmission (fun d => floatRoundShiftL d a k)
      (10 * na + 18 * nk + 57) (3 * (wa + wk) + 40) := by
  let q := quotient ha hk
  let back := bin q hk 11 (by decide)
  let rem := bin ha back 4 (by decide)
  let den := bin (literal 1) hk 11 (by decide)
  apply bounds (rounding q rem den) <;> omega

/-- Static emission succeeds independently of the input word's runtime value. -/
theorem continuation (F : Gleitkomma.Format) (input : Nat) :
    ∃ code top, floatOfIntContinuationL F input = some (code, top) ∧
      code.length = 63984 ∧ top ≤ input + 115 ∧
      code.all (fun i => decide (i.o < 256)) = true := by
  let source : Nat → Option (List II × Nat) := fun j => some ([ci 2 j input 0], j + 1)
  let mag := magnitude (copy input)
  let exp := exponent mag
  let threshold := konst 4 (F.p - 1)
  let cond := bin exp threshold 13 (by decide)
  let left := bin mag (bin threshold exp 4 (by decide)) 11 (by decide)
  let right := roundShift mag (bin exp threshold 4 (by decide))
  have scale : FloatEmission (fun d => floatOfIntScaleL F.p d source) 20939 112 := by
    apply bounds (branch cond left right (by decide)) <;> omega
  let sign := bin (imm (copy input) 13 (by decide) 0)
    (konst 4 (2^(F.ebits + F.fracBits))) 5 (by decide)
  let biased := bin exp (konst 4 F.bias) 3 (by decide)
  let carry := bin scale (konst 4 (2 * 2^(F.p - 1))) 14 (by decide)
  let exponent := bin biased carry 3 (by decide)
  let significand := bin scale carry 12 (by decide)
  let fraction := bin significand (konst 4 (2^(F.p - 1))) 4 (by decide)
  let upper := bin sign (bin exponent (konst 4 (2^(F.p - 1))) 5 (by decide)) 3 (by decide)
  have normal : FloatEmission
      (fun d => floatPackCarryL d
        (fun j => wordL 5 j (wordK 13 j (source j) 0)
          (some (konstWL 4 (2^(F.ebits + F.fracBits)) (j + 1))))
        (fun j => wordL 3 j (floatExponentL j (fun k => floatMagnitudeL k source))
          (some (konstWL 4 F.bias (j + 1))))
        (fun j => floatOfIntScaleL F.p j source) (2^(F.p - 1))) 63953 114 := by
    apply bounds (bin upper fraction 3 (by decide)) <;> omega
  have assembly : FloatEmission
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d source)
      63983 114 := by
    apply bounds (branch (imm mag 14 (by decide) 0) (konst 4 0) normal (by decide)) <;> omega
  obtain ⟨c, top, hs, hl, ht, ho⟩ := assembly (input + 1)
  refine ⟨c ++ [ci 2 input (input + 1) 0], top, ?_, ?_, by omega, ?_⟩
  · simp [floatOfIntContinuationL, source] at hs ⊢
    rw [hs]
    rfl
  · simp [hl]
  · simp [List.all_append, ho, ci]

#print axioms continuation

end FloatEmission
end Gabbro.Stage0.Senke
