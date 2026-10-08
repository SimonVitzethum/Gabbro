/-
  File:      Grammatik/Speichermodell/OptBereich.lean
  Subject:   Lean groundwork for `option` over an ordinary range
             (agent 03, usability team).

  Finding G5 of `messung/SPRACHE-EFFIZIENZ.md`: only `option index`
  exists, so a function that may have no capacity (`frei_min :
  option Bytes`) is unwritable. The sentinel representation of
  `option index` (value `n` = none) generalises to any range
  `lo .. hi`: `none` is `hi - lo + 1` in the offset encoding. This
  file proves, over every range and with no program named: the
  encoding round trip (`optDec_optEnc`), the width fit
  (`optEnc_lt_two_pow`), injectivity (`optEnc_inj`), the sentinel
  test (`none_ausserhalb`), and the bit cost (`optBits_le_bits_succ`
  plus the free-sentinel case `optBits_gleich_wenn_luft`). No Arm
  instruction facts (rule 7 N/A, recorded in CUTS).
-/
import Grammatik.Speichermodell.Darstellung

namespace Grammatik.Speichermodell.OptBereich

open Grammatik.Speichermodell.Darstellung

/-! ## 1. Sentinel encoding over a range. -/

/-- Offset encoding with a sentinel: `none` is `hi - lo + 1`. -/
def optEnc (lo hi : Int) : Option Int → Nat
  | none => (hi - lo + 1).toNat
  | some v => enc lo v

/-- Decoding: the sentinel reads `none`. -/
def optDec (lo hi : Int) (n : Nat) : Option Int :=
  if n = (hi - lo + 1).toNat then none else some (dec lo n)

/-- Bits with the sentinel counted as one more value. -/
def optBits (lo hi : Int) : Nat := bits 0 (hi - lo + 1)

/-! ## 2. Round trip and width fit. -/

/-- **Decoding undoes encoding** on `none` and on in-range values. -/
theorem optDec_optEnc (lo hi : Int) (o : Option Int)
    (h : o = none ∨ ∃ v, o = some v ∧ lo ≤ v ∧ v ≤ hi) :
    optDec lo hi (optEnc lo hi o) = o := by
  rcases h with rfl | ⟨v, rfl, h1, h2⟩
  · simp [optEnc, optDec]
  · have hlt : enc lo v < (hi - lo + 1).toNat := by
      unfold enc
      omega
    have hne : enc lo v ≠ (hi - lo + 1).toNat := by
      intro hcon
      omega
    simp only [optEnc, optDec]
    simp [hne]
    exact dec_enc lo hi v h1 h2
/-! ## 3. Width fit and injectivity. -/

/-- **Every valid code fits the width** (ranges via `enc_lt_two_pow`,
    the sentinel as a range value itself). -/
theorem optEnc_lt_two_pow (lo hi : Int) (o : Option Int)
    (h : o = none ∨ ∃ v, o = some v ∧ lo ≤ v ∧ v ≤ hi) :
    optEnc lo hi o < 2 ^ optBits lo hi := by
  rcases h with rfl | ⟨v, rfl, h1, h2⟩
  · simp only [optEnc, optBits]
    by_cases hnn : 0 ≤ hi - lo + 1
    · have e0 : (hi - lo + 1).toNat = enc 0 (hi - lo + 1) := by
        unfold enc
        congr 1
        omega
      rw [e0]
      exact enc_lt_two_pow 0 _ _ hnn (by omega)
    · have hpos : 0 < 2 ^ bits 0 (hi - lo + 1) := Nat.two_pow_pos _
      have h0 : (hi - lo + 1).toNat = 0 := by omega
      omega
  · have e : enc lo v = enc 0 (v - lo) := by
      unfold enc
      congr 1
      omega
    simp only [optEnc, optBits]
    rw [e]
    exact enc_lt_two_pow 0 _ _
      (by omega) (by omega)

/-- **Codes are pairwise distinct** on `none` and in-range values. -/
theorem optEnc_inj (lo hi : Int) (o₁ o₂ : Option Int)
    (h₁ : o₁ = none ∨ ∃ v, o₁ = some v ∧ lo ≤ v ∧ v ≤ hi)
    (h₂ : o₂ = none ∨ ∃ v, o₂ = some v ∧ lo ≤ v ∧ v ≤ hi)
    (heq : optEnc lo hi o₁ = optEnc lo hi o₂) : o₁ = o₂ := by
  rcases h₁ with rfl | ⟨v₁, rfl, h1l, h1h⟩ <;>
    rcases h₂ with rfl | ⟨v₂, rfl, h2l, h2h⟩
  · rfl
  · simp only [optEnc] at heq
    have hlt : enc lo v₂ < (hi - lo + 1).toNat := by
      unfold enc
      omega
    exfalso
    omega
  · simp only [optEnc] at heq
    have hlt : enc lo v₁ < (hi - lo + 1).toNat := by
      unfold enc
      omega
    exfalso
    omega
  · simp only [optEnc] at heq
    have h12 : v₁ = v₂ := by
      have e1 : enc lo v₁ = enc lo v₂ := heq
      unfold enc at e1
      omega
    rw [h12]

/-- **The sentinel is not a value code**: a compare-with-sentinel
    test decides `isNone` exactly. -/
theorem none_ausserhalb (lo hi : Int) (v : Int)
    (h1 : lo ≤ v) (h2 : v ≤ hi) :
    (hi - lo + 1).toNat ≠ enc lo v := by
  have hlt : enc lo v < (hi - lo + 1).toNat := by
    unfold enc
    omega
  omega

/-! ## 4. Bit cost: at most one extra bit, free with slack. -/

/-- **An option costs at most one extra bit.** -/
theorem optBits_le_bits_succ (lo hi : Int) :
    optBits lo hi ≤ bits lo hi + 1 := by
  unfold optBits
  apply bits_minimal
  have h1 : anzahl 0 (hi - lo + 1) ≤ anzahl lo hi + 1 := by
    unfold anzahl
    omega
  have h2 : anzahl lo hi ≤ 2 ^ bits lo hi :=
    anzahl_le_two_pow_bits lo hi
  have h4 : 2 ^ (bits lo hi + 1) = 2 ^ bits lo hi + 2 ^ bits lo hi := by
    rw [Nat.pow_succ]
    omega
  have h3 : 1 ≤ 2 ^ bits lo hi := Nat.two_pow_pos _
  omega

/-- **The sentinel is FREE when the range does not fill its power of
    two**: the none code fits in the same width. -/
theorem optBits_gleich_wenn_luft (lo hi : Int)
    (h : anzahl lo hi < 2 ^ bits lo hi) :
    optBits lo hi = bits lo hi := by
  unfold optBits
  have h1 : bits 0 (hi - lo + 1) ≤ bits lo hi := by
    apply bits_minimal
    have ha : anzahl 0 (hi - lo + 1) ≤ anzahl lo hi + 1 := by
      unfold anzahl
      omega
    have h2 : anzahl lo hi ≤ 2 ^ bits lo hi :=
      anzahl_le_two_pow_bits lo hi
    omega
  have h2 : bits lo hi ≤ bits 0 (hi - lo + 1) := by
    apply bits_minimal
    have ha : anzahl lo hi ≤ anzahl 0 (hi - lo + 1) := by
      unfold anzahl
      omega
    have h3 := anzahl_le_two_pow_bits 0 (hi - lo + 1)
    omega
  omega

/-! ## 5. Witnesses: the audit shapes, decided. -/

/-- Range `0 .. 99`: 7 bits, free sentinel, none code 100. -/
theorem wit_bits099 : optBits 0 99 = 7 := by decide

/-- The none code of `0 .. 99` is 100. -/
theorem wit_none099 : optEnc 0 99 none = 100 := by decide

/-- Range `0 .. 127`: 7 range bits, 8 with sentinel (full). -/
theorem wit_bits0127 : optBits 0 127 = 8 := by decide

/-- `some 5` in `3 .. 9` encodes as 2, none code 7. -/
theorem wit_enc5 : optEnc 3 9 (some 5) = 2 := by decide

/-- The none code of `3 .. 9` is 7. -/
theorem wit_none39 : optEnc 3 9 none = 7 := by decide

/-- Round trip at `some 5`. -/
theorem wit_round5 : optDec 3 9 (optEnc 3 9 (some 5)) = some 5 := by decide

/-- Round trip at `none`. -/
theorem wit_roundNone : optDec 3 9 (optEnc 3 9 none) = none := by decide

end Grammatik.Speichermodell.OptBereich

/-
CUTS: what is not proved or not covered.
  - Proved: the sentinel encoding over ranges (`optEnc`/`optDec`),
    the round trip (`optDec_optEnc`), the width fit
    (`optEnc_lt_two_pow`), injectivity (`optEnc_inj`), the sentinel
    test (`none_ausserhalb`), the bit cost (`optBits_le_bits_succ`,
    `optBits_gleich_wenn_luft`), and decide witnesses for the audit
    shapes (0..99 free at 7 bits, 0..127 full at 8, round trips).
  - The `Ty.opt` bridge (task item (5)) is SKIPPED, not one line:
    the stated target `.opt (n-1)` is off by one — the true
    correspondence is `optBits 0 (n-1) = tyBits (.opt n)` and
    `optEnc 0 (n-1) none = encW (.opt n) none` (both need `0 ≤ n`
    for the `toNat`), which is a small theorem, not a definitional
    coincidence. Recorded for whoever takes the `option <range>`
    language form.
  - NOT proved: syntax, checker or exporter forms (no
    `option <range type>` surface; the language form needs a
    parser/grammar decision by Simon).
  - Rule 7 (Sail citations) is N/A: pure `Int`/`Nat`/`Option`
    encoding logic, no Arm instruction semantics (confidence:
    definitional — the file states no fact about any machine).
-/

#print axioms Grammatik.Speichermodell.OptBereich.optDec_optEnc
#print axioms Grammatik.Speichermodell.OptBereich.optEnc_lt_two_pow
#print axioms Grammatik.Speichermodell.OptBereich.optEnc_inj
#print axioms Grammatik.Speichermodell.OptBereich.none_ausserhalb
#print axioms Grammatik.Speichermodell.OptBereich.optBits_le_bits_succ
#print axioms Grammatik.Speichermodell.OptBereich.optBits_gleich_wenn_luft
#print axioms Grammatik.Speichermodell.OptBereich.wit_bits099
#print axioms Grammatik.Speichermodell.OptBereich.wit_none099
#print axioms Grammatik.Speichermodell.OptBereich.wit_bits0127
#print axioms Grammatik.Speichermodell.OptBereich.wit_enc5
#print axioms Grammatik.Speichermodell.OptBereich.wit_none39
#print axioms Grammatik.Speichermodell.OptBereich.wit_round5
#print axioms Grammatik.Speichermodell.OptBereich.wit_roundNone
