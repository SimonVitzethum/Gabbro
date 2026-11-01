module

public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1
public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gleitkomma

/-- Division of finite values by a nonzero finite divisor with in-range
    exact quotient stays finite (and is the rounded exact quotient).
    `0 / 0` is NaN, so the divisor must be nonzero (`hkb`, `hv`). -/
theorem div_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hkb : klasse F b = .normal ∨ klasse F b = .subnormal)
    (hv : v.zaehler ≠ 0)
    (hob : (divBruch u v).zaehler.natAbs
      < (divBruch u v).nenner * 2 ^ F.emax) :
    klasse F (div F a b) = .normal ∨ klasse F (div F a b) = .subnormal
      ∨ klasse F (div F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hdD : 0 < (divBruch u v).nenner := by
    rw [divBruch_nenner]
    have h1 : 0 < v.zaehler.natAbs := by omega
    have h2 : 0 < 2 ^ (v.zweierExp
        - (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat :=
      Nat.pow_pos (show 0 < 2 by decide)
    exact Nat.mul_pos h1 h2
  have hfin : klasse F (rundeBruch F (divBruch u v)) = .normal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .subnormal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .null :=
    rundeBruch_finite F _ hF hdD hob
  generalize hka : klasse F a = ka
  cases hkb with
  | inl hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)
  | inr hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)

/-! ## Witnesses: concrete vectors by `decide`.

  Every vector below is a kernel computation (`decide`/`rfl`-checkable,
  no `native_decide`): the model rounds exactly like IEEE-754 hardware on
  fractions, ties, subnormals and overflow. The subnormal/overflow vectors
  evaluate `2 ^ 1074`-scale naturals through ~1100 structural steps, past
  both default elaborator limits, hence the two options (elaboration-only,
  no soundness content). -/

set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
theorem zeuge_ebits32 : f32.ebits = 8 := by decide

theorem zeuge_ebits64 : f64.ebits = 11 := by decide

theorem zeuge_zehntel64 :
    zuBits f64 (ofRat f64 1 10) = 0x3FB999999999999A := by decide

theorem zeuge_zweiZehntel64 :
    zuBits f64 (ofRat f64 2 10) = 0x3FC999999999999A := by decide

/-- `0.1 + 0.2 = 0.30000000000000004`: the famous `0x3FD3333333333334`. -/
theorem zeuge_add01 :
    zuBits f64 (add f64 (ofRat f64 1 10) (ofRat f64 2 10))
      = 0x3FD3333333333334 := by decide


end Gabbro.Grammatik.Gleitkomma
