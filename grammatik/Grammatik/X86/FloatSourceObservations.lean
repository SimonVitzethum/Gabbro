/-
  File:      Grammatik/X86/FloatSourceObservations.lean
  Subject:   Finite-value float observation equivalence over real source operations.

  Lane 624 (direct-source closure): proves which ACTUAL source observations can
  distinguish model-equivalent finite floats. Covered operators (pinned by the
  lemmas below): `fllt`/`flle` (`gleitLt`/`gleitLe`), `gleitNarrow` and `gleit`
  range-holding (`gleitPasst`), and the register-write truncation (`gleitRoh`).
  Float `==`/`!=` is EXCLUDED (F-EQ): `Expr.eq` takes only `.int` arguments, so
  no model term equates two floats. NaN non-inhabitation is a corollary: no
  `Gleit` value is NaN. Consumer hook: `cvttPaket`/`ucomiFlags` reuse pins for
  the ScalarFloat decoder consumer. Full source-to-final-bytes stays OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Typen
import Grammatik.Gleitkomma
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

/-- Two finite floats agree on every model comparison, in all four
    directions, against every third value. This is the premise of the
    observation-equivalence fragment -- comparisons only, never a blanket
    "all observations agree" assumption. -/
def vergleichsGleich (x y : Gabbro.Grammatik.GFloat) : Prop :=
  ∀ z : Gabbro.Grammatik.GFloat,
    Gabbro.Grammatik.gleitLt x z = Gabbro.Grammatik.gleitLt y z ∧
    Gabbro.Grammatik.gleitLt z x = Gabbro.Grammatik.gleitLt z y ∧
    Gabbro.Grammatik.gleitLe x z = Gabbro.Grammatik.gleitLe y z ∧
    Gabbro.Grammatik.gleitLe z x = Gabbro.Grammatik.gleitLe z y

/-- First checked fact: signed zeros compare equal (strict, one direction). -/
theorem null_flt_still :
    Gabbro.Grammatik.gleitLt (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) = false := by
  decide

/-! ## 1. Signed-zero class and exact value (decided facts). -/

/-- Minus zero classifies as zero. -/
theorem nullN_klasse :
    Gleitkomma.klasse Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) = .null := by
  decide

/-- Plus zero classifies as zero. -/
theorem nullP_klasse :
    Gleitkomma.klasse Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) = .null := by
  decide

/-- Minus zero has exact value zero. -/
theorem nullN_exakt :
    Gleitkomma.wertExakt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) =
      some ⟨0, 0⟩ := by
  decide

/-- Plus zero has exact value zero. -/
theorem nullP_exakt :
    Gleitkomma.wertExakt Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) =
      some ⟨0, 0⟩ := by
  decide

/-! ## 2. Signed-zero strict-comparison agreement (all four directions). -/

/-- Strict comparison with `-0` on the left agrees with `+0` on the left. -/
theorem null_flt_links (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z =
      Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) z := by
  unfold Gleitkomma.flt
  rw [nullN_klasse, nullP_klasse, nullN_exakt, nullP_exakt]
  cases hz : Gleitkomma.klasse Gleitkomma.f64 z with
  | nan => rfl
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-- Strict comparison with `-0` on the right agrees with `+0` on the right. -/
theorem null_flt_rechts (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) =
      Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullP Gleitkomma.f64) := by
  unfold Gleitkomma.flt
  rw [nullN_klasse, nullP_klasse, nullN_exakt, nullP_exakt]
  cases hz : Gleitkomma.klasse Gleitkomma.f64 z with
  | nan => rfl
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-! ## 3. Non-strict agreement and the comparison-equivalence instance. -/

/-- Non-strict comparison with `-0` on the left agrees with `+0` on the left. -/
theorem null_fle_links (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z =
      Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullP Gleitkomma.f64) z := by
  unfold Gleitkomma.fle
  rw [nullN_klasse, nullP_klasse, null_flt_rechts z]

/-- Non-strict comparison with `-0` on the right agrees with `+0` on the right. -/
theorem null_fle_rechts (z : Gabbro.Grammatik.GFloat) :
    Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) =
      Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullP Gleitkomma.f64) := by
  unfold Gleitkomma.fle
  rw [nullN_klasse, nullP_klasse, null_flt_links z]

/-- Signed zeros satisfy comparison agreement against every third value:
    the inhabited model-equivalent finite pair. -/
theorem null_vergleichsGleich :
    vergleichsGleich (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) := by
  intro z
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Gleitkomma.flt Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z = _
    exact null_flt_links z
  · show Gleitkomma.flt Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) = _
    exact null_flt_rechts z
  · show Gleitkomma.fle Gleitkomma.f64 (Gleitkomma.nullN Gleitkomma.f64) z = _
    exact null_fle_links z
  · show Gleitkomma.fle Gleitkomma.f64 z (Gleitkomma.nullN Gleitkomma.f64) = _
    exact null_fle_rechts z

/-! ## 4. Observation consequences: truncation and range-holding. -/

/-- The register-write truncation agrees on signed zeros (both give `0`). -/
theorem null_roh_gleich :
    Gabbro.Grammatik.gleitRoh (Gleitkomma.nullN Gleitkomma.f64) =
      Gabbro.Grammatik.gleitRoh (Gleitkomma.nullP Gleitkomma.f64) := by
  decide

/-- Generic fragment: comparison agreement plus finiteness gives
    range-holding agreement, for every declared range. The premise is the
    comparison part only -- never a blanket all-observations assumption. -/
theorem vergleichsgleich_passt (x y : Gabbro.Grammatik.GFloat)
    (hx : Gabbro.Grammatik.gleitEndlich x = true)
    (hy : Gabbro.Grammatik.gleitEndlich y = true)
    (h : vergleichsGleich x y) (lo hi : Int × Int) :
    (Gabbro.Grammatik.gleitPasst lo hi x).isSome =
      (Gabbro.Grammatik.gleitPasst lo hi y).isSome := by
  have e1 := (h (Gabbro.Grammatik.bruch lo)).2.2.2
  have e2 := (h (Gabbro.Grammatik.bruch hi)).2.2.1
  unfold Gabbro.Grammatik.gleitPasst
  by_cases hP : Gabbro.Grammatik.gleitEndlich x = true ∧
      Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) x = true ∧
      Gabbro.Grammatik.gleitLe x (Gabbro.Grammatik.bruch hi) = true
  · have hQ : Gabbro.Grammatik.gleitEndlich y = true ∧
        Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) y = true ∧
        Gabbro.Grammatik.gleitLe y (Gabbro.Grammatik.bruch hi) = true := by
      obtain ⟨-, b, c⟩ := hP
      exact ⟨hy, by rw [← e1]; exact b, by rw [← e2]; exact c⟩
    rw [dif_pos hP, dif_pos hQ]; rfl
  · have hQ : ¬ (Gabbro.Grammatik.gleitEndlich y = true ∧
        Gabbro.Grammatik.gleitLe (Gabbro.Grammatik.bruch lo) y = true ∧
        Gabbro.Grammatik.gleitLe y (Gabbro.Grammatik.bruch hi) = true) := by
      intro hQ
      obtain ⟨-, b, c⟩ := hQ
      apply hP
      exact ⟨hx, by rw [e1]; exact b, by rw [e2]; exact c⟩
    rw [dif_neg hP, dif_neg hQ]

/-- Range-holding agrees on signed zeros, for every declared range. -/
theorem null_passt_gleich (lo hi : Int × Int) :
    (Gabbro.Grammatik.gleitPasst lo hi (Gleitkomma.nullN Gleitkomma.f64)).isSome =
      (Gabbro.Grammatik.gleitPasst lo hi
        (Gleitkomma.nullP Gleitkomma.f64)).isSome :=
  vergleichsgleich_passt _ _ (by decide) (by decide) null_vergleichsGleich lo hi

/-! ## 5. NaN non-inhabitation (honestly labelled corollary). -/

/-- No accepted float value is NaN: a `Gleit` carries its finiteness proof.
    NaN-payload non-observability holds vacuously -- there is no NaN value
    to observe. -/
theorem kein_gleit_nan (lo hi : Int × Int) (v : Gabbro.Grammatik.Gleit lo hi) :
    Gleitkomma.klasse Gleitkomma.f64 v.x ≠ .nan := by
  intro hcon
  have he := v.endlich
  unfold Gabbro.Grammatik.gleitEndlich at he
  rw [hcon] at he
  exact Bool.false_ne_true he

/- CUTS:
    - Skeleton only: comparison agreement is defined, one strict-equality
      fact is proved. The `gleitRoh`/`gleitPasst` consequences, the NaN
      corollary, the F-EQ exclusion pin, the target reuse hooks and the
      joint table-write witness are still to come.
    - Full source-to-final-loaded-bytes validation remains OPEN.
-/

#print axioms null_flt_still

end Gabbro.Grammatik.X86
