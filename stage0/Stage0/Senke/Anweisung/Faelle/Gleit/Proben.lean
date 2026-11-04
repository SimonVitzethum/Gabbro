/- Full G fixtures for float forms not yet constructed by the source reader. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
public import Stage0.Senke.Gleit.Native.Values
@[expose] public section

namespace Gabbro.Stage0.Senke.FloatProbe
open Gabbro.Grammatik ControlProbe Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Body := Block D (vertragVon D entry) false [] [] []

def returnBlock {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Block D (vertragVon D entry) false Γ [] [] :=
  .cons (.ret (.val (.widen hl hh (.lit n))) (.refl [])) .nil

def literal (q lo hi : Int × Int) : Body :=
  .floatLit q lo hi (returnBlock 7 (by decide) (by decide))

def compare (a b : Int × Int) (le : Bool := false) : Body :=
  .floatLit a (-10, 1) (10, 1) (.floatLit b (-10, 1) (10, 1)
    (.cons (.ite
      (if le then .flle (.var (.there .here)) (.var .here)
       else .fllt (.var (.there .here)) (.var .here))
      (returnBlock 7 (by decide) (by decide))
      (returnBlock 41 (by decide) (by decide))) .nil))

def narrow (q lo hi : Int × Int) : Body :=
  .floatLit q (-10, 1) (10, 1) (.floatNarrow (.var .here) lo hi
    (retN 41 (by decide) (by decide)) (returnBlock 7 (by decide) (by decide)))

def images : List (String × Except String (List Runner.B) × Nat) :=
  [("float-literal-half", blockImageOf (literal (3, 2) (0, 1) (10, 1)), 7),
   ("float-literal-negative", blockImageOf (literal (-3, 2) (-10, 1) (10, 1)), 7),
   ("float-literal-wide", blockImageOf (literal (2^40, 1) (0, 1) (2^41, 1)), 7),
   ("float-literal-subnormal", blockImageOf (literal (1, 2^1074) (0, 1) (1, 1)), 7),
   ("float-literal-range", blockImageOf (literal (12, 1) (0, 1) (10, 1)), 107),
   ("float-literal-nan", blockImageOf (literal (0, 0) (-10, 1) (10, 1)), 107),
   ("float-literal-infinity", blockImageOf (literal (2^1024, 1) (-10, 1) (10, 1)), 107),
   ("float-lt", blockImageOf (compare (3, 2) (2, 1)), 7),
   ("float-lt-reverse", blockImageOf (compare (2, 1) (3, 2)), 41),
   ("float-lt-equal", blockImageOf (compare (3, 2) (3, 2)), 41),
   ("float-le-equal", blockImageOf (compare (3, 2) (3, 2) true), 7),
   ("float-le-reverse", blockImageOf (compare (2, 1) (3, 2) true), 41),
   ("float-lt-negative", blockImageOf (compare (-2, 1) (-1, 1)), 7),
   ("float-lt-negative-reverse", blockImageOf (compare (-1, 1) (-2, 1)), 41),
   ("float-lt-cross-sign", blockImageOf (compare (-1, 1) (1, 1)), 7),
   ("float-lt-zero", blockImageOf (compare (0, 1) (0, 1)), 41),
   ("float-le-zero", blockImageOf (compare (0, 1) (0, 1) true), 7),
   ("float-lt-subnormal", blockImageOf (compare (1, 2^1074) (2, 2^1074)), 7),
   ("float-narrow-inside", blockImageOf (narrow (1, 1) (0, 1) (2, 1)), 7),
   ("float-narrow-lower", blockImageOf (narrow (0, 1) (0, 1) (2, 1)), 7),
   ("float-narrow-upper", blockImageOf (narrow (2, 1) (0, 1) (2, 1)), 7),
   ("float-narrow-below", blockImageOf (narrow (-1, 1) (0, 1) (2, 1)), 41),
   ("float-narrow-above", blockImageOf (narrow (3, 1) (0, 1) (2, 1)), 41),
   ("float-narrow-empty", blockImageOf (narrow (1, 1) (2, 1) (0, 1)), 41),
   ("float-narrow-unbounded", blockImageOf (narrow (1, 1) (-(2^1024), 1) (2^1024, 1)), 7),
   ("float-narrow-infinite-lower", blockImageOf (narrow (1, 1) (2^1024, 1) (2^1024, 1)), 41),
   ("float-narrow-infinite-upper", blockImageOf (narrow (1, 1) (-(2^1024), 1) (-(2^1024), 1)), 41),
   ("float-narrow-nan-lower", blockImageOf (narrow (1, 1) (0, 0) (2, 1)), 41),
   ("float-narrow-nan-upper", blockImageOf (narrow (1, 1) (0, 1) (0, 0)), 41),
   ("float-literal-max-finite", blockImageOf (literal (2^1024 - 2^971, 1) (-(2^1024), 1) (2^1024, 1)), 7)]

/-- Nonempty programs jointly exercise literal binding, both comparisons and both range arms. -/
theorem float_lowering_zeuge : images.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- Direct ending continuations retain computed conversion, arithmetic and both
    narrowing branches through the ordinary complete image pipeline. -/
def ending (n : Int) : Endblock D (vertragVon D entry) false [] [] :=
  .bind (.add (.lit n) (.lit 1))
    (.floatOf (.var .here) (-10, 1) (10, 1)
      (.floatLit (1, 1) (-10, 1) (10, 1)
        (.float .add (.var .here) (.var (.there .here)) (-20, 1) (20, 1)
          (.floatNarrow (.var .here) (0, 1) (5, 1)
            (retN 41 (by decide) (by decide)) (retN 7 (by decide) (by decide))))))

def endingImages : List (String × Except String (List Runner.B) × Nat) :=
  [("float-end-inside", imageOf (ending 1), 7),
   ("float-end-fallback", imageOf (ending 8), 41),
   ("float-end-range-failure", imageOf (ending 20), 107)]

theorem float_end_image_zeuge : endingImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- The complete canonical outcomes retain the world and exact return payload;
    out-of-range conversion remains the existing IEEE range failure. -/
theorem float_end_semantics_zeuge (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) (σ : World D) :
    execEnd O passes R (ending 1) σ .nil =
        .zurueck σ (⟨7, by decide, by decide⟩ : Zahl 0 100) ∧
    execEnd O passes R (ending 8) σ .nil =
        .zurueck σ (⟨41, by decide, by decide⟩ : Zahl 0 100) ∧
    execEnd O passes R (ending 20) σ .nil = .logik .bereich := by
  constructor
  · cbv
  · constructor <;> cbv

/-- Native signed zeros retain their bits and the canonical ordered semantics. -/
theorem float_signed_zero_zeuge :
    (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 ∧
    (Float.ofBits 0).toBits = 0 ∧
    gleitLt (Float.ofBits 0x8000000000000000) (Float.ofBits 0) = false ∧
    gleitLt (Float.ofBits 0) (Float.ofBits 0x8000000000000000) = false ∧
    gleitLe (Float.ofBits 0x8000000000000000) (Float.ofBits 0) = true := by decide +kernel

end Gabbro.Stage0.Senke.FloatProbe
