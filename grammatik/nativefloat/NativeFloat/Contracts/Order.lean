module

public import NativeFloat.Primitives

public section

namespace RootNativeFloat.Contracts

/-- Native comparison contracts used by interval inclusion.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Order : Prop where
  nan_le : ∀ (a b : Float) (h : a.hwIsNaN = true),
      Float.hwLe a b = false

  le_nan : ∀ (a b : Float) (h : b.hwIsNaN = true),
      Float.hwLe a b = false

  le_refl : ∀ {a : Float} (ha : a.hwIsFinite = true),
      Float.hwLe a a = true

  le_trans : ∀ {a b c : Float} (ab : Float.hwLe a b = true) (bc : Float.hwLe b c = true),
      Float.hwLe a c = true

  le_upper : ∀ {a x y : Float} (ha : a.hwIsFinite = false)
      (hx : x.hwIsFinite = true) (hy : y.hwIsFinite = true) (xa : Float.hwLe x a = true),
      Float.hwLe y a = true

  lower_le : ∀ {a x y : Float} (ha : a.hwIsFinite = false)
      (hx : x.hwIsFinite = true) (hy : y.hwIsFinite = true) (ax : Float.hwLe a x = true),
      Float.hwLe a y = true

end RootNativeFloat.Contracts
