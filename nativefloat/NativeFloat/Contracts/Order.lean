module

public import Init.Data.Float.Float

public section

namespace RootNativeFloat.Contracts

/-- Native comparison contracts used by interval inclusion.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure Order : Prop where
  le_refl : ∀ {a : Float} (ha : a.isFinite = true),
      Float.le a a = true

  le_trans : ∀ {a b c : Float} (ab : Float.le a b = true) (bc : Float.le b c = true),
      Float.le a c = true

  le_upper : ∀ {a x y : Float} (ha : a.isFinite = false)
      (hx : x.isFinite = true) (hy : y.isFinite = true) (xa : Float.le x a = true),
      Float.le y a = true

  lower_le : ∀ {a x y : Float} (ha : a.isFinite = false)
      (hx : x.isFinite = true) (hy : y.isFinite = true) (ax : Float.le a x = true),
      Float.le a y = true

end RootNativeFloat.Contracts
