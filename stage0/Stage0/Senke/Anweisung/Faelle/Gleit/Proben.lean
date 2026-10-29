/- Full G fixtures for float forms not yet constructed by the source reader. -/
import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
import Stage0.Senke.Ausdruck.Gleit.Schluessel
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

/-- Signed zeros share a key and neither is strictly less than the other in G. -/
theorem float_signed_zero_zeuge :
    floatKey ⟨true, 0, 0⟩ = 0 ∧ floatKey ⟨false, 0, 0⟩ = 0 ∧
    gleitLt ⟨true, 0, 0⟩ ⟨false, 0, 0⟩ = false ∧
    gleitLt ⟨false, 0, 0⟩ ⟨true, 0, 0⟩ = false ∧
    gleitLe ⟨true, 0, 0⟩ ⟨false, 0, 0⟩ = true := by decide +kernel

/-- Arithmetic and integer conversion still require their software algorithms and proofs. -/
theorem float_refused_zeuge :
    lowB 1 (fun _ => 0) (layU u (fun _ => none) 0) 3 ([], 0) [] (0, 0)
      (show Body from .floatOf (.lit 42) (0, 1) (100, 1) .nil) = none ∧
    lowB 1 (fun _ => 0) (layU u (fun _ => none) 0) 3 ([], 0) [] (0, 0)
      (show Body from .floatLit (1, 1) (0, 1) (10, 1)
        (.float .add (.var .here) (.var .here) (0, 1) (10, 1) .nil)) = none := by
  decide +kernel

end Gabbro.Stage0.Senke.FloatProbe
