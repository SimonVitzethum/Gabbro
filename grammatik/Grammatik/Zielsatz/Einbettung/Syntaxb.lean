module
public import Grammatik.Zielsatz.Einbettung.Syntax
@[expose] public section

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable {E : Einbettung D D'}

/-! ## A function's contracts and body -/

/-- The `requires` of `f`, as the `requires` of its image. -/
def requiresE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Expr D' (D'.params (E.fn f)) (Signatur.anfang D' (D'.signatur (E.fn f))) .bool :=
  Expr.umΓ (paramsE hS f) (Expr.umΛ (anfangE_fn hS f) (exE E (P.requires f)))

/-- The `ensures` of `f`, as the `ensures` of its image. -/
def ensuresE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Expr D' (ErgCtx (D'.params (E.fn f)) (D'.erg (E.fn f))) (vertragVon D' (E.fn f)).ende .bool :=
  Expr.umΓ (by rw [E.ergCtxE, paramsE hS f, ergE_fn hS f])
    (Expr.umΛ (by rw [E.endeE, vertragVonE hS f]) (exE E (P.ensures f)))

/-- The body of `f`, as the body of its image. -/
def rumpfE (hS : E.SigTreu) (P : Programm D) (f : D.Fn) :
    Endblock D' (vertragVon D' (E.fn f)) false (D'.params (E.fn f))
      (Signatur.anfang D' (D'.signatur (E.fn f))) :=
  Endblock.umV (vertragVonE hS f)
    (Endblock.umΓ (paramsE hS f) (Endblock.umΛ (anfangE_fn hS f) (exEnd hS (P.rumpf f))))

/-- An invariant's predicate. -/
def invarianteE (P : Programm D) (i : D.Inv) : Expr D' [] (invSicht D' (E.inv i)) .bool :=
  Expr.umΛ (E.invSichtE i) (exE E (P.invariante i))

/-- **`P'` continues `P` along the embedding**: every function of `D` has, at its image, the
    translated contracts and body, every invariant of `D` the translated predicate, and the same
    dispatch fact. -/
structure Fortsetzung (hS : E.SigTreu) (P : Programm D) (P' : Programm D') : Prop where
  requires : ∀ f, P'.requires (E.fn f) = requiresE hS P f
  ensures : ∀ f, P'.ensures (E.fn f) = ensuresE hS P f
  rumpf : ∀ f, P'.rumpf (E.fn f) = rumpfE hS P f
  invariante : ∀ i, P'.invariante (E.inv i) = invarianteE P i
  unterbricht : ∀ f, P'.unterbricht (E.fn f) = P.unterbricht f

end Einbettung
end Gabbro.Grammatik.Einbettung
