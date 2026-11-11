/-
  File:      Grammatik/Gen/Zeugen/N/N47_P.lean
  Subject:   HAND-WRITTEN witness of member 47 for the fragment cell [true, true, true] (an indirect call
             through a type a function fits, whose contract carrier lies outside the caller's footprint).
             It replaces the generated `N47_20`, whose program (a `requires` on the function whose own
             pointer type is called) cannot be written in source text since pointer types carry contracts.
             Here `fn0` ensures the static `g1` and `fn1` calls through `&fn1` and `&fn0`; the source
             text `PText` calls through `&fn1` alone and has the same cells, because the front end admits
             `fn0` as a value of the pointer type of `fn1`. Checked by the kernel.
-/
module
public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1
public import Grammatik.Gen.Zeugen.Erreicht
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Gabbro.Grammatik.Gen.Zeugen.N47_P

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- The side conditions of a generated term, as the generator's witnesses discharge them. -/
local macro "prf" : term =>
  `(by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

abbrev z : Spez := mitglieder.getD 47 {}

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  (.ret .empty prf)

/-- `fn1` calls through the pointer type of `fn0`. -/
def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  (.cons (.callInd (.fnref (⟨0, by decide⟩ : Fin z.fns.length) 0 prf) .nil prf prf)
    (.ret .empty prf))


def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by have : z.fns.length = 2 := (by decide); omega)

def h0 : Haut z.deklaration := ⟨r, fun f => [false, false].getD f.val false⟩

def ws : List z.deklaration.Fn := [(⟨0, by decide⟩ : Fin z.fns.length)]

def fv : z.deklaration.Fn := (⟨0, by decide⟩ : Fin z.fns.length)

/-- The planted contract: `fn0` ensures the plain static `g1`. -/
def ve : Expr z.deklaration (ErgCtx (z.deklaration.params fv) (z.deklaration.erg fv))
    (vertragVon z.deklaration fv).ende .bool :=
  (Expr.glob (D := z.deklaration) (⟨1, by decide⟩ : Fin z.globs.length) prf)

def P : Programm z.deklaration :=
  { h0.programm with ensures := fun g => if hg : g = fv then hg ▸ ve else Expr.tru }

theorem ve_klein : @groesseExpr z.deklaration z.zahlen _ _ _ ve ≤ ncZiel := by decide

theorem ve_endlich : @groesseExpr z.deklaration z.zahlen _ _ _ ve < unendlich := by decide

/-- The test as a program of the source. -/
def e : Einsatz := z.einsatz P ws (by decide) (by decide)

def alle : List Zelle := e.zellen

def bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w

theorem zellen : RaumSchlecht ncZiel erreicht bnoetig :=
  ⟨47, by rw [mitglieder_laenge]; decide, raumSchlechtIn_aus z (grenzenVon 47).1 (grenzenVon 47).2 ncZiel h0
    (fun f => (by decide +kernel : ∀ f : Fin z.fns.length, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 47).1) f) (by decide)
    (by decide +kernel) (vertragsL_ens z ncZiel h0 fv ve ve_klein ve_endlich) (ws := ws) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem e_gueltig : e.gueltig = false := by decide +kernel

theorem e_gedeckt : gedeckt erreicht bnoetig e.zellen = true := by decide +kernel

/-- The only cell the witness is needed for. -/
theorem bnoetig_zelle : ∀ w ∈ bnoetig, w = ⟨0, 0, true, [true, true, true]⟩ := by decide +kernel

end Gabbro.Grammatik.Gen.Zeugen.N47_P
