/-
  File:      Grammatik/Gen/Zeugen/N47_20.lean
  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member 47, the cells below lie in the generator's
             space. Checked by the kernel; do not edit.
-/
import Grammatik.Gen.Abdeckung.Satz.Raum
import Grammatik.Gen.Erzeuger.Entscheidung
import Grammatik.Korpus.Zeugnis.Zeugnis.T1
import Grammatik.Gen.Zeugen.Erreicht

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Gabbro.Grammatik.Gen.Zeugen.N47_20

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := mitglieder.getD 47 {}

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  (.cons (.callInd (.fnref (⟨0, by decide⟩ : Fin z.fns.length) 0 (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by have : z.fns.length = 2 := (by decide); omega)

def h0 : Haut z.deklaration := ⟨r, fun f => [false, false].getD f.val false⟩

def ws : List z.deklaration.Fn := [(⟨0, by decide⟩ : Fin z.fns.length)]

def fv : z.deklaration.Fn := (⟨0, by decide⟩ : Fin z.fns.length)

def vr : Expr z.deklaration (z.deklaration.params fv)
    (Signatur.anfang z.deklaration (z.deklaration.signatur fv)) .bool :=
  (Expr.glob (D := z.deklaration) (⟨0, by decide⟩ : Fin z.globs.length) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))

def P : Programm z.deklaration :=
  { h0.programm with requires := fun g => if hg : g = fv then hg ▸ vr else Expr.tru }

theorem vr_klein : @groesseExpr z.deklaration z.zahlen _ _ _ vr ≤ ncZiel := by decide

theorem vr_endlich : @groesseExpr z.deklaration z.zahlen _ _ _ vr < unendlich := by decide

def alle : List Zelle := [⟨0, 0, true, [true, false, false]⟩, ⟨0, 0, true, [true, true, true]⟩, ⟨1, 0, true, [true, false, true]⟩, ⟨1, 0, true, [true, false, false]⟩, ⟨1, 0, true, [false, true, true]⟩, ⟨1, 0, true, [false, false, false]⟩, ⟨1, 0, true, [true, true, true]⟩, ⟨2, 0, true, [false, true, false, false]⟩, ⟨2, 2, false, [true, true, false]⟩, ⟨2, 3, false, [true, true, false]⟩, ⟨3, 0, true, [false, false]⟩, ⟨4, 0, true, [false, false]⟩, ⟨4, 0, true, [true, true]⟩, ⟨5, 0, true, [false, false]⟩, ⟨6, 0, true, [false, false, false]⟩, ⟨6, 1, true, [false, true, false, false]⟩, ⟨6, 1, true, [false, true, false, true]⟩, ⟨6, 1, true, [false, false, true, false]⟩, ⟨6, 1, true, [false, false, false, true]⟩, ⟨6, 1, true, [false, false, false, false]⟩, ⟨7, 0, true, [false, true]⟩, ⟨7, 1, false, [true, false, false]⟩, ⟨7, 0, true, [true, true]⟩, ⟨7, 1, false, [true, false, true]⟩, ⟨8, 0, true, [false, false, true]⟩, ⟨8, 0, true, [false, false, false]⟩, ⟨9, 0, true, [false, true, false, false]⟩, ⟨9, 0, true, [false, true, false, true]⟩, ⟨9, 0, true, [false, false, false, false]⟩, ⟨9, 0, true, [false, false, false, true]⟩]

def bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w

theorem zellen : RaumSchlecht ncZiel erreicht bnoetig :=
  ⟨47, by rw [mitglieder_laenge]; decide, raumSchlechtIn_aus z (grenzenVon 47).1 (grenzenVon 47).2 ncZiel h0
    (fun f => (by decide : ∀ f : Fin z.fns.length, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 47).1) f) (by decide)
    (by decide) (vertragsL_req z ncZiel h0 fv vr vr_klein vr_endlich) (ws := ws) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end Gabbro.Grammatik.Gen.Zeugen.N47_20
