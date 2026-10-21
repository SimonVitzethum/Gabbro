/-
  File:      Grammatik/Gen/Zeugen/N19_5.lean
  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member 19, the cells below lie in the generator's
             space. Checked by the kernel; do not edit.
-/
import Grammatik.Gen.Abdeckung.Satz.Raum
import Grammatik.Gen.Erzeuger.Entscheidung
import Grammatik.Korpus.Zeugnis.Zeugnis.T1
import Grammatik.Gen.Zeugen.Erreicht

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Gabbro.Grammatik.Gen.Zeugen.N19_5

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := mitglieder.getD 19 {}

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  (.retWhy (⟨0, by decide⟩ : Fin _) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  (.retWhy (⟨0, by decide⟩ : Fin _) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨n + 3, h⟩ => absurd h (by have : z.fns.length = 3 := (by decide); omega)

def h0 : Haut z.deklaration := ⟨r, fun f => [false, false, false].getD f.val false⟩

def ws : List z.deklaration.Fn := [(⟨0, by decide⟩ : Fin z.fns.length), (⟨0, by decide⟩ : Fin z.fns.length)]

def P : Programm z.deklaration := h0.programm

def alle : List Zelle := [⟨0, 0, true, [true, false, false]⟩, ⟨1, 0, true, [true, false, true]⟩, ⟨1, 0, true, [true, false, false]⟩, ⟨1, 0, true, [false, false, true]⟩, ⟨1, 0, true, [false, false, false]⟩, ⟨3, 0, true, [false, false]⟩, ⟨4, 0, true, [false, false]⟩, ⟨4, 0, true, [true, true]⟩, ⟨5, 0, true, [false, true]⟩, ⟨6, 0, true, [true, false, true]⟩, ⟨6, 1, true, [true, true, false, false]⟩, ⟨6, 1, true, [true, true, false, true]⟩, ⟨6, 1, true, [true, false, true, false]⟩, ⟨6, 1, true, [true, false, false, true]⟩, ⟨6, 1, true, [true, false, true, true]⟩, ⟨6, 1, true, [true, false, false, false]⟩, ⟨7, 0, true, [false, true]⟩, ⟨7, 1, false, [true, false, false]⟩, ⟨7, 0, true, [true, true]⟩, ⟨9, 0, true, [false, true, false, false]⟩, ⟨9, 0, true, [false, false, false, false]⟩]

def bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w

theorem zellen : RaumSchlecht ncZiel erreicht bnoetig :=
  ⟨19, by rw [mitglieder_laenge]; decide, raumSchlechtIn_aus z (grenzenVon 19).1 (grenzenVon 19).2 ncZiel h0
    (fun f => (by decide : ∀ f : Fin z.fns.length, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 19).1) f) (by decide)
    (by decide) List.mem_cons_self (ws := ws) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end Gabbro.Grammatik.Gen.Zeugen.N19_5
