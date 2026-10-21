/-
  File:      Grammatik/Gen/Zeugen/N23_4.lean
  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member 23, the cells below lie in the generator's
             space. Checked by the kernel; do not edit.
-/
import Grammatik.Gen.Abdeckung.Satz.Raum
import Grammatik.Gen.Erzeuger.Entscheidung
import Grammatik.Korpus.Zeugnis.Zeugnis.T1
import Grammatik.Gen.Zeugen.Erreicht

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Gabbro.Grammatik.Gen.Zeugen.N23_4

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := mitglieder.getD 23 {}

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  (.cons (.locks (⟨0, by decide⟩ : Fin z.locks.length) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.regRead (⟨0, by decide⟩ : Fin z.regs.length) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) .nil)) (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨n + 1, h⟩ => absurd h (by have : z.fns.length = 1 := (by decide); omega)

def h0 : Haut z.deklaration := ⟨r, fun f => [false].getD f.val false⟩

def ws : List z.deklaration.Fn := [(⟨0, by decide⟩ : Fin z.fns.length), (⟨0, by decide⟩ : Fin z.fns.length)]

def P : Programm z.deklaration := h0.programm

def alle : List Zelle := [⟨0, 0, true, [true, false, false]⟩, ⟨1, 0, true, [true, false, true]⟩, ⟨2, 1, true, [false, false]⟩, ⟨2, 2, false, [false, true, true]⟩, ⟨3, 0, true, [true, true]⟩, ⟨3, 0, true, [false, true]⟩, ⟨4, 0, true, [false, false]⟩, ⟨4, 0, true, [true, true]⟩, ⟨5, 0, true, [false, false]⟩, ⟨6, 0, true, [true, false, false]⟩, ⟨6, 1, true, [true, true, false, false]⟩, ⟨6, 1, true, [true, true, true, true]⟩, ⟨6, 1, true, [true, true, false, true]⟩, ⟨7, 0, true, [false, true]⟩, ⟨7, 1, false, [true, false, false]⟩, ⟨7, 0, true, [true, true]⟩, ⟨7, 1, false, [true, true, true]⟩, ⟨8, 0, true, [true, false, true]⟩, ⟨8, 0, true, [false, false, false]⟩, ⟨9, 0, true, [false, true, true, false]⟩, ⟨9, 0, true, [false, true, false, true]⟩]

def bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w

theorem zellen : RaumSchlecht ncZiel erreicht bnoetig :=
  ⟨23, by rw [mitglieder_laenge]; decide, raumSchlechtIn_aus z (grenzenVon 23).1 (grenzenVon 23).2 ncZiel h0
    (fun f => (by decide : ∀ f : Fin z.fns.length, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 23).1) f) (by decide)
    (by decide) List.mem_cons_self (ws := ws) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end Gabbro.Grammatik.Gen.Zeugen.N23_4
