/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public meta import Grammatik.Gen.Abdeckung.Satz.Raum
public meta import Grammatik.Gen.Abdeckung.Satz.ZellenVoll
public meta import Grammatik.Gen.Druck.LeanZeuge

import Grammatik.Gen.Druck.LeanZeuge

public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F02_foot

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }],
    globs := [{ typ := .int 0 1 }, { typ := .int 0 1, sperre := some 0 },
      { typ := .int 0 1, atomar := true }, { typ := .int 0 1, atomar := true, sperre := some 0 },
      { typ := .int 0 1 }, { typ := .int 0 1, sperre := some 0 }],
    sigs := [{ gschreibt := [0, 4] }, { haelt := [0] }, { gschreibt := [1], boden := some 0 },
      { gschreibt := [1] }, { boden := some 0 }, { haelt := [0] }],
    fns := [0, 1, 2, 3, 4, 5] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.glob (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.bind (.glob (D := z.deklaration) ⟨4, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (List.Perm.refl _)))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .bind (.glob (D := z.deklaration) ⟨1, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.bind (.glob (D := z.deklaration) ⟨5, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (List.Perm.refl _)))

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)
    (.cons (.call (D := z.deklaration) ⟨1, by decide⟩ .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) .nil))
    (.ret .empty (List.Perm.refl _))

def b3 : Rumpf z.deklaration ⟨3, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b4 : Rumpf z.deklaration ⟨4, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.bind (.glob (D := z.deklaration) ⟨5, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.cons (.call (D := z.deklaration) ⟨1, by decide⟩ .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.nil)))) (.ret .empty (List.Perm.refl _))

def b5 : Rumpf z.deklaration ⟨5, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨n + 6, h⟩ => absurd h (by change n + 6 < 6 at h; omega)

/-- All contracts are true; atomic declarations never add artificial read sites. -/
def P : Programm z.deklaration :=
  (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
  (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

def requested : List Zelle := [
  ⟨2, 0, true, [false, true, false, false]⟩,
  ⟨2, 0, true, [false, false, true, false]⟩,
  ⟨2, 0, true, [false, true, true, false]⟩,
  ⟨2, 0, true, [true, true, true, false]⟩,
  ⟨2, 0, true, [false, false, false, true]⟩,
  ⟨2, 0, true, [false, true, false, true]⟩,
  ⟨2, 2, false, [false, false, false]⟩,
  ⟨2, 2, false, [true, false, false]⟩,
  ⟨2, 2, false, [false, true, false]⟩,
  ⟨2, 2, false, [true, true, false]⟩,
  ⟨2, 2, false, [false, false, true]⟩,
  ⟨2, 2, false, [true, false, true]⟩,
  ⟨2, 2, false, [false, true, true]⟩,
  ⟨2, 2, false, [true, true, true]⟩,
  ⟨2, 3, false, [false, false, false]⟩,
  ⟨2, 3, false, [true, false, false]⟩,
  ⟨2, 3, false, [false, true, false]⟩,
  ⟨2, 3, false, [true, true, false]⟩,
  ⟨2, 3, false, [false, false, true]⟩,
  ⟨2, 3, false, [true, false, true]⟩,
  ⟨2, 3, false, [false, true, true]⟩,
  ⟨2, 3, false, [true, true, true]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F02_foot
