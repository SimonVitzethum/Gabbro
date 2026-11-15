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

namespace Gabbro.Grammatik.Gen.Zeugen.F09_mask

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- Handlers take only masking locks; the non-handler reaches both lock kinds. -/
abbrev z : Spez := ({
    locks := [{ rang := 0 }, { rang := 1, maskiert := true }],
    sigs := [{}, { boden := some 0 }, { boden := some 1 }],
    fns := [0, 0, 0, 1, 2] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .cons (.call (D := z.deklaration) ⟨1, by decide⟩ .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b3 : Rumpf z.deklaration ⟨3, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.nil)) (.cons (.locks (D := z.deklaration) ⟨1, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.nil)) (.ret .empty (List.Perm.refl _)))

def b4 : Rumpf z.deklaration ⟨4, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨1, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.nil)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨n + 5, h⟩ => absurd h (by change n + 5 < 5 at h; omega)

def P : Programm z.deklaration :=
  (⟨r, fun f => decide (f.val = 0 ∨ f.val = 4)⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨2, by decide⟩, ⟨3, by decide⟩] (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

def requested : List Zelle := [
  ⟨9, 0, true, [false, false, false, false]⟩,
  ⟨9, 0, true, [false, true, false, false]⟩,
  ⟨9, 0, true, [false, false, true, false]⟩,
  ⟨9, 0, true, [false, true, true, false]⟩,
  ⟨9, 0, true, [false, false, false, true]⟩,
  ⟨9, 0, true, [false, true, false, true]⟩,
  ⟨9, 0, true, [false, false, true, true]⟩,
  ⟨9, 0, true, [false, true, true, true]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F09_mask
