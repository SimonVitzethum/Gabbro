/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public meta import Grammatik.Gen.Abdeckung.Satz.Raum
public meta import Grammatik.Gen.Abdeckung.Satz.ZellenVoll
public meta import Grammatik.Gen.Druck.LeanZeuge

import Grammatik.Gen.Druck.LeanZeuge

public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1
public import Grammatik.Gen.Fein.Zellen
public import Grammatik.Gen.Zeugen.Gap.F03_reg
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F03_reg

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }],
    tabs := [{ count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 },
      { count := 1, felder := [{ typ := .int 0 1 }] },
      { count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 }],
    regs := [{ typ := .bool, klasse := .r, traeger := [0, 1, 2] }],
    sigs := [{ haelt := [0] }, { schreibt := [0], boden := some 0 }],
    fns := [0, 1] } : Spez).einzeln

/-- The ordinary read supplies the guarded footprint; the register is still read. -/
def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.slot (D := z.deklaration) (⟨0, by decide⟩ : z.deklaration.Tab) (⟨0, by decide⟩ : z.deklaration.Feld ⟨0, by decide⟩) (.lit 0) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))
    (.cons (.ite .tru (.regRead (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) .nil) .nil)
      (.ret .empty (List.Perm.refl _)))

/-- A repeated root can write the first guarded carrier; the third stays separate. -/
def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .cons (.locks (D := z.deklaration) (⟨0, by decide⟩ : z.deklaration.Lock) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)
    (.cons (.call (D := z.deklaration) ⟨0, by decide⟩ .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) .nil))
    (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by change n + 2 < 2 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨1, by decide⟩, ⟨1, by decide⟩] (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

def requested : List Zelle := [
  ⟨2, 0, true, [true, false, true, false]⟩,
  ⟨2, 1, true, [true, false]⟩,
  ⟨2, 1, true, [false, true]⟩,
  ⟨2, 1, true, [true, true]⟩]

/-- The block rule checks a discarded register result in the current fragment. -/
theorem e_gueltig : e.gueltig = true := by decide +kernel

/-- The original end-block form remains a finding; the accepted block form is real. -/
theorem register_variants_zeuge : Gap.F03_reg.e.gueltig = false ∧ e.gueltig = true ∧
    e.HatF ⟨0, 5, 8, false, []⟩ ∧ ¬ e.HatF ⟨0, 6, 10, false, []⟩ :=
  ⟨Gap.F03_reg.e_refused, e_gueltig, by decide, by decide⟩

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F03_reg
