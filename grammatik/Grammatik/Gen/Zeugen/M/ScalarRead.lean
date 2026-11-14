/- A scalar read with no atomic rely or lock-source obligation. -/
module

public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Fein.Zellen

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.ScalarRead

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({ globs := [{ typ := .bool }] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.glob ⟨0, by decide⟩ (by decide)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨n + 1, h⟩ => absurd h (by change n + 1 < 1 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩] (by decide) (by decide)

theorem e_gueltig : e.gueltig = true := by decide

/-- A real memory-read constructor is covered by an accepted fixture. -/
theorem e_hatF : e.HatF ⟨0, 0, 4, false, []⟩ := by decide

theorem e_hat : e.Hat ⟨0, 0, true, [true, false, false]⟩ := by decide

end Gabbro.Grammatik.Gen.Zeugen.ScalarRead
