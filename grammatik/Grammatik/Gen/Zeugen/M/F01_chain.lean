/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public meta import Grammatik.Gen.Abdeckung.Satz.Raum
public meta import Grammatik.Gen.Abdeckung.Satz.ZellenVoll
public meta import Grammatik.Gen.Druck.LeanZeuge

import Grammatik.Gen.Druck.LeanZeuge

public import Grammatik.Gen.Abdeckung.Satz.Raum

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F01_chain

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    fns := [0, 0, 0] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .cons (.call ⟨1, by decide⟩ .nil (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .cons (.call ⟨2, by decide⟩ .nil (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨n + 3, h⟩ => absurd h (by change n + 3 < 3 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩] (by decide) (by decide)

def requested : List Zelle := [
  ⟨1, 0, true, [false, true, false]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F01_chain
