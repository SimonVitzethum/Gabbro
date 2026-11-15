/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public meta import Grammatik.Gen.Abdeckung.Satz.Raum
public meta import Grammatik.Gen.Abdeckung.Satz.ZellenVoll
public meta import Grammatik.Gen.Druck.LeanZeuge

import Grammatik.Gen.Druck.LeanZeuge

public import Grammatik.Gen.Abdeckung.Satz.Raum

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F06_pool

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }],
    globs := [{ typ := .int 0 1, sperre := some 0 }, { typ := .int 0 1 }],
    sigs := [{ gschreibt := [0, 1] }, { gschreibt := [0] }, {}], fns := [0, 1, 2] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.glob ⟨1, by decide⟩ (by decide)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨n + 3, h⟩ => absurd h (by change n + 3 < 3 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] (by decide) (by decide)

def requested : List Zelle := [
  ⟨6, 1, true, [false, false, false, false]⟩,
  ⟨6, 1, true, [true, false, false, false]⟩,
  ⟨6, 1, true, [false, true, false, false]⟩,
  ⟨6, 1, true, [true, true, false, false]⟩,
  ⟨6, 1, true, [false, false, false, true]⟩,
  ⟨6, 1, true, [true, false, false, true]⟩,
  ⟨6, 1, true, [false, true, false, true]⟩,
  ⟨6, 1, true, [true, true, false, true]⟩,
  ⟨6, 1, true, [false, false, true, true]⟩,
  ⟨6, 1, true, [true, false, true, true]⟩,
  ⟨6, 1, true, [false, true, true, true]⟩,
  ⟨6, 1, true, [true, true, true, true]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F06_pool
