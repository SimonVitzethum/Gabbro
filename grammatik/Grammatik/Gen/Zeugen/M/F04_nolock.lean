/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public import Grammatik.Gen.Abdeckung.Satz.Raum

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F04_nolock

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({ locks := [{ rang := 0 }, { rang := 1, maskiert := true }],
    globs := [{ typ := .bool }], fns := [0, 0] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by change n + 2 < 2 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩] (by decide) (by decide)

def requested : List Zelle := [
  ⟨3, 0, true, [false, false]⟩,
  ⟨3, 0, true, [false, true]⟩,
  ⟨4, 0, true, [false, false]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩,
  ⟨6, 0, true, [true, false, false]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F04_nolock
