/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public import Grammatik.Gen.Abdeckung.Satz.Raum

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F07_race

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({ locks := [{ rang := 0 }],
    globs := [{ typ := .int 0 1, sperre := some 0 }, { typ := .int 0 1 }, { typ := .int 0 1 }, { typ := .int 0 1, sperre := some 0 }],
    sigs := [{ gschreibt := [0, 1] }, { gschreibt := [0] }, {}], fns := [0, 1, 2] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .cons (.assignGlob ⟨1, by decide⟩ (.widen (by decide) (by decide) (.lit 0)) (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .bind (.glob ⟨2, by decide⟩ (by decide)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨n + 3, h⟩ => absurd h (by change n + 3 < 3 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] (by decide) (by decide)

def requested : List Zelle := [
  ⟨7, 0, true, [true, false]⟩,
  ⟨7, 0, true, [false, true]⟩,
  ⟨7, 0, true, [true, true]⟩,
  ⟨7, 1, false, [false, false, false]⟩,
  ⟨7, 1, false, [true, false, false]⟩,
  ⟨7, 1, false, [false, true, false]⟩,
  ⟨7, 1, false, [false, false, true]⟩,
  ⟨7, 1, false, [true, false, true]⟩,
  ⟨7, 1, false, [false, true, true]⟩,
  ⟨7, 1, false, [true, true, true]⟩]

theorem e_gueltig : e.gueltig = true := by decide +kernel

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.F07_race
