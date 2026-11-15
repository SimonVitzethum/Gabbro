/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module



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
  .cons (.call (D := z.deklaration) ⟨1, by decide⟩ .nil (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b3 : Rumpf z.deklaration ⟨3, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨0, by decide⟩ (by decide) (.nil)) (.cons (.locks (D := z.deklaration) ⟨1, by decide⟩ (by decide) (.nil)) (.ret .empty (List.Perm.refl _)))

def b4 : Rumpf z.deklaration ⟨4, by decide⟩ :=
  .cons (.locks (D := z.deklaration) ⟨1, by decide⟩ (by decide) (.nil)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨n + 5, h⟩ => absurd h (by change n + 5 < 5 at h; omega)

def P : Programm z.deklaration :=
  (⟨r, fun f => decide (f.val = 0 ∨ f.val = 4)⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨2, by decide⟩, ⟨3, by decide⟩] (by decide) (by decide)

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

/-- Exact cell set, including every companion cell of this fixture. -/
def zellen : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨1, 0, true, [true, true, true]⟩,
  ⟨1, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [false, false, true]⟩,
  ⟨1, 0, true, [false, false, false]⟩,
  ⟨1, 0, true, [false, true, true]⟩,
  ⟨1, 0, true, [false, true, false]⟩,
  ⟨3, 0, true, [false, false]⟩,
  ⟨3, 0, true, [true, true]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩,
  ⟨9, 0, true, [true, true, false, false]⟩,
  ⟨9, 0, true, [true, true, false, true]⟩,
  ⟨9, 0, true, [true, false, false, false]⟩,
  ⟨9, 0, true, [true, false, false, true]⟩,
  ⟨9, 0, true, [true, false, true, false]⟩,
  ⟨9, 0, true, [true, false, true, true]⟩,
  ⟨9, 0, true, [false, false, false, false]⟩,
  ⟨9, 0, true, [false, false, false, true]⟩,
  ⟨9, 0, true, [false, true, false, false]⟩,
  ⟨9, 0, true, [false, true, false, true]⟩,
  ⟨9, 0, true, [false, false, true, false]⟩,
  ⟨9, 0, true, [false, false, true, true]⟩,
  ⟨9, 0, true, [false, true, true, false]⟩,
  ⟨9, 0, true, [false, true, true, true]⟩,
  ⟨9, 0, true, [true, true, true, true]⟩]

theorem zellen_exact : e.zellen.eraseDups = zellen := by decide

theorem e_hat : ∀ x ∈ zellen, e.Hat x := by
  intro x member
  rw [← zellen_exact] at member
  exact List.mem_eraseDups.1 member

theorem e_zeuge : e.gueltig = true ∧ e.Hat ⟨0, 0, true, [true, false, false]⟩ :=
  ⟨e_gueltig, e_hat _ (by decide)⟩

/-- Missing requested cells are findings, never an altered checker verdict. -/
def missing : List Zelle := requested.filter (fun x => !zellen.contains x)

end Gabbro.Grammatik.Gen.Zeugen.F09_mask
