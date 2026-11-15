/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module



public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F01_chain

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    fns := [0, 0, 0] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .cons (.call (D := z.deklaration) ⟨1, by decide⟩ .nil (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .cons (.call (D := z.deklaration) ⟨2, by decide⟩ .nil (by decide) (by decide)) (.ret .empty (List.Perm.refl _))

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

/-- Exact cell set, including every companion cell of this fixture. -/
def zellen : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨1, 0, true, [true, true, true]⟩,
  ⟨1, 0, true, [false, false, false]⟩,
  ⟨1, 0, true, [false, true, true]⟩,
  ⟨1, 0, true, [false, false, true]⟩,
  ⟨1, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [false, true, false]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩]

theorem zellen_exact : e.zellen.eraseDups = zellen := by cbv

theorem e_hat : ∀ x ∈ zellen, e.Hat x := by
  intro x member
  rw [← zellen_exact] at member
  exact List.mem_eraseDups.1 member

theorem e_zeuge : e.gueltig = true ∧ e.Hat ⟨0, 0, true, [true, false, false]⟩ :=
  ⟨e_gueltig, e_hat _ (by decide)⟩

/-- Missing requested cells are findings, never an altered checker verdict. -/
def missing : List Zelle := requested.filter (fun x => !zellen.contains x)

end Gabbro.Grammatik.Gen.Zeugen.F01_chain
