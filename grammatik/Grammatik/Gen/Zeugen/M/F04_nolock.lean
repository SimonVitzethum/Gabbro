/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module



public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.F04_nolock

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }, { rang := 1, maskiert := true }],
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

/-- Exact cell set, including every companion cell of this fixture. -/
def zellen : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨1, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [false, false, true]⟩,
  ⟨1, 0, true, [false, false, false]⟩,
  ⟨3, 0, true, [false, false]⟩,
  ⟨4, 0, true, [false, false]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩,
  ⟨6, 0, true, [true, false, false]⟩,
  ⟨6, 1, true, [false, true, false, false]⟩,
  ⟨6, 1, true, [false, false, false, false]⟩,
  ⟨6, 1, true, [true, false, false, false]⟩,
  ⟨6, 1, true, [true, true, false, false]⟩,
  ⟨7, 0, true, [false, true]⟩,
  ⟨7, 1, false, [true, false, false]⟩,
  ⟨7, 1, false, [false, false, false]⟩,
  ⟨9, 0, true, [false, true, false, false]⟩,
  ⟨9, 0, true, [false, true, false, true]⟩,
  ⟨9, 0, true, [false, false, false, false]⟩,
  ⟨9, 0, true, [false, false, false, true]⟩,
  ⟨10, 0, true, [true]⟩]

theorem zellen_exact : e.zellen.eraseDups = zellen := by cbv

theorem e_hat : ∀ x ∈ zellen, e.Hat x := by
  intro x member
  rw [← zellen_exact] at member
  exact List.mem_eraseDups.1 member

theorem e_zeuge : e.gueltig = true ∧ e.Hat ⟨0, 0, true, [true, false, false]⟩ :=
  ⟨e_gueltig, e_hat _ (by decide)⟩

/-- Missing requested cells are findings, never an altered checker verdict. -/
def missing : List Zelle := requested.filter (fun x => !zellen.contains x)

end Gabbro.Grammatik.Gen.Zeugen.F04_nolock
