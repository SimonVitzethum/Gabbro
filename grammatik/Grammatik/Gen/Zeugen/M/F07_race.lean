/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module



public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section

set_option maxRecDepth 4096

namespace Gabbro.Grammatik.Gen.Zeugen.F07_race

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }],
    globs := [{ typ := .int 0 1, sperre := some 0 }, { typ := .int 0 1 }, { typ := .int 0 1 }, { typ := .int 0 1, sperre := some 0 }],
    sigs := [{ gschreibt := [0, 1] }, { gschreibt := [0] }, {}], fns := [0, 1, 2] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .cons (.assignGlob (D := z.deklaration) ⟨1, by decide⟩ (.widen (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.lit 0)) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (List.Perm.refl _))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .ret .empty (List.Perm.refl _)

def b2 : Rumpf z.deklaration ⟨2, by decide⟩ :=
  .bind (.glob (D := z.deklaration) ⟨2, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨n + 3, h⟩ => absurd h (by change n + 3 < 3 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

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

/-- Exact cell set, including every companion cell of this fixture. -/
def zellen : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨1, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [false, false, true]⟩,
  ⟨1, 0, true, [false, false, false]⟩,
  ⟨2, 0, true, [false, true, false, false]⟩,
  ⟨2, 2, false, [true, false, false]⟩,
  ⟨2, 2, false, [false, false, false]⟩,
  ⟨2, 2, false, [false, true, false]⟩,
  ⟨2, 2, false, [true, true, false]⟩,
  ⟨2, 3, false, [false, true, true]⟩,
  ⟨3, 0, true, [false, false]⟩,
  ⟨4, 0, true, [true, true]⟩,
  ⟨4, 0, true, [false, false]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩,
  ⟨6, 0, true, [true, false, false]⟩,
  ⟨6, 1, true, [false, true, true, true]⟩,
  ⟨6, 1, true, [false, true, true, false]⟩,
  ⟨6, 1, true, [false, true, false, false]⟩,
  ⟨6, 1, true, [false, true, false, true]⟩,
  ⟨6, 1, true, [false, false, true, true]⟩,
  ⟨6, 1, true, [false, false, false, false]⟩,
  ⟨6, 1, true, [false, false, false, true]⟩,
  ⟨6, 1, true, [true, false, true, true]⟩,
  ⟨6, 1, true, [true, false, true, false]⟩,
  ⟨6, 1, true, [true, false, false, false]⟩,
  ⟨6, 1, true, [true, false, false, true]⟩,
  ⟨6, 1, true, [true, true, true, true]⟩,
  ⟨6, 1, true, [true, true, false, false]⟩,
  ⟨6, 1, true, [true, true, false, true]⟩,
  ⟨6, 1, true, [false, false, true, false]⟩,
  ⟨7, 0, true, [true, false]⟩,
  ⟨7, 1, false, [true, true, true]⟩,
  ⟨7, 1, false, [false, true, true]⟩,
  ⟨7, 1, false, [false, true, false]⟩,
  ⟨7, 1, false, [false, false, true]⟩,
  ⟨7, 1, false, [true, false, false]⟩,
  ⟨7, 0, true, [false, true]⟩,
  ⟨7, 1, false, [false, false, false]⟩,
  ⟨7, 1, false, [true, false, true]⟩,
  ⟨7, 0, true, [true, true]⟩,
  ⟨9, 0, true, [false, true, false, false]⟩,
  ⟨9, 0, true, [false, false, false, false]⟩,
  ⟨10, 0, true, [true]⟩]

theorem zellen_exact : e.zellen.eraseDups = zellen := by decide +kernel

theorem e_hat : ∀ x ∈ zellen, e.Hat x := by
  intro x member
  rw [← zellen_exact] at member
  exact List.mem_eraseDups.1 member

theorem e_zeuge : e.gueltig = true ∧ e.Hat ⟨0, 0, true, [true, false, false]⟩ :=
  ⟨e_gueltig, e_hat _ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)⟩

/-- Missing requested cells are findings, never an altered checker verdict. -/
def missing : List Zelle := requested.filter (fun x => !zellen.contains x)

end Gabbro.Grammatik.Gen.Zeugen.F07_race
