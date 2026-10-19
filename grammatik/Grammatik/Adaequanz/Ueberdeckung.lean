/-
  File:      Grammatik/Adaequanz/Ueberdeckung.lean
  Subject:   THEOREM 3 (CELL-LOCAL IMPLEMENTATIONS: THE COMPILER'S CASE): a test set is sufficient exactly when it
             COVERS every realizable cell, so the least sufficient set is a minimum cover.

  The compiler's correctness splits per constructor (Track L: `lowerS_ok`, `lowerFn_callref`): the lowering of
  a node is correct when the template chosen for its CELL (constructor x lowering context x child classes) is,
  given that its children's are. Model: an implementation is a table `ok : Z → Prop` of correct cells, and it
  handles a program correctly iff every cell the program contains is correct (`Korrekt`). The `iff` is the
  hypothesis NO MASKING: a wrong cell shows in the observed result of every program that contains it (the
  observation compares the complete behaviour, e.g. by translation validation of the whole function, not one
  run). Under it:

    * `deckung_iff`: `M` is sufficient for every table  iff  every realizable cell occurs in a program of `M`.
    * `deckung_schranke`: a set `A` of realizable cells no two of which occur in one program forces
      `|M| ≥ |A|` (the lower bound of the minimum cover number `κ`).
    * `deckung_konstruktion`: one witness per cell is a cover (`κ ≤` number of realizable cells).

  The flag mutants of `Minimal.lean` are such tables for the tree automata (`Enthaelt` as the containment), so
  for `m ≥ 2 n` Theorem 2b is the cover condition of this file.
-/
import Grammatik.Adaequanz.Gegenmodell

namespace Gabbro.Grammatik.Adaequanz

variable {P Z : Type} (zellen : P → Z → Prop)

/-- The program `p` is handled correctly by the table `ok`: every cell it contains is correct. -/
def Korrekt (ok : Z → Prop) (p : P) : Prop := ∀ z, zellen p z → ok z

/-- **Sufficient iff covering.** -/
theorem deckung_iff (M : List P) :
    (∀ ok : Z → Prop, (∀ p ∈ M, Korrekt zellen ok p) → ∀ p, Korrekt zellen ok p) ↔
      ∀ z, (∃ p, zellen p z) → ∃ p ∈ M, zellen p z := by
  constructor
  · intro h z ⟨p0, hp0⟩
    exact h (fun z' => ∃ p ∈ M, zellen p z') (fun p hp z' hz' => ⟨p, hp, hz'⟩) p0 z hp0
  · intro h ok hM p z hz
    obtain ⟨p', hp', hz'⟩ := h z ⟨p, hz⟩
    exact hM p' hp' z hz'

/-- **Lower bound of the minimum cover**: cells that never share a program each need their own program. -/
theorem deckung_schranke {M : List P} (hM : ∀ z, (∃ p, zellen p z) → ∃ p ∈ M, zellen p z) (A : Finset Z)
    (hreal : ∀ z ∈ A, ∃ p, zellen p z)
    (hfremd : ∀ p, ∀ z ∈ A, ∀ z' ∈ A, zellen p z → zellen p z' → z = z') : A.card ≤ M.length := by
  classical
  have hw : ∀ z : A, ∃ p ∈ M, zellen p z := fun z => hM z (hreal z z.2)
  choose f hf hfz using hw
  have hinj : Function.Injective f := fun z z' he =>
    Subtype.ext (hfremd (f z) z z.2 z' z'.2 (hfz z) (he ▸ hfz z'))
  calc A.card = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    _ ≤ M.toFinset.card := Finset.card_le_card fun p hp => by
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
        exact List.mem_toFinset.mpr (hf z)
    _ ≤ M.length := List.toFinset_card_le M

/-- **Upper bound of the minimum cover**: one witness per realizable cell. -/
theorem deckung_konstruktion (zs : List Z) (hzs : ∀ z, (∃ p, zellen p z) → z ∈ zs) (wit : Z → P)
    (hwit : ∀ z ∈ zs, (∃ p, zellen p z) → zellen (wit z) z) :
    (∀ z, (∃ p, zellen p z) → ∃ p ∈ zs.map wit, zellen p z) ∧ (zs.map wit).length = zs.length :=
  ⟨fun z hz => ⟨wit z, List.mem_map.mpr ⟨z, hzs z hz, rfl⟩, hwit z (hzs z hz) hz⟩, List.length_map _⟩

end Gabbro.Grammatik.Adaequanz
