module
public import Core.Katalog.Lauf

@[expose] public section

namespace Gabbro.Core.Katalog

/-- Boot arguments granted by the outside, initial core assignments for image entry occurrences,
    and the initial external state. Entry indices describe image data. -/
structure AussenStart where
  bootCore : Nat
  assignment : Nat → Option Nat
  regions : List Strecke
  inputBytes : Nat → Option UInt8
  outside : AussenSicht

/-- Admissibility at the boundary, before either loader runs. The unit supplies the image
    declaration and may impose its own interpretation of the boot arguments. -/
def ZulStart (k : Katalog) (h : Umgebung) (bild : Bild) (s : AussenStart) : Prop :=
  bild.gueltig k.plattform.ziel ∧
    s.bootCore < h.kernzahl ∧
    (∀ i, i < bild.entries.length → ∃ c, s.assignment i = some c) ∧
    (∀ i c, s.assignment i = some c → i < bild.entries.length ∧ c < h.kernzahl) ∧
    s.regions.Pairwise Strecke.getrennt ∧
    (∀ r ∈ s.regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.enthaelt (.endpoint e) → k.plattform.geraet e = some d → d.bus = .mmio →
        r.getrennt d.window) ∧
    (∀ a byte, s.inputBytes a = some byte → ∃ r ∈ s.regions, r.drin a) ∧
    s.outside = h.politik.sicht 0 []

theorem zulStart_erfuellbar {k h bild} (hw : Hardware k h) (image : bild.gueltig k.plattform.ziel) :
    ∃ s, ZulStart k h bild s := by
  let assignment := fun i => if i < bild.entries.length then some 0 else none
  refine ⟨⟨0, assignment, [], fun _ => none, h.politik.sicht 0 []⟩,
    image, hw.kerne, ?_, ?_, .nil, ?_, ?_, rfl⟩
  · intro i valid
    exact ⟨0, ite_eq_left valid⟩
  · intro i c assigned
    change (if i < bild.entries.length then some 0 else none) = some c at assigned
    split at assigned
    · rename_i valid
      cases assigned
      exact ⟨valid, hw.kerne⟩
    · cases assigned
  · intro r hr
    cases hr
  · intro a byte absent
    cases absent

end Gabbro.Core.Katalog
