module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Linken.Modul

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The constructions that supply whole language units to the concrete model. Each constructor fixes the
    complete machine unit, including its rules, loader, clause table and hardware catalogue. -/
inductive EinheitHerkunft : Ast.Semantik.Einheit → Prop where
  | quelle (P : Katalog.Plattform) (t : Ast.Unit) : EinheitHerkunft (einheitVon P t)
  | mitInvarianten (P : Katalog.Plattform) (u : Ast.Semantik.UnitMitInvarianten) :
      EinheitHerkunft (Ast.Semantik.elaborierenMitInvarianten P u)
  | verlinkt (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment)
      (h : Linken.linke plan = some p) : EinheitHerkunft (p.einheit plan.plattform)

/-- The image of the whole-unit constructions, with equality inherited from the machine unit. -/
abbrev Spracheinheit := { E : Ast.Semantik.Einheit // EinheitHerkunft E }

theorem bezeichnet_herkunft {P : Katalog.Plattform} {a : Text.RawText} {E : Ast.Semantik.Einheit}
    (h : Ast.Semantik.Bezeichnet P Ast.Category.unit a E) : EinheitHerkunft E := by
  obtain ⟨t, _, hElab, _⟩ := h
  rw [Ast.Semantik.elab_vollstaendig hElab]
  exact .quelle P t

/-- Restricting the type of denoted units to their construction image preserves every denotation, including
    its existing platform admission conditions. -/
theorem bezeichnet_spracheinheit_iff (P : Katalog.Plattform) (a : Text.RawText) :
    (∃ E : Spracheinheit, Ast.Semantik.Bezeichnet P Ast.Category.unit a E.val) ↔
      ∃ E : Ast.Semantik.Einheit, Ast.Semantik.Bezeichnet P Ast.Category.unit a E := by
  constructor
  · rintro ⟨E, h⟩
    exact ⟨E.val, h⟩
  · rintro ⟨E, h⟩
    exact ⟨⟨E, bezeichnet_herkunft h⟩, h⟩

/-- Changing the tag of either kind of run preserves the dependent run payload. An existing tagged run has
    a tag in the construction image exactly when its machine unit has a whole-unit origin. -/
def spracheinheit_tag (F : Ast.Semantik.Einheit → Type) :
    (Σ E : Spracheinheit, F E.val) ≃ { r : Σ E : Ast.Semantik.Einheit, F E // EinheitHerkunft r.1 } where
  toFun := fun ⟨E, r⟩ => ⟨⟨E.val, r⟩, E.property⟩
  invFun := fun ⟨⟨E, r⟩, h⟩ => ⟨⟨E, h⟩, r⟩
  left_inv := by
    rintro ⟨⟨E, h⟩, r⟩
    rfl
  right_inv := by
    rintro ⟨⟨E, r⟩, h⟩
    rfl

end Gabbro.Core.Ziel.Korrektheit
