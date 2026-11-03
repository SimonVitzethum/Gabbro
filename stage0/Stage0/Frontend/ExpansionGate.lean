module
public import Stage0.Frontend.Elaboration
public import Grammatik.Parser.Elab.Modules.Frontend
public import Grammatik.Parser.Elab.Generic.Expansion
public import Grammatik.Parser.Elab.Export.ExportMetadata
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Source headers consumed by canonical expansion: module templates and uses,
    spec and implementation groups, tagged declarations and generic function,
    prototype, spec or translator headers. Ordinary elaboration and checking
    still run on every instantiated body afterwards (check model A). -/
def expansionHeader : SItemTief → Bool
  | .moduleTemplateT .. | .moduleUseT .. => true
  | .specGroupT .. | .implGroupT .. | .taggedByT .. => true
  | item => Generic.genericHeader item

/-- Template and use headers are consumed by expansion, never lowered directly. -/
theorem expansionHeader_template (name : String) (params : List SGenericParam)
    (body : List SItemTief) : expansionHeader (.moduleTemplateT name params body) = true := rfl

theorem expansionHeader_use (alias : String) (path args : List String) :
    expansionHeader (.moduleUseT alias path args) = true := rfl

/-- Spec groups, implementation groups and tagged declarations are consumed. -/
theorem expansionHeader_specGroup (name : String) (types effects : List String)
    (functions : List FnSig) :
    expansionHeader (.specGroupT name types effects functions) = true := rfl

theorem expansionHeader_implGroup (name : String) (types : List STyp)
    (effects : List (List SEffekt)) (functions : List SItemTief) :
    expansionHeader (.implGroupT name types effects functions) = true := rfl

theorem expansionHeader_tagged (declaration : SItemTief) (spec : String) :
    expansionHeader (.taggedByT declaration spec) = true := rfl

/-- The expansion-aware gate: run the very same canonical expansion the
    elaborator consumes, then check the EXPANDED unit for unbound metadata.
    Acceptance never refuses an original header the expansion consumes. -/
def checkExpansionGate (declarations : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let (expanded, requirements) ← Modules.prepare declarations
  ExportMetadata.check (uMembers expanded)
  .ok (expanded, requirements)

/-- Gate acceptance runs the canonical expansion on the source declarations. -/
theorem checkExpansionGate_expansion {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    Modules.prepare declarations = .ok (expanded, requirements) := by
  cases hp : Modules.prepare declarations with
  | error e => simp [checkExpansionGate, hp] at h
  | ok pr =>
    obtain ⟨e, r⟩ := pr
    cases hc : ExportMetadata.check (uMembers e) with
    | error err => simp [checkExpansionGate, hp, hc] at h
    | ok _ =>
      simp [checkExpansionGate, hp, hc] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hp

/-- Gate acceptance leaves no unbound metadata in the expanded unit. -/
theorem checkExpansionGate_checked {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    (uMembers expanded).any ExportMetadata.itemMetadata = false := by
  have hp := checkExpansionGate_expansion h
  cases hc : ExportMetadata.check (uMembers expanded) with
  | error e =>
    have contra : checkExpansionGate declarations = .error e := by
      simp [checkExpansionGate, hp, hc]
    rw [contra] at h
    cases h
  | ok _ => exact ExportMetadata.check_sound _ hc

/-- The gate checks the exact expansion the elaborator consumes. -/
theorem checkExpansionGate_expands {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    expandU declarations = .ok (expanded, requirements) :=
  checkExpansionGate_expansion h

/-- Headers are consumed: no generic header survives in the checked unit. -/
theorem checkExpansionGate_existingForms {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    Modules.existingForms expanded = true :=
  Modules.prepare_existingForms declarations expanded requirements
    (checkExpansionGate_expansion h)

/-- The successful expansion carries its complete structural postcondition. -/
theorem checkExpansionGate_output {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : Modules.prepare declarations = .ok (expanded, requirements)) :
    ∃ result, Modules.prepareDetailedRaw declarations = .ok result ∧
      result.items = expanded ∧ result.requirements = requirements ∧
      Modules.validOutput declarations result = true := by
  cases hr : Modules.prepareDetailedRaw declarations with
  | error e => simp [Modules.prepare, hr] at h
  | ok result =>
    cases hv : Modules.validOutput declarations result with
    | false => simp [Modules.prepare, hr, hv] at h
    | true =>
      simp [Modules.prepare, hr, hv] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨result, hr, rfl, rfl, hv⟩

/-- No residual generic syntax and no open module reference survive the gate. -/
theorem checkExpansionGate_ordinary {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    Instantiation.ohneGenerik expanded = true ∧
      Instantiation.closed expanded = true := by
  obtain ⟨result, _, rfl, _, hv⟩ :=
    checkExpansionGate_output (checkExpansionGate_expansion h)
  unfold Modules.validOutput at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨_, hgenerik⟩, _, hclosed⟩ := hv
  exact ⟨hgenerik, hclosed⟩

end Gabbro.Stage0.Frontend
