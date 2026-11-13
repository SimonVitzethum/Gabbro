module
public import Stage0.Frontend.Elaboration
public import Grammatik.Parser.Elab.Modules.Frontend
public import Grammatik.Parser.Elab.Generic.Expansion
public import Grammatik.Parser.Elab.Konst.ErsetzungTor
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

theorem expansionHeader_use (moduleAlias : String) (path args : List String) :
    expansionHeader (.moduleUseT moduleAlias path args) = true := rfl

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
    elaborator consumes, then check the expanded unit with certified const substitution
    and runtime metadata checks.
    Consumed headers are checked through their expanded runtime declarations. -/
def checkExpansionGate (declarations : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let (expanded, requirements) ← Modules.prepare declarations
  Konst.checkSourceMetadata (uMembers expanded)
  .ok (expanded, requirements)

/-- Gate acceptance runs the canonical expansion on the source declarations. -/
theorem checkExpansionGate_expansion {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    Modules.prepare declarations = .ok (expanded, requirements) := by
  cases hp : Modules.prepare declarations with
  | error e => simp [checkExpansionGate, hp, bind, Except.bind] at h
  | ok pr =>
    obtain ⟨e, r⟩ := pr
    cases hc : Konst.checkSourceMetadata (uMembers e) with
    | error err => simp [checkExpansionGate, hp, bind, Except.bind, hc] at h
    | ok _ =>
      have returned : e = expanded ∧ r = requirements := by
        simpa only [checkExpansionGate, hp, bind, Except.bind, hc,
          Except.ok.injEq, Prod.mk.injEq] using h
      obtain ⟨rfl, rfl⟩ := returned
      rfl

/-- Gate acceptance leaves no unbound metadata in the expanded unit. -/
theorem checkExpansionGate_checked {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    ExportMetadata.unitMetadata (Konst.ohneKonst (uMembers expanded)) = false := by
  have hp := checkExpansionGate_expansion h
  cases hc : Konst.checkSourceMetadata (uMembers expanded) with
  | error e =>
    have contra : checkExpansionGate declarations = .error e := by
      simp [checkExpansionGate, hp, bind, Except.bind, hc]
    rw [contra] at h
    cases h
  | ok value =>
    cases value
    exact Konst.checkSourceMetadata_runtime_sound _ hc

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
  | error e => simp [Modules.prepare, hr, bind, Except.bind] at h
  | ok result =>
    cases hv : Modules.validOutput declarations result with
    | false => simp [Modules.prepare, hr, bind, Except.bind, hv] at h
    | true =>
      have returned : result.items = expanded ∧ result.requirements = requirements := by
        simpa only [Modules.prepare, hr, bind, Except.bind, hv, ite_true,
          pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] using h
      exact ⟨result, rfl, returned.1, returned.2, hv⟩

/-- No residual generic syntax and no open module reference survive the gate. -/
theorem checkExpansionGate_ordinary {declarations expanded : List SItemTief}
    {requirements : List (STyp × String)}
    (h : checkExpansionGate declarations = .ok (expanded, requirements)) :
    Instantiation.ohneGenerik expanded = true ∧
      Instantiation.closed expanded = true := by
  obtain ⟨result, _, same, _, hv⟩ :=
    checkExpansionGate_output (checkExpansionGate_expansion h)
  have parts : Modules.existingForms result.items = true ∧
      Instantiation.ohneGenerik result.items = true ∧
      Instantiation.freshNames (Modules.userNames declarations) result.generatedNames = true ∧
      Instantiation.closed result.items = true := by
    simpa only [Modules.validOutput, Bool.and_eq_true, and_assoc] using hv
  rw [← same]
  exact ⟨parts.2.1, parts.2.2.2⟩

end Gabbro.Stage0.Frontend
