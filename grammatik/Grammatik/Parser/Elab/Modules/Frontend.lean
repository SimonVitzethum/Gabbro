module
public import Grammatik.Parser.Elab.Modules.Expansion
public import Grammatik.Parser.Elab.SourceNormalization
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules

/-- The prescribed frontend order: modules, generic functions, specification contracts, then
    named literals. Module static-function requirements travel with the same unit to SigPasst. -/
def prepareRaw (items : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let modules ← expandWithRequirements items
  let members := Uebersetze.uMembers modules.items
  let members := if syntaxList items then UebersetzeAllg2.normTopU32 members else members
  let (target, requirements) ← Generic.expandWithLiterals members modules.literals
  pure (target, modules.requirements ++ requirements)

def existingForms (items : List SItemTief) : Bool :=
  ordinary items && !(items.any Generic.genericHeader)

/-- The actual exporter entry checks its syntactic postcondition. Checking real contracts,
    storage and every implementation body still belongs to the unchanged ordinary elaborator. -/
def prepare (items : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let (target, requirements) ← prepareRaw items
  if existingForms target then pure (target, requirements)
  else throw "parametric-module-output: frontend left an unexpanded form"

theorem prepare_existingForms (items target : List SItemTief) (requirements : List (STyp × String))
    (h : prepare items = .ok (target, requirements)) : existingForms target = true := by
  cases hr : prepareRaw items with
  | error error => simp [prepare, hr] at h
  | ok result =>
    rcases result with ⟨result, obligations⟩
    cases ho : existingForms result with
    | false => simp [prepare, hr, ho] at h
    | true =>
      simp [prepare, hr, ho] at h
      rcases h with ⟨rfl, rfl⟩
      exact ho

end Gabbro.Grammatik.Parser.Modules
