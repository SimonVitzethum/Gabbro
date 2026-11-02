module
public import Grammatik.Parser.Elab.Modules.Expansion
public import Grammatik.Parser.Elab.SourceNormalization
public import Grammatik.Parser.Elab.Instantiation.Items
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules

/-- Declaration names in the actual flat output, across all namespaces. -/
def outputNames (items : List SItemTief) : List String := items.filterMap Generic.sourceName

/-- The original, ordinary namespace, before generative copies or function instances exist.
    Both canonical lookup keys and written flat names participate in collision checking. -/
def userNames (items : List SItemTief) : List String :=
  let ordinary := ordinaryList items
  let source := Aufloesung.quelle ordinary
  source.namen.map (Aufloesung.schluessel source.namen) ++ outputNames (Uebersetze.uMembers ordinary)

structure Prepared where
  items : List SItemTief
  requirements : List (STyp × String)
  /-- Actual allocations retained in the final output; never inferred from absence in userNames. -/
  generatedNames : List String

/-- The prescribed frontend order: modules, generic functions, specification contracts, then
    named literals. Provenance crosses the phase boundary with static-function requirements. -/
def prepareDetailedRaw (items : List SItemTief) : Except String Prepared := do
  let modules ← expandWithRequirements items
  let members := Uebersetze.uMembers modules.items
  let members := if syntaxList items then UebersetzeAllg2.normTopU32 members else members
  let result ← Generic.expandDetailed members modules.literals
  let allocated := modules.generatedNames ++ result.generatedNames
  let generated := allocated.filter ((outputNames result.items).contains)
  pure ⟨result.items, modules.requirements ++ result.requirements, generated⟩

def existingForms (items : List SItemTief) : Bool :=
  ordinary items && !(items.any Generic.genericHeader)

/-- The output name list has provenance even for user-supplied synthetic ASTs that spell reserved
    names. Filtering only removes allocated declarations consumed as templates by the next phase. -/
def generatedOutputNames (source target : List SItemTief) : List String :=
  match prepareDetailedRaw source with
  | .ok result => result.generatedNames.filter ((outputNames target).contains)
  | .error _ => []

/-- These structural checks do not establish acceptance. The unchanged ordinary checker still
    checks every instantiated body, signature, contract, builtin and indirect call afterwards. -/
def validOutput (source : List SItemTief) (result : Prepared) : Bool :=
  existingForms result.items && Instantiation.ohneGenerik result.items &&
    Instantiation.freshNames (userNames source) result.generatedNames && Instantiation.closed result.items

/-- The actual exporter entry checks the complete structural postcondition on the very same AST
    it returns. Failure refuses; neither partial expansion nor unchecked output can escape. -/
def prepare (items : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let result ← prepareDetailedRaw items
  if validOutput items result then pure (result.items, result.requirements)
  else throw "generic-output: residual syntax, name collision or unresolved direct global reference"

/-- Composed surface instantiation, with the exact same gate as the ordinary exporter. -/
def instantiate (items : List SItemTief) : Except String (List SItemTief) :=
  (prepare items).map Prod.fst

private theorem prepare_valid (source target : List SItemTief) (requirements : List (STyp × String))
    (h : prepare source = .ok (target, requirements)) :
    ∃ result, prepareDetailedRaw source = .ok result ∧ result.items = target ∧
      validOutput source result = true := by
  cases hr : prepareDetailedRaw source with
  | error error => simp [prepare, hr] at h
  | ok result =>
    cases hv : validOutput source result with
    | false => simp [prepare, hr, hv] at h
    | true =>
      simp [prepare, hr, hv] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨result, hr, rfl, hv⟩

private theorem instantiate_valid (source target : List SItemTief)
    (h : instantiate source = .ok target) :
    ∃ result, prepareDetailedRaw source = .ok result ∧ result.items = target ∧
      validOutput source result = true := by
  cases hp : prepare source with
  | error error => simp [instantiate, hp] at h
  | ok result =>
    rcases result with ⟨actual, requirements⟩
    simp [instantiate, hp] at h
    subst target
    exact prepare_valid source actual requirements hp

private theorem validOutput_parts (source : List SItemTief) (result : Prepared)
    (h : validOutput source result = true) :
    existingForms result.items = true ∧ Instantiation.ohneGenerik result.items = true ∧
      Instantiation.freshNames (userNames source) result.generatedNames = true ∧
      Instantiation.closed result.items = true := by
  simpa [validOutput, Bool.and_eq_true, and_assoc] using h

theorem prepare_existingForms (items target : List SItemTief) (requirements : List (STyp × String))
    (h : prepare items = .ok (target, requirements)) : existingForms target = true := by
  obtain ⟨result, _, same, valid⟩ := prepare_valid items target requirements h
  rw [← same]
  exact (validOutput_parts items result valid).1

/-- Success removes generic syntax throughout items, statements, expressions and type bounds. -/
theorem instantiate_ohneGenerik (p q : List SItemTief) (h : instantiate p = .ok q) :
    Instantiation.ohneGenerik q = true := by
  obtain ⟨result, _, same, valid⟩ := instantiate_valid p q h
  rw [← same]
  exact (validOutput_parts p result valid).2.1

/-- Every generated output name is distinct from every other generated output name and every
    original user name. This follows from the executable collision gate, not name conventions. -/
theorem instantiate_nameHygiene (p q : List SItemTief) (h : instantiate p = .ok q) :
    (generatedOutputNames p q).Nodup ∧
      ∀ name ∈ generatedOutputNames p q, name ∉ userNames p := by
  obtain ⟨result, raw, _, valid⟩ := instantiate_valid p q h
  have fresh := Instantiation.freshNames_sound _ _ (validOutput_parts p result valid).2.2.1
  unfold generatedOutputNames
  rw [raw]
  constructor
  · exact List.Pairwise.filter _ fresh.1
  · intro name member
    exact fresh.2 name (List.mem_filter.mp member).1

/-- Every direct global reference in the emitted AST names an emitted function declaration.
    This includes unchanged input references, rewritten spec calls, all instance edges and all
    lifted literal addresses/calls. Builtins, nominal constructors and local function-pointer
    calls are excluded exactly as documented by directReferences, and are checked later. -/
theorem instantiate_closed (p q : List SItemTief) (h : instantiate p = .ok q) :
    ∀ name ∈ Instantiation.directReferences q, name ∈ Instantiation.functionNames q := by
  obtain ⟨result, _, same, valid⟩ := instantiate_valid p q h
  rw [← same]
  exact Instantiation.closed_sound _ (validOutput_parts p result valid).2.2.2

theorem generatedOutputNames_declared (p q : List SItemTief) :
    ∀ name ∈ generatedOutputNames p q, name ∈ outputNames q := by
  intro name member
  cases hr : prepareDetailedRaw p with
  | error error => simp [generatedOutputNames, hr] at member
  | ok result =>
    have selected : name ∈ result.generatedNames.filter ((outputNames q).contains) := by
      simpa [generatedOutputNames, hr] using member
    exact List.contains_iff_mem.mp (List.mem_filter.mp selected).2

end Gabbro.Grammatik.Parser.Modules
