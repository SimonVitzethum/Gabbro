module

public import Core.Ast.Semantik.Beispiele

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter
open Lean (Name)

/-- Every executing instruction of an elaborated unit came from its reference
    tree at the acting context's indicated instruction position. -/
def AusElaborierung : Prop :=
  ∀ (platform : Plattform) (category : Category) (tree : category.Tree) (E : Einheit),
    Elaboriert platform tree E → ∀ s c b, E.system.kopf s c = some b →
      (fragment category tree).code[(s.lokal c).pc]? = some b

theorem aus_elaborierung : AusElaborierung := by
  intro platform category tree E meaning s c b head
  have same := elab_vollstaendig meaning
  subst E
  change kopf (fragment category tree).code s c = some b at head
  unfold kopf at head
  split at head
  · cases status : s.status c with
    | ruht =>
      rw [status] at head
      cases head
    | laeuft => rwa [status] at head
    | beendet _ =>
      rw [status] at head
      cases head
  · cases head

def Quellform.kernStatements {cat : Scope → Category} {args : Scope → Type}
    (forms : (scope : Scope) → Quellform (cat scope) (args scope))
    (joint : Prop) (constructor : Name) : RegistryStatements constructor .core :=
  let shared := Quellform.statements forms joint constructor
  ⟨.core (AusElaborierung ∧ ∀ scope, (forms scope).RegelAmOrt),
    shared.acceptanceRule, shared.idealRule, shared.unitsAndCommutation,
    shared.implementationRule, shared.preservation, shared.jointlySatisfiable⟩

def befehlSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Befehl.literal then
    ⟨.core, Quellform.kernStatements literalForm LiteralErfuellbar constructor⟩
  else if constructor = ``Befehl.binaer then
    ⟨.core, Quellform.kernStatements binaryForm BinaryErfuellbar constructor⟩
  else if constructor = ``Befehl.binden then
    ⟨.core, Quellform.kernStatements letForm LetErfuellbar constructor⟩
  else nichtSpezifiziert constructor

def Quellform.kernEintrag {cat : Scope → Category} {args : Scope → Type}
    {forms : (scope : Scope) → Quellform (cat scope) (args scope)} {joint : Prop}
    {sourceName constructor : Name}
    (source : RegistryEntry sourceName ⟨.surface, Quellform.statements forms joint sourceName⟩) :
    RegistryEntry constructor ⟨.core, Quellform.kernStatements forms joint constructor⟩ where
  realization := .core ⟨aus_elaborierung, fun scope => (source.idealRule scope).1⟩
  acceptanceRule := source.acceptanceRule
  idealRule := source.idealRule
  unitsAndCommutation := source.unitsAndCommutation
  implementationRule := source.implementationRule
  preservation := source.preservation
  jointlySatisfiable := source.jointlySatisfiable

def kernLiteralEntry : RegistryEntry ``Befehl.literal (befehlSchema ``Befehl.literal) := by
  rw [befehlSchema, ite_eq_left rfl]
  have source := literalEntry
  rw [exprSchema, ite_eq_left rfl] at source
  exact Quellform.kernEintrag source

def kernBinaryEntry : RegistryEntry ``Befehl.binaer (befehlSchema ``Befehl.binaer) := by
  have different : (``Befehl.binaer : Name) ≠ ``Befehl.literal := by
    intro same
    have label : "binaer" = "literal" := (Name.str.inj same).2
    simp only [String.reduceEq] at label
  rw [befehlSchema, ite_eq_right different, ite_eq_left rfl]
  have source := binaryEntry
  rw [exprSchema, ite_eq_right binary_ne_lit, ite_eq_left rfl] at source
  exact Quellform.kernEintrag source

def kernLetEntry : RegistryEntry ``Befehl.binden (befehlSchema ``Befehl.binden) := by
  have noLiteral : (``Befehl.binden : Name) ≠ ``Befehl.literal := by
    intro same
    have label : "binden" = "literal" := (Name.str.inj same).2
    simp only [String.reduceEq] at label
  have noBinary : (``Befehl.binden : Name) ≠ ``Befehl.binaer := by
    intro same
    have label : "binden" = "binaer" := (Name.str.inj same).2
    simp only [String.reduceEq] at label
  rw [befehlSchema, ite_eq_right noLiteral, ite_eq_right noBinary, ite_eq_left rfl]
  have source := letEntry
  rw [stmtSchema, ite_eq_left rfl] at source
  exact Quellform.kernEintrag source

end Gabbro.Core.Ast.Semantik
