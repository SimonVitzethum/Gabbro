module

public import Core.Ast.Semantik.Beispiele
public import Core.Ast.Semantik.BatchRegistry
public import Core.Ast.Semantik.LocalEffects
public import Core.Ast.Semantik.ProgramRegistry

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
    | laeuft =>
      cases returned : (s.lokal c).rueckgabe with
      | none =>
        simp only [status, returned] at head
        split at head
        · exact head
        · cases head
      | some _ =>
        simp only [status, returned] at head
        cases head
    | beendet _ =>
      rw [status] at head
      cases head
  · cases head

def Quellform.kernStatements {Context : Type} {cat : Context → Category} {args : Context → Type}
    (forms : (scope : Context) → Quellform (cat scope) (args scope))
    (joint : Prop) (constructor : Name) : RegistryStatements constructor .core :=
  let shared := Quellform.statements forms joint constructor
  ⟨.core (AusElaborierung ∧ ∀ scope, (forms scope).RegelAmOrt),
    shared.acceptanceRule, shared.idealRule, shared.unitsAndCommutation,
    shared.implementationRule, shared.preservation, shared.jointlySatisfiable⟩

def Befehl.programConstructor : Befehl → Option Name
  | .bindeWert .. => some ``Befehl.bindeWert
  | .definiere .. => some ``Befehl.definiere
  | .rufe .. => some ``Befehl.rufe
  | .rueckVoid .. => some ``Befehl.rueckVoid
  | .pruefeMass .. => some ``Befehl.pruefeMass
  | .setzePasszahl .. => some ``Befehl.setzePasszahl
  | .whileTest .. => some ``Befehl.whileTest
  | .forAnfang .. => some ``Befehl.forAnfang
  | .forTest .. => some ``Befehl.forTest
  | .forNaechster .. => some ``Befehl.forNaechster
  | .zurueckSprung .. => some ``Befehl.zurueckSprung
  | .starte .. => some ``Befehl.starte
  | .ende .. => some ``Befehl.ende
  | _ => none

def programConstructors : List Name :=
  [``Befehl.bindeWert,
    ``Befehl.definiere,
    ``Befehl.rufe,
    ``Befehl.rueckVoid,
    ``Befehl.pruefeMass,
    ``Befehl.setzePasszahl,
    ``Befehl.whileTest,
    ``Befehl.forAnfang,
    ``Befehl.forTest,
    ``Befehl.forNaechster,
    ``Befehl.zurueckSprung,
    ``Befehl.starte,
    ``Befehl.ende]

def programKernStatements (constructor : Name) : RegistryStatements constructor .core where
  realization := .core AusElaborierung
  acceptanceRule := ∀ (p : Fragment) (platform : Plattform) (b : Befehl), b.programConstructor = some constructor →
    Annahme.RegelLokal (p.einheit platform) b
  idealRule := ∀ b : Befehl, b.programConstructor = some constructor →
    Ideal.RegelBestimmt b.regel ∧ ∀ c s w plans u, b.ideal c s w plans u ↔ plans = [plan] ∧ u = b.nach c s
  unitsAndCommutation := ∀ (p : Fragment) (platform : Plattform) (b : Befehl), b.programConstructor = some constructor →
    (p.einheit platform).stotterLaenge b = 0 ∧ ∀ other, Kommutation b.vor b.danach other
  implementationRule := ∀ b : Befehl, b.programConstructor = some constructor →
    ∀ c s w plans u, b.impl c s w plans u ↔ plans = [plan] ∧ u = b.nach c s
  preservation := ∀ (p : Fragment) platform b, b.programConstructor = some constructor →
    p.klauseln.invariant = [] →
    I.RegelAbgleich (p.einheit platform) b ∧ Ideal.RegelFortschritt (p.einheit platform).system b ∧
      I.RegelKomponierbar (p.einheit platform).einrichtung (p.einheit platform).system b ∧
      Sicherheit.RegelSicher (p.sicherheitsEinheit platform) b
  jointlySatisfiable := ∀ platform start,
    ∃ (category : Category) (tree : category.Tree) (text : Text.RawText) (s : Zustand) (b : Befehl),
      b.programConstructor = some constructor ∧ Ast.Parse text tree ∧
      let E := elaborieren platform tree
      E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s eintritt = some b ∧
        E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) ∧
        E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s)

-- Mirror binary_erfuellbar, selecting a source occurrence of each auxiliary program instruction.
theorem programKern_erfuellbar (constructor : Name) (registered : constructor ∈ programConstructors) :
    (programKernStatements constructor).jointlySatisfiable := by
  sorry

def programKernProofs (constructor : Name) (registered : constructor ∈ programConstructors) :
    RegistryEntry constructor ⟨.core, programKernStatements constructor⟩ where
  realization := .core aus_elaborierung
  acceptanceRule := fun p platform b _ => b.lokal (p.einheit platform) rfl
  idealRule := fun b _ => ⟨b.bestimmt, fun _ _ _ _ _ => Iff.rfl⟩
  unitsAndCommutation := fun _ _ b _ => ⟨rfl, b.kommutation⟩
  implementationRule := fun _ _ _ _ _ _ _ => Iff.rfl
  preservation := fun p platform b _ inv => ⟨b.abgleich p platform, b.fortschritt p,
    b.komponierbar p platform, Befehl.sicher p platform inv b⟩
  jointlySatisfiable := programKern_erfuellbar constructor registered

def befehlSchema (constructor : Name) : RegistrySchema constructor :=
  if constructor = ``Befehl.literal then
    ⟨.core, Quellform.kernStatements literalForm LiteralErfuellbar constructor⟩
  else if constructor = ``Befehl.binaer then
    ⟨.core, Quellform.kernStatements binaryForm BinaryErfuellbar constructor⟩
  else if constructor = ``Befehl.binden then
    ⟨.core, Quellform.kernStatements letForm LetErfuellbar constructor⟩
  else if constructor = ``Befehl.wahrheitswert then
    ⟨.core, Quellform.kernStatements trueLitForm trueLitJoint constructor⟩
  else if constructor = ``Befehl.lesen then
    ⟨.core, Quellform.kernStatements variableForm variableJoint constructor⟩
  else if constructor = ``Befehl.negativ then
    ⟨.core, Quellform.kernStatements negativeLitForm negativeLitJoint constructor⟩
  else if constructor = ``Befehl.negieren then
    ⟨.core, Quellform.kernStatements negForm negJoint constructor⟩
  else if constructor = ``Befehl.verneinen then
    ⟨.core, Quellform.kernStatements notValueForm notValueJoint constructor⟩
  else if constructor = ``Befehl.teilen then
    ⟨.core, Quellform.kernStatements divisionForm divisionJoint constructor⟩
  else if constructor = ``Befehl.vergleichen then
    ⟨.core, Quellform.kernStatements comparisonForm comparisonJoint constructor⟩
  else if constructor = ``Befehl.springeWenn then
    ⟨.core, Quellform.kernStatements logicForm logicJoint constructor⟩
  else if constructor = ``Befehl.zuweisen then
    ⟨.core, Quellform.kernStatements assignVarForm assignVarJoint constructor⟩
  else if constructor = ``Befehl.zurueck then
    ⟨.core, Quellform.kernStatements returnValueForm returnValueJoint constructor⟩
  else if constructor = ``Befehl.springe then
    ⟨.core, Quellform.kernStatements thenJumpForm thenJumpJoint constructor⟩
  else if constructor = ``Befehl.blockEnde then
    ⟨.core, Quellform.kernStatements bracedForm bracedJoint constructor⟩
  else if constructor = ``Befehl.baueArray then
    ⟨.core, Quellform.kernStatements arrayValueForm ArrayValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.liesArray then
    ⟨.core, Quellform.kernStatements arrayIndexForm ArrayIndexErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.baueTupel then
    ⟨.core, Quellform.kernStatements tupleValueForm TupleValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.liesTupelfeld then
    ⟨.core, Quellform.kernStatements tupleFieldForm TupleFieldErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.baueRecord then
    ⟨.core, Quellform.kernStatements recordValueForm RecordValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.liesRecordFeld then
    ⟨.core, Quellform.kernStatements recordFieldForm RecordFieldErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.bindeTupel then
    ⟨.core, Quellform.kernStatements tupleBindForm TupleBindErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.setzeRecordFeld then
    ⟨.core, Quellform.kernStatements assignFieldForm AssignFieldErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.definiereRecord then
    ⟨.core, Quellform.kernStatements recordDeclForm RecordDeclErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.baueVariante then
    ⟨.core, Quellform.kernStatements variantValueForm VariantValueErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.waehleVariante then
    ⟨.core, Quellform.kernStatements variantMatchForm VariantMatchErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.definiereVariante then
    ⟨.core, Quellform.kernStatements taggedDeclForm TaggedDeclErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.textLiteral then
    ⟨.core, Quellform.kernStatements textLiteralForm TextLiteralErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.textConcat then
    ⟨.core, Quellform.kernStatements textConcatForm TextConcatErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.textIndex then
    ⟨.core, Quellform.kernStatements textIndexForm TextIndexErfuellbarAmAussage constructor⟩
  else if constructor = ``Befehl.substring then
    ⟨.core, Quellform.kernStatements substringForm SubstringErfuellbarAmAussage constructor⟩
  else if constructor ∈ programConstructors then
    ⟨.core, programKernStatements constructor⟩
  else nichtSpezifiziert constructor

-- Mirror kernLiteralEntry by reducing befehlSchema after selecting an auxiliary instruction.
theorem befehlSchema_program (constructor : Name) (registered : constructor ∈ programConstructors) :
    befehlSchema constructor = ⟨.core, programKernStatements constructor⟩ := by
  sorry

def kern_bindeWert : RegistryEntry ``Befehl.bindeWert (befehlSchema ``Befehl.bindeWert) := by
  have registered : ``Befehl.bindeWert ∈ programConstructors := List.Mem.head _
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_definiere : RegistryEntry ``Befehl.definiere (befehlSchema ``Befehl.definiere) := by
  have registered : ``Befehl.definiere ∈ programConstructors := List.Mem.tail _ (List.Mem.head _)
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_rufe : RegistryEntry ``Befehl.rufe (befehlSchema ``Befehl.rufe) := by
  have registered : ``Befehl.rufe ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_rueckVoid : RegistryEntry ``Befehl.rueckVoid (befehlSchema ``Befehl.rueckVoid) := by
  have registered : ``Befehl.rueckVoid ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_pruefeMass : RegistryEntry ``Befehl.pruefeMass (befehlSchema ``Befehl.pruefeMass) := by
  have registered : ``Befehl.pruefeMass ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_setzePasszahl : RegistryEntry ``Befehl.setzePasszahl (befehlSchema ``Befehl.setzePasszahl) := by
  have registered : ``Befehl.setzePasszahl ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_whileTest : RegistryEntry ``Befehl.whileTest (befehlSchema ``Befehl.whileTest) := by
  have registered : ``Befehl.whileTest ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_forAnfang : RegistryEntry ``Befehl.forAnfang (befehlSchema ``Befehl.forAnfang) := by
  have registered : ``Befehl.forAnfang ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_forTest : RegistryEntry ``Befehl.forTest (befehlSchema ``Befehl.forTest) := by
  have registered : ``Befehl.forTest ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_forNaechster : RegistryEntry ``Befehl.forNaechster (befehlSchema ``Befehl.forNaechster) := by
  have registered : ``Befehl.forNaechster ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_zurueckSprung : RegistryEntry ``Befehl.zurueckSprung (befehlSchema ``Befehl.zurueckSprung) := by
  have registered : ``Befehl.zurueckSprung ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_starte : RegistryEntry ``Befehl.starte (befehlSchema ``Befehl.starte) := by
  have registered : ``Befehl.starte ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def kern_ende : RegistryEntry ``Befehl.ende (befehlSchema ``Befehl.ende) := by
  have registered : ``Befehl.ende ∈ programConstructors := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  rw [befehlSchema_program _ registered]
  exact programKernProofs _ registered

def Quellform.kernEintrag {Context : Type} {cat : Context → Category} {args : Context → Type}
    {forms : (scope : Context) → Quellform (cat scope) (args scope)} {joint : Prop}
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

def kern_wahrheitswert : RegistryEntry ``Befehl.wahrheitswert (befehlSchema ``Befehl.wahrheitswert) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "wahrheitswert") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "wahrheitswert") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "wahrheitswert") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag trueLitProofs

def kern_lesen : RegistryEntry ``Befehl.lesen (befehlSchema ``Befehl.lesen) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "lesen") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "lesen") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "lesen") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "lesen") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag variableProofs

def kern_negativ : RegistryEntry ``Befehl.negativ (befehlSchema ``Befehl.negativ) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "negativ") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativ") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativ") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativ") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negativ") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag negativeLitProofs

def kern_negieren : RegistryEntry ``Befehl.negieren (befehlSchema ``Befehl.negieren) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "negieren") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negieren") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negieren") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negieren") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negieren") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "negieren") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag negProofs

def kern_verneinen : RegistryEntry ``Befehl.verneinen (befehlSchema ``Befehl.verneinen) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "verneinen") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "verneinen") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag notValueProofs

def kern_teilen : RegistryEntry ``Befehl.teilen (befehlSchema ``Befehl.teilen) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "teilen") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "teilen") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag divisionProofs

def kern_vergleichen : RegistryEntry ``Befehl.vergleichen (befehlSchema ``Befehl.vergleichen) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "vergleichen") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "vergleichen") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag comparisonProofs

def kern_springeWenn : RegistryEntry ``Befehl.springeWenn (befehlSchema ``Befehl.springeWenn) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "springeWenn") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springeWenn") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag logicProofs

def kern_zuweisen : RegistryEntry ``Befehl.zuweisen (befehlSchema ``Befehl.zuweisen) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "zuweisen") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zuweisen") (b := "springeWenn") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag assignVarProofs

def kern_zurueck : RegistryEntry ``Befehl.zurueck (befehlSchema ``Befehl.zurueck) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "zurueck") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "springeWenn") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "zurueck") (b := "zuweisen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag returnValueProofs

def kern_springe : RegistryEntry ``Befehl.springe (befehlSchema ``Befehl.springe) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "springe") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "springeWenn") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "zuweisen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "springe") (b := "zurueck") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag thenJumpProofs

def kern_blockEnde : RegistryEntry ``Befehl.blockEnde (befehlSchema ``Befehl.blockEnde) := by
  rw [befehlSchema,
    ite_eq_right (differentLabels (a := "blockEnde") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "springeWenn") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "zuweisen") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "zurueck") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_right (differentLabels (a := "blockEnde") (b := "springe") (by intro same; simp only [String.reduceEq] at same)),
    ite_eq_left rfl]
  exact Quellform.kernEintrag bracedProofs

end Gabbro.Core.Ast.Semantik
