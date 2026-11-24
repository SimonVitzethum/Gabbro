module

public import Core.Ast.LowLevel.Exec.Execution
public import Core.Annahme.Annahme
public import Core.Verfeinerung.Maschine
public import Core.Waechter.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine Text

def ExecParseAussage (form : ExecForm) : Prop :=
  ∀ text (tree : ExecTree form), ExecParse text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)

def ExecInversionAussage (form : ExecForm) : Prop :=
  ∀ (tree : ExecTree form) tokens, tree.production tokens →
    ∃ pieces, Lexed tree.print pieces ∧ canonicalTokens pieces = tokens

def ExecEindeutigAussage (form : ExecForm) : Prop :=
  ∀ (first second : ExecTree form) tokens, first.production tokens → second.production tokens →
    first = second

def ExecDruckAussage (form : ExecForm) : Prop :=
  ∀ tree : ExecTree form,
    tree.production (tree.printPieces.map PrintedToken.value) ∧ ExecParse tree.print tree

def ElaboriertExec (k : Katalog) (scope : ExecScope) (tree : ExecTree form) (E : ExecUnit) : Prop :=
  ∃ op, elaborateExec scope tree = some op ∧ E = execUnit k op

def BezeichnetExec (k : Katalog) (scope : ExecScope) (text : RawText) (E : ExecUnit) (form : ExecForm) : Prop :=
  ∃ tree : ExecTree form, ExecParse text tree ∧ ElaboriertExec k scope tree E

def ExecElaboriertAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    ElaboriertExec k scope tree (execUnit k op)

def ExecRealisiertAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    ∀ s c, (execUnit k op).system.kopf s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate s c).isSome = true

def ExecAnnahmeAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Annahme.RegelLokal (execUnit k op) op

def ExecIdealAussage (form : ExecForm) : Prop :=
  ∀ (k : Katalog) scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Ideal.RegelBestimmt op.rule

def ExecEinheitAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    (execUnit k op).stotterLaenge op = 0 ∧ (execUnit k op).lokalerBezug = Eq

def ExecImplAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    let rule := (execUnit k op).system.regel op
    ∀ c s w plans next, rule.impl c s w plans next ↔ rule.ideal c s w plans next

def ExecFortschrittAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Ideal.RegelFortschritt (execUnit k op).system op

def ExecErhaltungAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    I.RegelAbgleich (execUnit k op) op ∧
      I.RegelKomponierbar (execUnit k op).einrichtung (execUnit k op).system op

def ExecRegelSicherAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Sicherheit.RegelSicher (execSafetyUnit k op) op

def ExecRegelAntwortSicherAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Sicherheit.RegelAntwortSicher (execSafetyUnit k op) op ∧
    ∀ t c s w middle next p trace, op.step c s w [p] middle →
      FuehrtSchrittAus (execUnit k op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧ next.verbraucht = s.verbraucht

def ExecAussenLokalAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    Annahme.AussenLokal (execUnit k op)

def ExecKostenAussage (form : ExecForm) : Prop :=
  ∀ k scope (tree : ExecTree form) op, elaborateExec scope tree = some op →
    ∀ t c s w middle next p trace, op.step c s w [p] middle →
      FuehrtSchrittAus (execUnit k op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (execUnit k op).stotterLaenge op = 0

def ExecSchrankenAussage : Prop := ∀ k op, (execUnit k op).schranken = .leer
def ExecEtikettenAussage : Prop := ∀ k op, (execUnit k op).etiketten = .leer
def ExecFlussAussage : Prop := ∀ k op, (execUnit k op).fluss = .leer

/-- An occurrence is reached in a real program after its legal prefix. This
    includes forms that need the states declared by earlier steps. -/
def ExecErfuellbarNach (form : ExecForm) (precedes : List ExecInstruction → ExecInstruction → Prop) : Prop :=
  ∃ (k : Katalog) (scope : ExecScope) (tree : ExecTree form) (op : ExecInstruction)
    (env : Katalog.Umgebung) (start : AussenStart) (text : RawText) («prefix» : List ExecInstruction)
    (s : ExecState) (next : ExecFrame),
    let E := execProgram k («prefix» ++ [op])
    precedes «prefix» op ∧ Hardware k env ∧ E.ZulStart env start ∧ Annahme.Akzeptiert E ∧
    (scope.states.map Subtype.val).Nodup ∧ (scope.spaces.map Subtype.val).Nodup ∧
    (scope.stapel.map Subtype.val).Nodup ∧ (scope.entries.map Subtype.val).Nodup ∧
    BezeichnetExec k scope text (execUnit k op) form ∧ ExecParse text tree ∧
    elaborateExec scope tree = some op ∧ E.system.IErreichbar (I.start E start).2 s ∧
    E.system.kopf s entryContext = some op ∧ op.evaluate s entryContext = some next ∧
    E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) ∧
    E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s)

def ExecErfuellbarAussage (form : ExecForm) : Prop := ExecErfuellbarNach form (fun _ _ => True)

def execObligationsKern (form : ExecForm) : Prop :=
  ExecParseAussage form ∧ ExecInversionAussage form ∧ ExecEindeutigAussage form ∧
  ExecDruckAussage form ∧ ExecElaboriertAussage form ∧ ExecRealisiertAussage form ∧
  ExecAnnahmeAussage form ∧ ExecIdealAussage form ∧ ExecEinheitAussage form ∧
  ExecImplAussage form ∧ ExecFortschrittAussage form ∧ ExecErhaltungAussage form ∧
  ExecRegelSicherAussage form ∧ ExecRegelAntwortSicherAussage form ∧
  ExecAussenLokalAussage form ∧ ExecKostenAussage form ∧
  ExecSchrankenAussage ∧ ExecEtikettenAussage ∧ ExecFlussAussage

theorem execElaboriert (form : ExecForm) : ExecElaboriertAussage form :=
  fun _ _ _ op elaborated => ⟨op, elaborated, rfl⟩

theorem execEinheit (form : ExecForm) : ExecEinheitAussage form := fun _ _ _ _ _ => ⟨rfl, rfl⟩

theorem execImpl (form : ExecForm) : ExecImplAussage form :=
  fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem execSchranken : ExecSchrankenAussage := fun _ _ => rfl
theorem execEtiketten : ExecEtikettenAussage := fun _ _ => rfl
theorem execFluss : ExecFlussAussage := fun _ _ => rfl

end Gabbro.Core.Ast.LowLevel
