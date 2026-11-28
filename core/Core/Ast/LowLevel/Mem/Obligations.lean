module

public import Core.Ast.LowLevel.Mem.Execution
public import Core.Annahme.Annahme
public import Core.Verfeinerung.Maschine
public import Core.Waechter.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine Text

def MemParseAussage (form : MemForm) : Prop :=
  ∀ text (tree : MemTree form), MemParse text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)

def MemInversionAussage (form : MemForm) : Prop :=
  ∀ (tree : MemTree form) tokens, tree.production tokens →
    ∃ pieces, Lexed tree.print pieces ∧ canonicalTokens pieces = tokens

def MemEindeutigAussage (form : MemForm) : Prop :=
  ∀ (first second : MemTree form) tokens, first.production tokens → second.production tokens →
    first = second

def MemDruckAussage (form : MemForm) : Prop :=
  ∀ tree : MemTree form,
    tree.production (tree.printPieces.map PrintedToken.value) ∧ MemParse tree.print tree

def ElaboriertMem (k : Katalog) (scope : MemScope) (tree : MemTree form) (E : MemUnit) : Prop :=
  ∃ op, elaborateMemAt k.plattform.ziel scope tree = some op ∧ E = memUnit k op

def BezeichnetMem (k : Katalog) (scope : MemScope) (text : RawText) (E : MemUnit) (form : MemForm) : Prop :=
  ∃ tree : MemTree form, MemParse text tree ∧ ElaboriertMem k scope tree E

def MemElaboriertAussage (form : MemForm) : Prop :=
  ∀ (k : Katalog) scope (tree : MemTree form) op, elaborateMemAt k.plattform.ziel scope tree = some op →
    ElaboriertMem k scope tree (memUnit k op)

def MemRealisiertAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    ∀ s c, (memUnit k op).system.kopf s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate k.plattform.ziel s c).isSome = true

def MemAnnahmeAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Annahme.RegelLokal (memUnit k op) op

def MemIdealAussage (form : MemForm) : Prop :=
  ∀ (k : Katalog) scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Ideal.RegelBestimmt (op.rule k.plattform.ziel)

def MemEinheitAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    (memUnit k op).stotterLaenge op = 0 ∧ (memUnit k op).lokalerBezug = Eq

def MemImplAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    let rule := (memUnit k op).system.regel op
    ∀ c s w plans next, rule.impl c s w plans next ↔ rule.ideal c s w plans next

def MemFortschrittAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Ideal.RegelFortschritt (memUnit k op).system op

def MemErhaltungAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    I.RegelAbgleich (memUnit k op) op ∧
      I.RegelKomponierbar (memUnit k op).einrichtung (memUnit k op).system op

def MemRegelSicherAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Sicherheit.RegelSicher (memSafetyUnit k op) op

def MemRegelAntwortSicherAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Sicherheit.RegelAntwortSicher (memSafetyUnit k op) op ∧
    ∀ t c s w middle next p trace, op.step k.plattform.ziel c s w [p] middle →
      FuehrtSchrittAus (memUnit k op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧ next.verbraucht = s.verbraucht

theorem memRegelAntwortSicher (form : MemForm) : MemRegelAntwortSicherAussage form := by
  intro k scope tree op _
  constructor
  · intro t c w vor zwischen nach p trace _ impl execute befugt
    have same := (MemInstruction.vollzugGenau (w := w) impl execute).2
    obtain ⟨_, _, _, advance⟩ := impl
    rw [same, advance]
    exact befugt
  · intro t c s w middle next p trace impl execute
    obtain ⟨rfl, rfl⟩ := MemInstruction.vollzugGenau (w := w) impl execute
    refine ⟨?_, execute.1.verbraucht⟩
    intro _ mem
    obtain ⟨_, eq⟩ := MemInstruction.schrittSpur_aussen mem
    cases eq

def MemAussenLokalAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    Annahme.AussenLokal (memUnit k op)

theorem memProgramAussenLokal (k : Katalog) (code : List MemInstruction) :
    Annahme.AussenLokal (memProgram k code) := by
  refine ⟨Aussen.zulassung_m2 _, ?_⟩
  apply Annahme.aussen_gueltig_aus_kontext
  intro run t s c w spur next step
  cases step with
  | kontext _ _ rule execute =>
    obtain ⟨op, _, impl⟩ := rule
    have step : op.step k.plattform.ziel c s w [_] _ := impl
    obtain ⟨rfl, rfl⟩ := MemInstruction.vollzugGenau step execute
    obtain ⟨_, _, _, rfl⟩ := step
    refine ⟨⟨?_, [], (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩,
      fun h => h⟩
    intro _ mem
    obtain ⟨_, eq⟩ := MemInstruction.schrittSpur_aussen mem
    cases eq

theorem memProgramRegelIsolation (k : Katalog) (code : List MemInstruction)
    (domain : Annahme.DomaenenPlan) (op : MemInstruction) :
    Annahme.RegelIsolation (memProgram k code) domain op := by
  intro t c s u next w p trace rule execute
  have step : op.step k.plattform.ziel c s w [p] u := rule
  obtain ⟨rfl, _⟩ := MemInstruction.vollzugGenau step execute
  refine ⟨fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
  intro _ mem
  obtain ⟨_, eq⟩ := MemInstruction.schrittSpur_aussen mem
  cases eq

def MemKostenAussage (form : MemForm) : Prop :=
  ∀ k scope (tree : MemTree form) op, elaborateMem scope tree = some op →
    ∀ t c s w middle next p trace, op.step k.plattform.ziel c s w [p] middle →
      FuehrtSchrittAus (memUnit k op).einrichtung t c s middle p trace next →
      trace = op.schrittSpur s c ∧ (memUnit k op).stotterLaenge op = 0

def MemSchrankenAussage : Prop := ∀ k op, (memUnit k op).schranken = .leer
def MemEtikettenAussage : Prop := ∀ k op, (memUnit k op).etiketten = .leer
def MemFlussAussage : Prop := ∀ k op, (memUnit k op).fluss = .leer

/-- An occurrence is reached in a real program after its legal prefix. This
    includes forms that need the spaces or tokens produced by earlier steps. -/
def MemErfuellbarNach (form : MemForm) (precedes : List MemInstruction → MemInstruction → Prop) : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tree : MemTree form) (op : MemInstruction)
    (env : Katalog.Umgebung) (start : AussenStart) (text : RawText) («prefix» : List MemInstruction)
    (s : MemState) (next : MemFrame),
    let E := memProgram k («prefix» ++ [op])
    precedes «prefix» op ∧ Hardware k env ∧ E.ZulStart env start ∧ Annahme.Akzeptiert E ∧
    (scope.regionen.map Subtype.val).Nodup ∧ (scope.raeume.map Subtype.val).Nodup ∧
    (scope.marken.map Subtype.val).Nodup ∧
    BezeichnetMem k scope text (memUnit k op) form ∧ MemParse text tree ∧
    elaborateMemAt k.plattform.ziel scope tree = some op ∧ E.system.IErreichbar (I.start E start).2 s ∧
    E.system.kopf s entryContext = some op ∧ op.evaluate k.plattform.ziel s entryContext = some next ∧
    E.system.ISchritt entryContext s () [op.schrittPlan s entryContext] (next.advance entryContext s) ∧
    E.system.ImplSchritt entryContext s () [op.schrittPlan s entryContext] (next.advance entryContext s)

def MemErfuellbarAussage (form : MemForm) : Prop := MemErfuellbarNach form (fun _ _ => True)

def memObligationsKern (form : MemForm) : Prop :=
  MemParseAussage form ∧ MemInversionAussage form ∧ MemEindeutigAussage form ∧ MemDruckAussage form ∧
  MemElaboriertAussage form ∧ MemRealisiertAussage form ∧ MemAnnahmeAussage form ∧
  MemIdealAussage form ∧ MemEinheitAussage form ∧ MemImplAussage form ∧ MemFortschrittAussage form ∧
  MemErhaltungAussage form ∧ MemRegelSicherAussage form ∧ MemRegelAntwortSicherAussage form ∧
  MemAussenLokalAussage form ∧ MemKostenAussage form ∧
  MemSchrankenAussage ∧ MemEtikettenAussage ∧ MemFlussAussage

theorem memElaboriert (form : MemForm) : MemElaboriertAussage form :=
  fun _ _ _ op elaborated => ⟨op, elaborated, rfl⟩

theorem memEinheit (form : MemForm) : MemEinheitAussage form := fun _ _ _ _ _ => ⟨rfl, rfl⟩

theorem memImpl (form : MemForm) : MemImplAussage form :=
  fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem memSchranken : MemSchrankenAussage := fun _ _ => rfl
theorem memEtiketten : MemEtikettenAussage := fun _ _ => rfl
theorem memFluss : MemFlussAussage := fun _ _ => rfl

end Gabbro.Core.Ast.LowLevel
