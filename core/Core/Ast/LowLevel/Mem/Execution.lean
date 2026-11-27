module

public import Core.Ast.LowLevel.Mem.Meaning
public import Core.Ast.LowLevel.Execution
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

abbrev MemUnit := Maschine.Einheit PUnit Nat UInt8 PUnit MemFrame PUnit PUnit PUnit MemInstruction

def MemFrame.advance (next : MemFrame) (c : Kontext) (s : MemState) : MemState :=
  { s with lokal := Function.update s.lokal c { next with pc := (s.lokal c).pc + 1 } }

/-- The effect uses the same named token as evaluation of `flushSpace`. The evaluator
    remains the guard on whether the plan may execute. -/
def MemInstruction.abschluss (op : MemInstruction) (s : MemState) (c : Kontext) :
    Option Zuruecknahme :=
  match op with
  | .flushSpace name => ((s.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd
  | _ => none

def MemInstruction.schrittPlan (op : MemInstruction) (s : MemState) (c : Kontext) : Plan :=
  { plan with aktion := (op.abschluss s c).elim .intern .ruecknahmeAbschliessen }

def MemInstruction.schrittSpur (op : MemInstruction) (s : MemState) (c : Kontext) :
    SchrittSpur Nat UInt8 :=
  ⟨[], ((op.abschluss s c).map (.ruecknahmeAbgeschlossen s.epoche)).toList⟩

def MemInstruction.step (target : ZielDaten) (op : MemInstruction) (c : Kontext) (s : MemState)
    (_ : PUnit.{1}) (plans : List Plan) (next : MemState) : Prop :=
  ∃ frame, op.evaluate target s c = some frame ∧
    plans = [op.schrittPlan s c] ∧ next = frame.advance c s

def MemInstruction.rule (target : ZielDaten) (op : MemInstruction) : Regel MemState Plan PUnit :=
  ⟨op.step target, op.step target⟩

def memHead (target : ZielDaten) (code : List MemInstruction) (s : MemState) (c : Kontext) :
    Option MemInstruction :=
  if c = entryContext then
    match s.status c with
    | .laeuft => do
      let op ← code[(s.lokal c).pc]?
      if (op.evaluate target s c).isSome then some op else none
    | .ruht | .beendet _ => none
  else none

def memBoot (regions : List Strecke) (core : Option Nat) :
    Startdaten UInt8 PUnit MemFrame PUnit :=
  let slots := regions.zipIdx |>.map fun (extent, i) => some (⟨extent, [⟨i, 0⟩]⟩ : MemRegion)
  ⟨fun c => if c = entryContext then { regions := slots } else {},
    fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩, ⟨fun i => decide (i < regions.length), fun _ => 0⟩⟩

def memSetup : Einrichtung PUnit Nat UInt8 PUnit MemFrame PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => memBoot [] (some 0), fun _ _ => 0, id⟩,
    fun _ => 0, fun _ _ _ => none⟩

namespace MemInstruction

private theorem graphEreignisse_schrittSpur (op : MemInstruction) (s : MemState) (c : Kontext) :
    (op.schrittPlan s c).aktion.graphEreignisse (op.schrittSpur s c).aussen = [] := by
  cases h : op.abschluss s c <;> simp only [schrittPlan, schrittSpur, h, Option.elim, Option.map, Option.toList] <;> rfl

theorem vollzug (op : MemInstruction) (frame : MemFrame) (t : Nat) (c : Kontext) (s : MemState) :
    FuehrtSchrittAus memSetup t c s (frame.advance c s) (op.schrittPlan s c)
      (op.schrittSpur s c) (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    cases hl
  · cases h : op.abschluss s c with
    | none => simpa only [schrittPlan, schrittSpur, h, Option.elim, Option.map, Option.toList] using
        (FuehrtAus.intern (e := memSetup) (t := t) (c := c) (s := s) (u := frame.advance c s))
    | some token => simpa only [schrittPlan, schrittSpur, h, Option.elim, Option.map, Option.toList] using
        (FuehrtAus.ruecknahmeAbschliessen (e := memSetup) (t := t) (c := c) (s := s)
          (u := frame.advance c s) token)
  · rw [graphEreignisse_schrittSpur]
    exact Speicherfolge.nil _

theorem vollzugGenau {target} {op : MemInstruction} {t : Nat} {c : Kontext}
    {s u : MemState} {w : PUnit} {p : Plan} {trace : SchrittSpur Nat UInt8} {next : MemState}
    (rule : op.step target c s w [p] u) (execute : FuehrtSchrittAus memSetup t c s u p trace next) :
    trace = op.schrittSpur s c ∧ next = u := by
  obtain ⟨_, _, plans, _⟩ := rule
  cases (List.cons.inj plans).1
  obtain ⟨rahmen, _, locks, v, action, memory, successor⟩ := execute
  have effect : locks = [] ∧ trace.aussen = (op.schrittSpur s c).aussen ∧ v = u := by
    cases h : op.abschluss s c with
    | none =>
      have step : FuehrtAus memSetup t c s u .intern locks trace.aussen v := by
        simpa only [schrittPlan, h, Option.elim] using action
      generalize trace.aussen = events at step
      cases step
      exact ⟨rfl, by simp only [schrittSpur, h, Option.map, Option.toList], rfl⟩
    | some token =>
      have step : FuehrtAus memSetup t c s u (.ruecknahmeAbschliessen token) locks trace.aussen v := by
        simpa only [schrittPlan, h, Option.elim] using action
      generalize trace.aussen = events at step
      cases step
      exact ⟨rfl, by simp only [schrittSpur, h, Option.map, Option.toList], rfl⟩
  rw [effect.1, effect.2.1, graphEreignisse_schrittSpur] at memory
  have empty : Speicherfolge s.initial (.kontext c) s.graph [] trace.speicher next.graph := memory
  have unchanged : ∀ {events graph},
      Speicherfolge s.initial (.kontext c) s.graph [] events graph →
        events = [] ∧ graph = s.graph := by
    intro _ _ h
    cases h
    exact ⟨rfl, rfl⟩
  obtain ⟨recorded, graph⟩ := unchanged empty
  refine ⟨?_, ?_⟩
  · cases trace
    simp_all only [schrittSpur, SchrittSpur.mk.injEq]
  · rw [successor, graph, effect.2.2, ← rahmen.graph]

theorem schrittSpur_aussen {op : MemInstruction} {s : MemState} {c : Kontext} {e : Ereignis}
    (mem : e ∈ (op.schrittSpur s c).aussen) :
    ∃ token, e = .ruecknahmeAbgeschlossen s.epoche token := by
  cases h : op.abschluss s c with
  | none => exact (List.not_mem_nil (by simpa only [schrittSpur, h, Option.map, Option.toList] using mem)).elim
  | some token =>
    have hmem : e ∈ [Ereignis.ruecknahmeAbgeschlossen s.epoche token] := by
      simpa only [schrittSpur, h, Option.map, Option.toList] using mem
    exact ⟨token, List.mem_singleton.mp hmem⟩

end MemInstruction

def memProgram (k : Katalog) (code : List MemInstruction) : MemUnit :=
  let target := k.plattform.ziel
  { katalog := k
    bild := image
    einrichtung := memSetup
    system := ⟨MemInstruction.rule target, memHead target code,
      fun s c => memHead target code s c = none, fun _ _ _ => False⟩
    startdaten := fun start => memBoot start.regions (start.assignment 0)
    startmedium := medium
    laden := fun start load =>
      if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
        let d := memBoot start.regions (start.assignment 0)
        some (Zustand.start d.lokal d.status d.kerne d.rechte memSetup.initial (.leer (medium start)))
      else none
    lokalerBezug := Eq
    stotterLaenge := fun _ => 0
    quelltabellen := ⟨.leer, fun _ _ _ => False⟩ }

theorem memKontextSchrittGenau {k : Katalog} {code : List MemInstruction} {hw : HwLauf}
    {t : Nat} {s next : MemState} {c : Kontext} {w : PUnit} {trace : SchrittSpur Nat UInt8}
    (step : ImplSchritt memSetup (memProgram k code).system k hw t s (.kontext c w, trace) next) :
    ∃ op frame, (memProgram k code).system.kopf s c = some op ∧
      op.evaluate k.plattform.ziel s c = some frame ∧
      trace = op.schrittSpur s c ∧ next = frame.advance c s := by
  cases step with
  | kontext _ _ rule execute =>
    obtain ⟨op, head, impl⟩ := rule
    obtain ⟨traceEq, successor⟩ := MemInstruction.vollzugGenau
      (target := k.plattform.ziel) (op := op) (w := w) impl execute
    obtain ⟨frame, eval, _, advance⟩ := impl
    exact ⟨op, frame, head, eval, traceEq, successor.trans advance⟩

def memUnit (k : Katalog) (op : MemInstruction) : MemUnit := memProgram k [op]

def memSafetyUnit (k : Katalog) (op : MemInstruction) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit MemFrame PUnit PUnit PUnit MemInstruction :=
  ⟨memUnit k op, []⟩

end Gabbro.Core.Ast.LowLevel
