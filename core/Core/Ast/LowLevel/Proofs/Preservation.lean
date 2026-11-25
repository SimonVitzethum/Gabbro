module

public import Core.Ast.LowLevel.Obligations
public import Core.Annahme.AussenLauf

/-!
# Low-level preservation, safety and cost proofs

Invert the composed transition and replay the shared internal plan. Check the
four M7S fields, M10 commit and answer discipline, and M9 event counts.

- `ErhaltungAussage`
- `RegelSicherAussage`
- `RegelAntwortSicherAussage`
- `AussenLokalAussage`
- `KostenAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

public section

open Gabbro.Core.Maschine
open Gabbro.Core.Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
open Gabbro.Core.Katalog
open Gabbro.Core.Aussen

namespace Instruction

/-- Invert the one internal implementation rule: its plan is the shared plan
    and its successor state is the transfer applied by the instruction. -/
theorem implTransfer {k : Katalog} {op : Instruction k} {c : Kontext} {s : State k}
    {w : PUnit} {plans : List Plan} {u : State k} (h : op.impl c s w plans u) :
    ∃ transfer : Transfer k, op.evaluate s c = some transfer ∧ plans = [plan] ∧
      u = transfer.apply c s := by
  cases he : op.evaluate s c with
  | none =>
    unfold Instruction.impl at h
    rw [he] at h
    cases h
  | some transfer =>
    unfold Instruction.impl at h
    rw [he] at h
    exact ⟨transfer, rfl, h.1, h.2⟩

/-- The internal plan runs through the shared protocol with an empty trace and
    a frame-only successor state. -/
theorem vollzug {k : Katalog} (op : Instruction k) (transfer : Transfer k)
    (t : Nat) (c : Kontext) (s : State k) :
    FuehrtSchrittAus (setup k) t c s (transfer.apply c s) plan ⟨[], []⟩ (transfer.apply c s) := by
  refine ⟨?_, ?_, [], transfer.apply c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus (setup k) t c s (transfer.apply c s) .intern [] [] (transfer.apply c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (transfer.apply c s).graph
    exact Speicherfolge.nil _

/-- An executed internal plan leaves no trace and only advances the frame. -/
theorem genauInternal {k : Katalog} {t : Nat} {c : Kontext} {s u : State k}
    {trace : SchrittSpur Nat UInt8} {next : State k}
    (execute : FuehrtSchrittAus (setup k) t c s u plan trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨rahmen, _, _, _, action, memory, nextEq⟩ := execute
  cases trace with
  | mk events outside =>
    cases action
    simp only [plan, List.nil_append, schreibEreignisse, List.map_nil] at memory
    have unchanged : ∀ {recorded graph},
        Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
          recorded = [] ∧ graph = s.graph := by
      intro _ _ run
      cases run
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, graph⟩ := unchanged memory
    rw [graph] at nextEq
    rw [← rahmen.graph] at nextEq
    exact ⟨rfl, nextEq⟩

theorem vollzugGenau {k : Katalog} (op : Instruction k) {t : Nat} {c : Kontext}
    {s u : State k} {w : PUnit} {p : Plan} {trace : SchrittSpur Nat UInt8} {next : State k}
    (rule : op.impl c s w [p] u) (execute : FuehrtSchrittAus (setup k) t c s u p trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨_, _, hp, _⟩ := implTransfer (op := op) (w := w) rule
  cases (List.cons.inj hp).1
  exact Instruction.genauInternal execute

end Instruction

/-- The concrete step is matched by the ideal step at the same head. -/
theorem Instruction.abgleich {k : Katalog} (op : Instruction k) : I.RegelAbgleich (unit op) op := by
  intro hw t c w s u s' i stepPlan trace related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨transfer, evaluate, planEq, hu⟩ := Instruction.implTransfer (op := op) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨transfer, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

theorem Instruction.komponierbar {k : Katalog} (op : Instruction k) :
    I.RegelKomponierbar (unit op).einrichtung (unit op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨transfer, evaluate, planEq, hu⟩ := ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, transfer.apply c s, planEq, Instruction.vollzug op transfer t c s⟩

/-- The internal step has no accesses, releases, locks, graph change or
    outside effect, so all six M7S fields hold. -/
theorem Instruction.regelSicher {k : Katalog} (op : Instruction k) :
    Gabbro.Core.Sicherheit.RegelSicher (safetyUnit op) op := by
  intro H ρ t c w vor zwischen nach stepPlan trace head impl execute
  obtain ⟨transfer, _, planEq, _⟩ := Instruction.implTransfer (op := op) (w := w) impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := Instruction.genauInternal execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (transfer.apply c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change [][i]? = some d at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

theorem Instruction.regelAntwortSicher {k : Katalog} (op : Instruction k) :
    Sicherheit.RegelAntwortSicher (safetyUnit op) op ∧
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧
      next.verbraucht = s.verbraucht := by
  constructor
  · intro t c w vor zwischen nach p trace _ impl execute befugt
    obtain ⟨transfer, _, _, rfl⟩ := Instruction.implTransfer (op := op) (w := w) impl
    obtain ⟨_, rfl⟩ := op.vollzugGenau (w := w) impl execute
    exact befugt
  · intro t c s w middle next p trace impl execute
    obtain ⟨rfl, rfl⟩ := op.vollzugGenau (w := w) impl execute
    exact ⟨fun _ => List.not_mem_nil, execute.1.verbraucht⟩

/-- The unit admits all M2 catalogue rows and no ideal step asks a question. -/
theorem Instruction.aussenLokal {k : Katalog} (op : Instruction k) :
    Gabbro.Core.Annahme.AussenLokal (unit op) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, transfer, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := Instruction.genauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

/-- The unit charges one model step and no private steps. -/
theorem Instruction.kosten {k : Katalog} (op : Instruction k) :
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (unit op).stotterLaenge op = 0 := by
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := Instruction.implTransfer (op := op) (w := w) impl
  cases (List.cons.inj hp).1
  exact ⟨(Instruction.genauInternal execute).1, rfl⟩

theorem erhaltung (form : Form) : ErhaltungAussage form := by
  intro k scope tree op _
  exact ⟨Instruction.abgleich op, Instruction.komponierbar op⟩

theorem regelSicher (form : Form) : RegelSicherAussage form := by
  intro k scope tree op _
  exact Instruction.regelSicher op

theorem regelAntwortSicher (form : Form) : RegelAntwortSicherAussage form := by
  intro k scope tree op _
  exact Instruction.regelAntwortSicher op

theorem aussenLokal (form : Form) : AussenLokalAussage form := by
  intro k scope tree op _
  exact Instruction.aussenLokal op

theorem kosten (form : Form) : KostenAussage form := by
  intro k scope tree op _
  exact Instruction.kosten op

end

end Gabbro.Core.Ast.LowLevel
