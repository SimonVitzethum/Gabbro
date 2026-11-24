module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine
open Gabbro.Core.Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)
open Gabbro.Core.Aussen

namespace MemInstruction

theorem implTransfer {k : Katalog} {op : MemInstruction} {c : Kontext} {s : MemState}
    {w : PUnit} {plans : List Plan} {u : MemState}
    (h : (MemInstruction.rule k.plattform.ziel op).impl c s w plans u) :
    ∃ frame : MemFrame, op.evaluate k.plattform.ziel s c = some frame ∧ plans = [plan] ∧
      u = frame.advance c s := by
  cases he : op.evaluate k.plattform.ziel s c with
  | none =>
      dsimp [MemInstruction.rule, MemInstruction.step] at h
      rcases h with ⟨frame, heq, _, _⟩
      rw [he] at heq
      cases heq
  | some frame =>
      dsimp [MemInstruction.rule, MemInstruction.step] at h
      rw [he] at h
      rcases h with ⟨frame', heq, hp, hu⟩
      cases heq
      exact ⟨frame, rfl, hp, hu⟩

theorem vollzug {k : Katalog} (op : MemInstruction) (frame : MemFrame)
    (t : Nat) (c : Kontext) (s : MemState) :
    FuehrtSchrittAus memSetup t c s (frame.advance c s) plan ⟨[], []⟩ (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus memSetup t c s (frame.advance c s) .intern [] [] (frame.advance c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (frame.advance c s).graph
    exact Speicherfolge.nil _

theorem genauInternal {k : Katalog} {t : Nat} {c : Kontext} {s u : MemState}
    {trace : SchrittSpur Nat UInt8} {next : MemState}
    (execute : FuehrtSchrittAus memSetup t c s u plan trace next) :
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

theorem vollzugGenau {k : Katalog} (op : MemInstruction) {t : Nat} {c : Kontext}
    {s u : MemState} {w : PUnit} {p : Plan} {trace : SchrittSpur Nat UInt8} {next : MemState}
    (rule : (MemInstruction.rule k.plattform.ziel op).impl c s w [p] u)
    (execute : FuehrtSchrittAus memSetup t c s u p trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨_, _, hp, _⟩ := implTransfer (k := k) (op := op) (w := w) rule
  cases (List.cons.inj hp).1
  exact genauInternal (k := k) execute

theorem abgleich {k : Katalog} (op : MemInstruction) : I.RegelAbgleich (memUnit k op) op := by
  intro hw t c w s u s' i pl spur related crash kann head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := implTransfer (k := k) (op := op) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext crash kann ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

theorem komponierbar {k : Katalog} (op : MemInstruction) :
    I.RegelKomponierbar (memUnit k op).einrichtung (memUnit k op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := ideal
  subst u
  dsimp [memUnit, memProgram]
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, vollzug (k := k) op frame t c s⟩

theorem regelSicher {k : Katalog} (op : MemInstruction) :
    Gabbro.Core.Sicherheit.RegelSicher (memSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach pl trace head impl execute
  obtain ⟨frame, _, planEq, _⟩ := implTransfer (k := k) (op := op) (w := w) impl
  subst zwischen
  cases (List.cons.inj planEq).1
  dsimp [memSafetyUnit, memUnit, memProgram] at execute
  obtain ⟨traceEq, nextEq⟩ := genauInternal (k := k) execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
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

theorem aussenLokal {k : Katalog} (op : MemInstruction) :
    Gabbro.Core.Annahme.AussenLokal (memUnit k op) := by
  refine ⟨zulassung_m2 k.plattform, ?_⟩
  apply aussen_gueltig_aus_kontext (memUnit k op)
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    dsimp [memUnit, memProgram] at execute
    obtain ⟨rfl, rfl⟩ := genauInternal (k := k) execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem kosten {k : Katalog} (op : MemInstruction) :
    ∀ t c s w middle next p trace,
      (MemInstruction.rule k.plattform.ziel op).impl c s w [p] middle →
      FuehrtSchrittAus memSetup t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (memUnit k op).stotterLaenge op = 0 := by
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := implTransfer (k := k) (op := op) (w := w) impl
  cases (List.cons.inj hp).1
  exact ⟨(genauInternal (k := k) execute).1, rfl⟩

end MemInstruction

theorem memErhaltungAussage_merge : MemErhaltungAussage .merge := by
  intro k scope tree op _
  exact ⟨MemInstruction.abgleich (k := k) op, MemInstruction.komponierbar (k := k) op⟩

theorem memRegelSicherAussage_merge : MemRegelSicherAussage .merge := by
  intro k scope tree op _
  exact MemInstruction.regelSicher (k := k) op

theorem memAussenLokalAussage_merge : MemAussenLokalAussage .merge := by
  intro k scope tree op _
  exact MemInstruction.aussenLokal (k := k) op

theorem memKostenAussage_merge : MemKostenAussage .merge := by
  intro k scope tree op _
  exact MemInstruction.kosten (k := k) op

end Gabbro.Core.Ast.LowLevel
