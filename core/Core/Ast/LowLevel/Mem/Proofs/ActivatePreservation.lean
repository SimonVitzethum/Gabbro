module

public import Core.Ast.LowLevel.Mem.Proofs.ActivateObligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

theorem memErhaltung (form : MemForm) : MemErhaltungAussage form := by
  intro k scope tree op _
  constructor
  · intro hw t c w s u s' i plan spur related normal ready head impl execute
    obtain ⟨protocol, frames⟩ := related
    change s.lokal = i.lokal at frames
    change { s with lokal := i.lokal } = i at protocol
    rw [← frames] at protocol
    subst i
    obtain ⟨frame, evaluate, planEq, hu⟩ := impl
    subst u
    exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
      I.ProtokollBezug.refl _, rfl⟩
  · intro t s c w plans u head gut ideal
    obtain ⟨frame, evaluate, planEq, hu⟩ := ideal
    subst u
    exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq,
      MemInstruction.vollzug k.plattform.ziel op frame t c s⟩

theorem memRegelSicher (form : MemForm) : MemRegelSicherAussage form := by
  intro k scope tree op _
  intro H ρ t c w vor zwischen nach plan spur head impl execute
  obtain ⟨frame, _, planEq, _⟩ := impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := MemInstruction.vollzugGenau (target := k.plattform.ziel) impl execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor)
      (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
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

theorem memRegelAntwortSicher (form : MemForm) : MemRegelAntwortSicherAussage form := by
  intro k scope tree op _
  constructor
  · intro t c w vor zwischen nach p trace _ impl execute befugt
    obtain ⟨frame, _, _, rfl⟩ := impl
    obtain ⟨rfl, rfl⟩ := MemInstruction.vollzugGenau (target := k.plattform.ziel)
      (w := w) impl execute
    exact befugt
  · intro t c s w middle next p trace impl execute
    obtain ⟨rfl, rfl⟩ := MemInstruction.vollzugGenau (target := k.plattform.ziel)
      (w := w) impl execute
    exact ⟨fun _ => List.not_mem_nil, execute.1.verbraucht⟩

theorem memAussenLokalUnit (k : Katalog) (op : MemInstruction) :
    Annahme.AussenLokal (memUnit k op) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
      obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
      cases (List.cons.inj planEq).1
      obtain ⟨rfl, rfl⟩ := MemInstruction.genauInternal execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem memAussenLokal (form : MemForm) : MemAussenLokalAussage form := by
  intro k scope tree op _
  exact memAussenLokalUnit k op

theorem memKosten (form : MemForm) : MemKostenAussage form := by
  intro k scope tree op _
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := impl
  cases (List.cons.inj hp).1
  exact ⟨(MemInstruction.genauInternal execute).1, rfl⟩

theorem activateObligations : memObligationsKern .activateSpace := by
  refine ⟨memParse _, memInversion _, memEindeutig _, memDruck _, memElaboriert _,
    memRealisiert _, memAnnahme _, memIdeal _, memEinheit _, memImpl _, memFortschritt _,
    memErhaltung _, memRegelSicher _, memRegelAntwortSicher _, memAussenLokal _, memKosten _,
    memSchranken, memEtiketten, memFluss⟩

end Gabbro.Core.Ast.LowLevel
