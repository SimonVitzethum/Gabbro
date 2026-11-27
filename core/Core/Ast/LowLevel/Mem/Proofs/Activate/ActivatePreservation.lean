module

public import Core.Ast.LowLevel.Mem.Proofs.Activate.ActivateObligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter Aussen Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

theorem memErhaltungActivate (form : MemForm) : MemErhaltungAussage form := by
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
    exact ⟨op.schrittPlan s c, op.schrittSpur s c, frame.advance c s, planEq, op.vollzug frame t c s⟩

theorem MemInstruction.regelSicher (k : Katalog) (op : MemInstruction) :
    Gabbro.Core.Sicherheit.RegelSicher (memSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach plan spur head impl execute
  obtain ⟨spurEq, nextEq⟩ := MemInstruction.vollzugGenau (target := k.plattform.ziel) (w := w) impl execute
  obtain ⟨frame, _, planEq, _⟩ := impl
  subst zwischen
  cases (List.cons.inj planEq).1
  subst spur
  subst nach
  have ohneAbsturz : ¬ Absturz (op.schrittSpur vor c) := by
    intro mem
    obtain ⟨_, eq⟩ := MemInstruction.schrittSpur_aussen mem
    cases eq
  have wirkungen : NeueWirkungen vor (frame.advance c vor)
      (op.schrittSpur vor c) [] :=
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
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro event mem
    obtain ⟨_, rfl⟩ := MemInstruction.schrittSpur_aussen mem
    exact ⟨fun _ eq => nomatch eq, fun _ commit => nomatch commit.1⟩
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro event mem _ commit
    obtain ⟨_, rfl⟩ := MemInstruction.schrittSpur_aussen mem
    exact nomatch commit.1

theorem memRegelSicherActivate (form : MemForm) : MemRegelSicherAussage form :=
  fun k _ _ op _ => op.regelSicher k

theorem memAussenLokalActivate (form : MemForm) : MemAussenLokalAussage form := by
  intro k scope tree op _
  exact memProgramAussenLokal k [op]

theorem memKostenActivate (form : MemForm) : MemKostenAussage form := by
  intro k scope tree op _
  intro t c s w middle next p trace impl execute
  exact ⟨(MemInstruction.vollzugGenau impl execute).1, rfl⟩

end Gabbro.Core.Ast.LowLevel
