module

public import Core.Ast.LowLevel.Exec.Proofs.ExecJumpLong

public section

namespace Gabbro.Core.Ast.LowLevel

open Maschine

/-- A completed abstract long jump reaches the declared execution-state slot
    with the same grants, ownership ledger and loan state. The destination
    declaration describes the local execution frame; the machine's core
    fields are unchanged at this boundary. -/
theorem execJumpLong_preservesAuthority {code dest t : Nat} {space stack : Option Nat}
    {c : Kontext} {before middle after : ExecState} {choice : PUnit}
    {p : Plan} {trace : SchrittSpur Nat UInt8}
    (step : (ExecInstruction.jumpLong code dest space stack).step c before choice [p] middle)
    (execute : FuehrtSchrittAus execSetup t c before middle p trace after) :
    after.rechte = before.rechte ∧ after.buchung = before.buchung ∧
    after.leihen = before.leihen ∧ after.kerne = before.kerne ∧
    ∃ origin target, (before.lokal c).current = some origin ∧ origin ≠ dest ∧
      (before.lokal c).states[dest]? = some target ∧
      (after.lokal c).current = some dest ∧ (after.lokal c).activeSpace = space ∧
      (after.lokal c).result = some (.jumpedLong code dest) := by
  obtain ⟨frame, eval, planEq, rfl⟩ := execImplTransfer step
  cases (List.cons.inj planEq).1
  obtain ⟨_, rfl⟩ := execGenauInternal execute
  obtain ⟨origin, target, current, distinct, declared, _, arrived, active, result, _, _⟩ :=
    jumpLong_aussage.2.1 code dest space stack before c frame eval
  refine ⟨rfl, rfl, rfl, rfl, origin, target, current, distinct, declared, ?_⟩
  simp only [ExecFrame.advance, Function.update_self]
  exact ⟨arrived, active, result⟩

end Gabbro.Core.Ast.LowLevel
