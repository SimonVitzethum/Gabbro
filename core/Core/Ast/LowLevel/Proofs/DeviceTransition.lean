module

public import Core.Ast.LowLevel.Proofs.DeviceRegisters

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

def RegisterTransitionAussage : Prop :=
  RegisterBefugtAussage ∧ RegisterAussenLokalAussage ∧ RegisterCommitAussage ∧ RegisterSafetyAussage ∧
  ∀ k (decl : TransitionDeclaration k) c before plan next,
    let transition := decl.changes
    let binding := decl.binding
    let access := RegisterAccess.write decl.row.offset decl.data
    Rule binding access transition.prior (some transition.after) c before plan next →
    GeraeteUebergang binding.row k.plattform.ziel transition.prior transition.action transition.after ∧
    ((next.lokal c).phases binding.object =
      (before.lokal c).phases binding.object ∨
      ((next.lokal c).phases binding.object = some transition.after ∧
        ∃ answer, before.naechsteAntwort c = some answer ∧
          answer.question = binding.question access ∧ access.result answer.reply = .written))

theorem device_transition : RegisterTransitionAussage := by
  refine ⟨register_befugt, register_aussenLokal, register_commit, register_safety, ?_⟩
  intro k decl c before plan next
  dsimp only
  intro step
  refine ⟨decl.changes.rule, ?_⟩
  cases step with
  | issue _ _ =>
    left
    simp only [setFrame, Function.update_self]
  | @consume _ answer _ ready same =>
    simp only [setFrame, Function.update_self]
    cases written : (RegisterAccess.write decl.row.offset decl.data).result answer.reply with
    | written =>
      right
      exact ⟨by simp only [Binding.object, Function.update_self], answer, ready, same, written⟩
    | value _ | readOutOfRange _ | refused _ | unexpectedAnswer =>
      exact Or.inl rfl

end Gabbro.Core.Ast.LowLevel.Device

