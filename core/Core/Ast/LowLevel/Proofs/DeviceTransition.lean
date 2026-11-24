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

end Gabbro.Core.Ast.LowLevel.Device
