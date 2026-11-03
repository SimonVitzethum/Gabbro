module

public import Stage0.Compiler
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Zeugen

@[expose] public section

namespace Gabbro.Stage0.CheckConsumerWitness

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A real selected Stage-0 source: check, measured local, floor and ordinary
    gate. The image configuration explicitly selects its retiring consumer. -/
def text : String :=
  "impl fn main() { return; } impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return x >= 2; } floor x >= 2 }"

def options : Profil.Options := { checkConsumer := some retiringSelection }

theorem selected_compiles : (compile text options).toOption.isSome = true := by
  decide +kernel

def compiled : Compiled text options :=
  (compile text options).toOption.get selected_compiles

/-- Acceptance is the actual compiler's full checker result. -/
theorem selected_accepted :
    OldSource.accepts compiled.unit compiled.program = .ok true := compiled.accepted

/-- Entry selection is retained in the source-to-program certificate. -/
theorem selected_entry :
    fnIdx compiled.unit.fns "p#driver#g" = .ok compiled.main := compiled.entry

/-- The generated entry's returning resource inventory is empty. -/
theorem selected_retired :
    (Gabbro.Grammatik.vertragVon (declOf compiled.unit) compiled.main).ende = [] := by
  decide +kernel

/-- The same canonical-source theorem used by every emitted image includes
    the exact selected source tree and selected elaboration. -/
theorem selected_canonical : CanonicalSourceProgram compiled :=
  compile_source_program text compiled

end Gabbro.Stage0.CheckConsumerWitness
