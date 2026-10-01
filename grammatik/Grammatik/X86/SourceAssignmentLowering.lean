/-
  File:      Grammatik/X86/SourceAssignmentLowering.lean
  Subject:   Direct typed-source assignment to pilot machine code (lane 628).

  Lower the actually covered typed `Stmt.assignSlot` (an `.int lo hi` field
  admitted by the accepted `SourceMemory570` `repOk`, with its value
  expression in the accepted `ExpressionLowering599` `senkFrag` fragment)
  into generated pilot instructions (`prog ++ [store64]`), and prove the
  source `execStmt` world update matches the target `lauf` execution under
  the one representation map (`zahlWort`/`intWort` bridge). No second IR,
  no new interpreter, no source/checker/emitter edit.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat
import Grammatik.X86.SourceMemory
import Grammatik.X86.ExpressionLowering

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Direct lowering of one admitted assignment: the value fragment lowered
    by `senkFrag` (599), followed by one `store64` through the admitted
    slot base register. `none` is the explicit unsupported-expression
    refusal; admission of the slot itself stays with `repOk` (570). -/
def senkAssign {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp base : Register) (disp : BitVec 32) :
    Option (List Befehl) :=
  match senkFrag abb e dst tmp with
  | some prog => some (prog ++ [Befehl.store64 base dst disp])
  | none => none

/- CUTS:
     - Skeleton only: lowering shape stated, nothing proved yet.
     - Pilot integer fragment only; sums/FP/locks/calls outside.
     - Full source-to-final-loaded-bytes remains OPEN.
-/

#print axioms senkAssign

end Gabbro.Grammatik.X86
