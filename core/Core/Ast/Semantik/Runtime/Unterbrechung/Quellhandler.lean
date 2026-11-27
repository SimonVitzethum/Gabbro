module

public import Core.Ast.LowLevel.Exec.Meaning
public import Core.Ast.Semantik.Runtime.Mehrkontext.Start

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog LowLevel

/-- Attach the body of a declared, maskable per-core entry to its target-bound vector.
    The entry declaration supplies neither a vector number nor a body. This profile
    takes a closed integer result expression and ends the handler after evaluating it.
    Dispatch selects by vector for every core and delivery instance, with priority
    supplied by the hardware offer at delivery. -/
def interruptHandler (platform : Plattform) (scope : ExecScope)
    (vectorFor : Identifier → Option Nat) (entry : ExecTree .entryDecl)
    {lo hi : Int} (result : Expr [] (.int lo hi)) (main : Fragment) : Option Fragment := do
  match ← elaborateExec scope entry with
  | .declareEntry name .interrupt .perCore (some priority) =>
    let vector ← vectorFor name
    if vector < platform.ziel.interruptCount ∧ priority < 256 then
      let body := (expr 0 result).anhaengen (.einzel (.faden (.beende 0)))
      let handler := body.rumpf fun c => match c with
        | .handler _ line _ => decide (line = vector)
        | _ => false
      pure ((main.anhaengen (.einzel .ende)).anhaengen handler)
    else none
  | _ => none

end Gabbro.Core.Ast.Semantik
