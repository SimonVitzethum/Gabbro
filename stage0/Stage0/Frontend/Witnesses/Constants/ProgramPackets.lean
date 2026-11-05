module
public import Stage0.Frontend.Witnesses.Constants.Compilation

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Choose complete canonical triples after success is fixed, before the assembler projects them. -/
def Functions.of_success {unit : UProg}
    (produced : ∀ f : Fin unit.fns.length, (lowerFnAt unit f).toOption.isSome = true)
    (noInvariants : unit.invs = [])
    (noMeasures : ∀ f : Fin unit.fns.length, (fnAt unit f).decreases = none)
    (contracts : contractGate unit = true) : Functions unit where
  values := fun f => (lowerFnAt unit f).toOption.get (produced f)
  equations := fun f => Gabbro.Grammatik.except_ok_get (produced f)
  noInvariants := noInvariants
  noMeasures := noMeasures
  contracts := contracts

end Gabbro.Stage0.Frontend.ConstPhases
