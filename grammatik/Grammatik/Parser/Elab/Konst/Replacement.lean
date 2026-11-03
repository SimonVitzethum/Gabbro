module
public import Grammatik.Parser.Elab.Konst.Values.Export

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst
open Uebersetze

/-- Both result families expose one replacement interface, retaining their exact
    source certificates. Integer results additionally retain bounded/KExpr checks. -/
inductive ReplacementEvidence (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) : SExpr → Type where
  | integer (call : Scalar.CheckedCall k fns env sources) :
      ReplacementEvidence k fns env sources (literalVonInt call.value)
  | portable (call : Values.CheckedCall k fns env sources) :
      ReplacementEvidence k fns env sources call.quoted.syntax

structure Replacement (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) where
  syntax : SExpr
  evidence : ReplacementEvidence k fns env sources syntax

/-- The one production entry point for certified value replacement. -/
def checkReplacement (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) :
    Except String (Replacement k fns env sources) := do
  match k.erg with
  | .int _ _ =>
    let checked ← Scalar.checkCall k fns env sources
    return ⟨literalVonInt checked.value, .integer checked⟩
  | _ =>
    if Values.resultType k.erg then
      let checked ← Values.checkCall k fns env sources
      return ⟨checked.quoted.syntax, .portable checked⟩
    else throw ("const result type without a certified replacement at `" ++ k.name ++ "`")

end Gabbro.Grammatik.Parser.Konst
