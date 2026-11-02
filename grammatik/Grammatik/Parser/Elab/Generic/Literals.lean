module
public import Grammatik.Parser.Elab.Generic.FreeNames
public import Grammatik.Parser.Elab.Generic.Closure
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Length encoding reserves a deterministic namespace disjoint from generic instance names.
    Equal capture-free literal syntax shares one lifted definition. Names are collision-checked
    against every source item and every generated instance before any declaration is inserted. -/
def literalName (canonical : String) : String := "$literal$" ++ encodeComponent canonical

def functionArgument (word : String) : Except String (String × SFunctionArgument) := do
  let ts ← match lex word with
    | .ok ts => pure ts
    | .error _ => throw "static function argument does not lex"
  let argument ← parseFunctionArgument (ts.length * 4 + 32) ts
  let canonical := String.intercalate " " ((ts.filter fun
    | .ende => false
    | _ => true).map zeigeTok)
  pure (canonical, argument)

/-- Validate the reserved names and share identical pending literals before any body visitor.
    The result remains signature/body pairs until the final materialization phase. -/
def uniqueLiterals (sourceNames : List String) (literals : List (FnSig × SAnw)) :
    Except String (List (FnSig × SAnw)) := do
  let mut seen : List String := []
  let mut unique := []
  for (sig, body) in literals do
    if sourceNames.contains sig.name then
      throw "function-literal-name-collision: generated literal name is already declared"
    if !seen.contains sig.name then
      unique := unique ++ [(sig, body)]
      seen := seen ++ [sig.name]
  pure unique

/-- Only the final phase inserts literal declarations, after their calls and contracts expand. -/
def appendLiterals (sourceNames : List String) (ordinary : List SItemTief)
    (literals : List (FnSig × SAnw)) : Except String (List SItemTief) := do
  let literals ← uniqueLiterals sourceNames literals
  pure (ordinary ++ literals.map (fun (sig, body) => .fnT sig body))

end Gabbro.Grammatik.Parser.Generic
