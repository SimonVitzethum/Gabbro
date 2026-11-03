module

public import Grammatik.Parser.TaggedDispatch.Resolve

@[expose] public section
namespace Gabbro.Grammatik.Parser

abbrev TaggedLocals := List (String × STyp)

/-- Type information used solely to select a generated overload. Ordinary typing
    remains with the elaborator; an unresolved receiver refuses rather than guesses. -/
def taggedExprType (items : List SItemTief) (locals : TaggedLocals) (e : SExpr) : Option STyp :=
  Spec.inferType (Spec.materialize items) locals 128 e

/-- Follow transparent aliases while retaining the identity of a tagged declaration. -/
def taggedSumName (items : List SItemTief) : Nat → STyp → Option String
  | 0, _ => none
  | f + 1, .atom name =>
    match items.find? (fun | .typeT _ n [] [] _ => strEq n name | _ => false) with
    | some (.typeT flags _ _ _ (some t)) =>
      if flags.any (strEq "tagged") then some name else taggedSumName items f t
    | _ => none
  | _, _ => none

def taggedResolveCall (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) (name : String) (args : List SExpr) :
    Except String String := do
  let candidates := bindings.filter (fun b => strEq b.source name)
  if candidates.isEmpty then pure name
  else
    let selected := candidates.filter fun b =>
      args.length == b.signature.params.length &&
        ((args[b.receiver]?).bind (taggedExprType items locals)).any
          (fun ty => taggedSumName items 128 ty == some b.sumName)
    match selected with
    | [b] => pure b.signature.name
    | [] => pure name
    | _ => throw ("tagged-dispatch-ambiguous-call: " ++ name)

end Gabbro.Grammatik.Parser
