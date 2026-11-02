module

public import Grammatik.Parser.Item.ElementTief.Defs6

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Group members reuse the ordinary signature and body readers. A spec has only
    prototypes; an implementation has only bodies. Unsupported headers refuse. -/
def parseTaggedMembers : Nat → Bool → List Token →
    Except String (List SItemTief × List Token)
  | 0, _, _ => .error "out of fuel"
  | _ + 1, _, .zeichen "}" :: rest => .ok ([], rest)
  | f + 1, spec, toks => do
    let (sig, tail) ← parseFnSig f (if spec then "spec" else "impl") toks
    let (item, tail) ← parseFnRest f sig tail
    match spec, item with
    | true, .protoT _ | false, .fnT _ _ => pure ()
    | _, _ => throw ("tagged-dispatch-invalid-group-member: " ++ sig.name)
    let (items, rest) ← parseTaggedMembers f spec tail
    pure (item :: items, rest)

/-- Single-type spec groups needed by closed dispatch. Effect-parameter headers
    remain refused rather than discarding their substitution obligations. -/
def parseTaggedGroup (fuel : Nat) (spec : Bool) (toks : List Token) :
    Except String (SItemTief × List Token) := do
  let (name, tail) ← nimmName toks
  let tail ← fordereZeichen "[" tail
  if spec then
    let (parameter, tail) ← nimmName tail
    let tail ← fordereZeichen "]" tail
    let tail ← fordereZeichen "{" tail
    let (items, rest) ← parseTaggedMembers fuel true tail
    pure (.specGroupT name parameter (items.filterMap fun
      | .protoT sig => some sig | _ => none), rest)
  else
    let (variant, tail) ← parseTyp fuel tail
    let tail ← fordereZeichen "]" tail
    let tail ← fordereZeichen "{" tail
    let (items, rest) ← parseTaggedMembers fuel false tail
    pure (.implGroupT name variant (items.filterMap fun
      | .fnT sig body => some (sig, body) | _ => none), rest)

end Gabbro.Grammatik.Parser
