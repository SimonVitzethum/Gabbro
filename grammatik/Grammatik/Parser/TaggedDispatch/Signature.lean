module

public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1a

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Substitute the spec receiver throughout a surface signature type. -/
def taggedSubstituteSelf (variant : STyp) : STyp → STyp
  | .atom "Self" => variant
  | .ptr r w t => .ptr r w (taggedSubstituteSelf variant t)
  | .range t a b closed => .range (taggedSubstituteSelf variant t) a b closed
  | .array t n => .array (taggedSubstituteSelf variant t) n
  | .wrap t => .wrap (taggedSubstituteSelf variant t)
  | .embed t n e => .embed (taggedSubstituteSelf variant t) n e
  | .entry args result => .entry args (result.map (taggedSubstituteSelf variant))
  | t => t

/-- Conservative occurrence check, including nested result types. -/
def taggedContainsSelf : STyp → Bool
  | .atom "Self" => true
  | .ptr _ _ t | .range t _ _ _ | .array t _ | .wrap t | .embed t _ _ =>
    taggedContainsSelf t
  | .entry _ result => result.any taggedContainsSelf
  | _ => false

/-- Result-producing static functions do not participate in closed dispatch. -/
def taggedDispatchable (signature : FnSig) : Bool :=
  (signature.params.filter (fun p => beqSTyp p.2 (.atom "Self"))).length == 1 &&
    !(signature.res.any taggedContainsSelf)

/-- Resolve signatures before generating calls; report the offending implementation. -/
def checkTaggedSignature (variant : STyp) (expected actual : FnSig) : Except String Unit := do
  let params := expected.params.map (fun p => taggedSubstituteSelf variant p.2)
  if !(params.length == actual.params.length &&
      (params.zip actual.params).all (fun p => beqSTyp p.1 p.2.2) &&
      beqSTypOpt (expected.res.map (taggedSubstituteSelf variant)) actual.res &&
      beqOptWort expected.fehler actual.fehler) then
    throw ("tagged-dispatch-signature-mismatch: " ++ actual.name)

end Gabbro.Grammatik.Parser
