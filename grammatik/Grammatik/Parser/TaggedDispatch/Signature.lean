module

public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1a
public import Grammatik.Parser.TaggedDispatch.Expansion

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Substitute the spec receiver throughout a surface signature type. -/
def taggedSubstituteType (parameter : String) (variant : STyp) : STyp → STyp
  | .atom name => if strEq name parameter then variant else .atom name
  | .ptr r w t => .ptr r w (taggedSubstituteType parameter variant t)
  | .range t a b closed => .range (taggedSubstituteType parameter variant t) a b closed
  | .array t n => .array (taggedSubstituteType parameter variant t) n
  | .wrap t => .wrap (taggedSubstituteType parameter variant t)
  | .embed t n e => .embed (taggedSubstituteType parameter variant t) n e
  | .entry args (some result) => .entry args (some (taggedSubstituteType parameter variant result))
  | t => t

def taggedSubstituteSelf (variant : STyp) : STyp → STyp :=
  taggedSubstituteType "Self" variant

/-- Conservative occurrence check, including nested result types. -/
def taggedContainsSelf : STyp → Bool
  | .atom "Self" => true
  | .ptr _ _ t | .range t _ _ _ | .array t _ | .wrap t | .embed t _ _ =>
    taggedContainsSelf t
  | .entry _ (some result) => taggedContainsSelf result
  | _ => false

/-- Result-producing static functions do not participate in closed dispatch. -/
def taggedDispatchable (signature : FnSig) : Bool :=
  (signature.params.filter (fun p => beqSTyp p.2 (.atom "Self"))).length == 1 &&
    signature.params.all (fun p => beqSTyp p.2 (.atom "Self") || !taggedContainsSelf p.2) &&
    !(signature.res.any taggedContainsSelf)

/-- Resolve signatures before generating calls; report the offending implementation. -/
def checkTaggedSignature (variant : STyp) (expected actual : FnSig) : Except String Unit := do
  let params := expected.params.map (fun p => taggedSubstituteSelf variant p.2)
  if !(params.length == actual.params.length &&
      (params.zip actual.params).all (fun p => beqSTyp p.1 p.2.2) &&
      beqSTypOpt (expected.res.map (taggedSubstituteSelf variant)) actual.res &&
      beqOptWort expected.fehler actual.fehler) then
    throw ("tagged-dispatch-signature-mismatch: " ++ actual.name)

/-- A statically selected implementation, before calls are generated. Function pairs
    retain the spec member name separately from the ordinary target function name. -/
structure TaggedImplementation where
  variant : STyp
  functions : List (String × FnSig)
  deriving Repr

mutual
def taggedHeld : SExpr → Bool
  | .call "Held" _ => true
  | .field e _ | .arrow e _ | .un _ e | .old e => taggedHeld e
  | .index a b | .bin _ a b => taggedHeld a || taggedHeld b
  | .call _ es | .built _ es | .ext _ _ es => taggedHeldList es
  | _ => false
def taggedHeldList : List SExpr → Bool
  | [] => false
  | e :: es => taggedHeld e || taggedHeldList es
end

/-- No held lock may cross a generated abstract call. -/
def taggedSignatureHeld (signature : FnSig) : Bool :=
  signature.klauseln.any fun
    | .needs e | .gives e => taggedHeld e
    | _ => false

/-- Check the whole group, then resolve every case for every dispatchable function.
    Static constructors returning Self are deliberately skipped, including their
    implementation lookup. Missing and ambiguous bindings never choose a fallback. -/
def checkTaggedGroup (functions : List FnSig)
    (variants : List (String × Option STyp)) (impls : List TaggedImplementation) :
    Except String (List (FnSig × List TaggedDispatchCase)) := do
  if ¬ (functions.map (·.name)).Nodup then
    throw "tagged-dispatch-duplicate-spec-function"
  let mut resolved := []
  for expected in functions do
    if taggedSignatureHeld expected then
      throw ("tagged-dispatch-held: " ++ expected.name)
    if taggedDispatchable expected then
      let cases ← variants.mapM fun (name, payload) => do
        let variant ← match payload with
          | some ty => pure ty
          | none => throw ("tagged-dispatch-missing-payload: " ++ name)
        let implementation ← match impls.filter (fun i => beqSTyp i.variant variant) with
          | [i] => pure i
          | [] => throw ("tagged-dispatch-missing-implementation: " ++ name ++ "::" ++ expected.name)
          | _ => throw ("tagged-dispatch-ambiguous-implementation: " ++ name)
        let actual ← match implementation.functions.filter (fun f => strEq f.1 expected.name) with
          | [(_, actual)] => pure actual
          | [] => throw ("tagged-dispatch-missing-implementation: " ++ name ++ "::" ++ expected.name)
          | _ => throw ("tagged-dispatch-duplicate-function: " ++ name ++ "::" ++ expected.name)
        checkTaggedSignature variant expected actual
        if taggedSignatureHeld actual then
          throw ("tagged-dispatch-held: " ++ actual.name)
        pure (TaggedDispatchCase.mk name (some actual.name))
      resolved := resolved ++ [(expected, cases)]
  pure resolved

end Gabbro.Grammatik.Parser
