module

public import Grammatik.Parser.Dyn.Collect
public import Grammatik.Parser.TaggedDispatch.Resolve
public import Grammatik.Parser.Print.Stmt

@[expose] public section
namespace Gabbro.Grammatik.Parser.Dyn
open Spec

structure Case where
  name : String
  payload : STyp
  implementation : Nat
  deriving Repr

structure Closed where
  surface : STyp
  spec : String
  name : String
  effects : List SEffekt
  cases : List Case
  aliases : List STyp := []
  deriving Repr

/-- Bounds are concrete ordinary effects; the parser retained the balancing closing brace. -/
def readBound (items : List SItemTief) (raw : String) : Except String (List SEffekt) := do
  let tokens ← match lex raw with
    | .ok tokens => pure tokens
    | .error _ => throw "dyn.effects.syntax"
  let (effects, tail) ← if istZeichenZ "}" tokens then pure ([], tokens)
    else parseEffektListe (tokens.length * 8 + 32) tokens
  let [.zeichen "}", .ende] := tail | throw "dyn.effects.syntax"
  expandEffects items (groups items) (instances items) [] [] 1000 effects

def actualEffects (items : List SItemTief) (i : Instance) : Except String (List SEffekt) :=
  expandEffects items (groups items) (instances items) [] [] 1000
    (i.functions.flatMap fun | .fnT s _ => functionEffects s | _ => [])

/-- All linked instances are known here. A bound excludes effects before case
    collection, so an unrelated implementation outside the bound never constrains
    the linked sum. Every implementation whose effects fit the bound becomes a
    case, carrying its own payload type: scalar or aggregate, of any size. The
    closed sum travels through the existing tagged sum layout (the declaration
    below), never through a separate dynamic representation. Lowering premise
    (Stage 0, branch s0-gaps1): sum payloads beyond one word lower through
    `sumPayloadWords`/`sumOff` and the `encodeWords` sum branch; the front end
    here assumes that layout and proves nothing about its words. -/
def close (items : List SItemTief) (index : Nat) (surface : STyp) : Except String Closed := do
  let .dyn spec raw := surface | throw "dyn.type"
  let some group := (groups items).find? (fun g => strEq g.name spec)
    | throw ("dyn.unknown-spec: " ++ spec)
  if group.types.length != 1 then throw "dyn.spec-type-arity"
  let effects ← match raw with
    | some raw =>
      if strEq raw inferredBound then do
        let effects ← ((instances items).filter (fun i => strEq i.group spec)).mapM (actualEffects items)
        pure effects.flatten
      else readBound items raw
    | none =>
      if !group.effects.isEmpty then throw ("dyn.effects.required: " ++ spec)
      expandEffects items (groups items) (instances items) [] [] 1000
        (group.functions.flatMap functionEffects)
  let mut cases := []
  for (i, implementation) in (instances items).zipIdx do
    if strEq i.group spec then
      let actual ← actualEffects items i
      if actual.all (fun e => effects.any (beqSEffekt e)) then
        let [payload] := i.types | throw "dyn.spec-type-arity"
        cases := cases ++ [⟨"GabbroDyn" ++ toString index ++ "Case" ++ toString implementation,
          payload, implementation⟩]
  if cases.isEmpty then throw ("dyn.no-implementation: " ++ spec)
  return { surface, spec, name := "#dyn" ++ toString index, effects, cases }

/-- Equal effect sets denote the same type irrespective of list order or spelling.
    A producer without a written type infers the union only when no contextual bound exists. -/
def catalog (items : List SItemTief) (uses : List STyp) : Except String (List Closed) := do
  let uses := uses.filter fun
    | .dyn spec (some raw) =>
      !strEq raw inferredBound || !(uses.any fun
        | .dyn other bound => strEq spec other && bound != some inferredBound
        | _ => false)
    | _ => true
  uses.foldlM (fun closed ty => do
    let candidate ← close items closed.length ty
    match closed.find? (fun c => strEq c.spec candidate.spec &&
        c.effects.all (fun e => candidate.effects.any (beqSEffekt e)) &&
        candidate.effects.all (fun e => c.effects.any (beqSEffekt e))) with
    | none => pure (closed ++ [candidate])
    | some previous =>
      pure (closed.map fun c => if strEq c.name previous.name then
        { c with aliases := c.aliases ++ [ty] } else c)) []

def typeText (t : STyp) : String := " ".intercalate ((druckTyp t).map zeigeTok)

/-- Ordinary source sum and the existing by-dispatch metadata, consumed by the next pass. -/
def declaration (closed : Closed) : SItemTief :=
  .taggedByT (.typeT ["tagged"] closed.name [] [] (some (.raw
    ("{ " ++ ", ".intercalate (closed.cases.map fun c =>
      c.name ++ "(" ++ typeText c.payload ++ ")") ++ " }")))) closed.spec

def lowerType (closed : List Closed) : STyp → Except String STyp
  | t@(.dyn ..) =>
    match closed.find? (fun c => beqSTyp c.surface t || c.aliases.any (beqSTyp t)) with
    | some c => .ok (.atom c.name)
    | none => .error "dyn.unresolved-type"
  | .raw raw => do
    let tokens ← match lex raw with
      | .ok tokens => pure tokens
      | .error _ => throw "dyn.raw-type"
    if tokens.any (fun | .wort "dyn" => true | _ => false) then throw "dyn.raw-type"
    return .raw raw
  | t => .ok t

end Gabbro.Grammatik.Parser.Dyn
