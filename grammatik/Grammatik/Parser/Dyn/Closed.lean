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

/-- Measure declared scalar representation, following aliases with bounded fuel.
    Aggregates are measured for a precise size refusal, but are not dyn payloads. -/
def payloadBytes (items : List SItemTief) : Nat → STyp → Except String Nat
  | 0, _ => .error "dyn.payload-type-cycle"
  | f + 1, .atom n =>
    if strEq n "bool" then .ok 1
    else if strEq n "f32" then .ok 4
    else if strEq n "f64" then .ok 8
    else match Uebersetze.eingebauteInt.find? (fun p => strEq p.1 n) with
      | some _ =>
        match (String.ofList n.toList.tail).toNat? with
        | some bits => .ok ((bits + 7) / 8)
        | none => .error "dyn.payload-type"
      | none =>
        match items.find? (fun
          | .typeT _ name [] [] (some _) | .whyT name _ _ => strEq name n
          | _ => false) with
        | some (.typeT _ _ _ _ (some t)) => payloadBytes items f t
        | some (.whyT ..) => .ok 8
        | _ => .error ("dyn.payload-type: " ++ n)
  | f + 1, .path [n] => payloadBytes items f (.atom n)
  | _, .index .. => .ok 8
  | f + 1, .range t _ _ _ | f + 1, .wrap t => payloadBytes items f t
  | f + 1, .array t (.lit n) => do
    return (← payloadBytes items f t) * n
  | _, _ => .error "dyn.payload-type"

def scalarPayload (items : List SItemTief) : Nat → STyp → Bool
  | 0, _ => false
  | f + 1, .atom n =>
    match items.find? (fun | .typeT _ name [] [] (some _) => strEq name n | _ => false) with
    | some (.typeT _ _ _ _ (some t)) => scalarPayload items f t
    | _ => true
  | f + 1, .path [n] => scalarPayload items f (.atom n)
  | f + 1, .range t _ _ _ | f + 1, .wrap t => scalarPayload items f t
  | _, .index .. => true
  | _, _ => false

/-- Bounds are concrete ordinary effects; the parser retained the balancing closing brace. -/
def readBound (items : List SItemTief) (raw : String) : Except String (List SEffekt) := do
  let tokens ← lex raw
  let (effects, tail) ← if istZeichenZ "}" tokens then pure ([], tokens)
    else parseEffektListe (tokens.length * 8 + 32) tokens
  let [.zeichen "}", .ende] := tail | throw "dyn.effects.syntax"
  expandEffects items (groups items) (instances items) [] [] 1000 effects

def actualEffects (items : List SItemTief) (i : Instance) : Except String (List SEffekt) :=
  expandEffects items (groups items) (instances items) [] [] 1000
    (i.functions.flatMap fun | .fnT s _ => functionEffects s | _ => [])

/-- All linked instances are known here. A bound excludes effects before payload-size checking,
    so an unrelated large implementation cannot invalidate a smaller bound. -/
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
        let bytes ← payloadBytes items 128 payload
        if bytes > 8 then throw ("dyn.payload-too-large: " ++ spec)
        if !scalarPayload items 128 payload then throw ("dyn.payload-type: " ++ spec)
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
    let tokens ← lex raw
    if tokens.any (fun | .wort "dyn" => true | _ => false) then throw "dyn.raw-type"
    return .raw raw
  | t => .ok t

end Gabbro.Grammatik.Parser.Dyn
