module

public import Grammatik.Parser.Namen.Oeffentlich

@[expose] public section

namespace Gabbro.Grammatik.Parser.EffectGroups

/-- Group bodies refer to declared global carriers. The surface table suffix
    stays attached for the ordinary effect checker. -/
def carrier : SExpr → Option String
  | .variable name | .field (.variable name) "slots" => some name
  | _ => none

def carrierName : SItemTief → Option String
  | .tableT name .. | .arenaT name .. | .globT _ name .. => some name
  | _ => none

def isCarrierEffect (carriers : List String) : SEffekt → Bool
  | .reads place | .writes place => (carrier place).any carriers.contains
  | _ => false

abbrev Groups := List (String × List SEffekt)

def group : SItemTief → Option (String × List SEffekt)
  | .effectGroupT name effects => some (name, effects)
  | _ => none

def effectGroup (groups : Groups) (bound : List String) : SEffekt → Option (List SEffekt)
  | .param name =>
    if bound.contains name then none
    else (groups.find? fun entry => entry.1 == name).map Prod.snd
  | _ => none

/-- Expand each reference in declaration order and refuse capture by a
    parameter. Other effect syntax goes to its existing checker. -/
def expandEffects (groups : Groups) (bound : List String) :
    List SEffekt → Except String (List SEffekt)
  | [] => .ok []
  | effect :: tail => do
    let head ← match effectGroup groups bound effect with
      | none => pure [effect]
      | some places =>
        if (places.flatMap (Oeffentlich.namenE [])).any bound.contains then
          throw "effect group: a parameter shadows a declared carrier"
        else pure places
    pure (head ++ (← expandEffects groups bound tail))

/-- Ordinary effects keep their order and each group occurrence contributes
    exactly the effects of its declaration. -/
theorem expandEffects_exact (groups : Groups) (bound : List String) (effects expanded : List SEffekt)
    (accepted : expandEffects groups bound effects = .ok expanded) :
    expanded = effects.flatMap fun effect => (effectGroup groups bound effect).getD [effect] := by
  induction effects generalizing expanded with
  | nil =>
    exact (Except.ok.inj accepted).symm
  | cons head tail ih =>
    cases candidate : effectGroup groups bound head with
    | none =>
      cases rest : expandEffects groups bound tail with
      | error err => simp [expandEffects, candidate, rest, bind, Except.bind, pure, Except.pure] at accepted
      | ok result =>
        have returned : [head] ++ result = expanded := by
          simpa [expandEffects, candidate, rest, bind, Except.bind, pure, Except.pure] using accepted
        simpa only [List.flatMap_cons, candidate, Option.getD_none, ih result rest] using returned.symm
    | some places =>
      by_cases capture : (places.flatMap (Oeffentlich.namenE [])).any bound.contains = true
      · simp [expandEffects, candidate, capture, bind, Except.bind, pure, Except.pure] at accepted
      · cases rest : expandEffects groups bound tail with
        | error err => simp [expandEffects, candidate, capture, rest, bind, Except.bind, pure, Except.pure] at accepted
        | ok result =>
          have returned : places ++ result = expanded := by
            simpa [expandEffects, candidate, capture, rest, bind, Except.bind, pure, Except.pure] using accepted
          simpa only [List.flatMap_cons, candidate, Option.getD_some, ih result rest] using returned.symm

/-- A declared place can be named through its group and retains its write
    effect, for arbitrary group and carrier names. -/
theorem effectGroup_erfuellbar (name place : String) :
    isCarrierEffect [place] (.writes (.variable place)) = true ∧
    expandEffects [(name, [.writes (.variable place)])] [] [.param name] =
      .ok [.writes (.variable place)] := by
  simp [isCarrierEffect, carrier, expandEffects, effectGroup, bind, Except.bind, pure, Except.pure]

def signature (groups : Groups) (bound : List String) (sig : FnSig) : Except String FnSig := do
  let bound := bound ++ sig.params.map Prod.fst ++ sig.generics.map SGenericParam.name
  let clauses ← sig.klauseln.mapM fun
    | .effs effects => return .effs (← expandEffects groups bound effects)
    | clause => pure clause
  pure { sig with klauseln := clauses }

def transition (groups : Groups) (bound : List String) (decl : STrans) : Except String STrans := do
  pure { decl with wirkung := ← expandEffects groups bound decl.wirkung }

mutual
def item (groups : Groups) : SItemTief → Except String SItemTief
  | .fnT sig body => return .fnT (← signature groups [] sig) body
  | .protoT sig => return .protoT (← signature groups [] sig)
  | .specT sig body => return .specT (← signature groups [] sig) body
  | .asmT sig text => return .asmT (← signature groups [] sig) text
  | .transT target sig body => return .transT target (← signature groups [] sig) body
  | .adaptT sig params parent body => return .adaptT (← signature groups [] sig) params parent body
  | .specGroupT name types params functions =>
    return .specGroupT name types params (← functions.mapM (signature groups (types ++ params)))
  | .implGroupT name types effects functions =>
    return .implGroupT name types (← effects.mapM (expandEffects groups [])) (← items groups functions)
  | .taggedByT decl spec => return .taggedByT (← item groups decl) spec
  | .axiomT name params res pre effects kind =>
    return .axiomT name params res pre (← expandEffects groups (params.map Prod.fst) effects) kind
  | .callT call =>
    return .callT { call with gate := { call.gate with
      uses := ← expandEffects groups (call.params.map Prod.fst) call.gate.uses } }
  | .stateT name transitions =>
    return .stateT name (← transitions.mapM (transition groups []))
  | .devT name params space members =>
    return .devT name params space (← members.mapM fun
      | .trans decl => return .trans (← transition groups (params.map Prod.fst) decl)
      | member => pure member)
  | decl => pure decl

def items (groups : Groups) : List SItemTief → Except String (List SItemTief)
  | [] => .ok []
  | decl :: rest => return (← item groups decl) :: (← items groups rest)
end

/-- The shared expansion boundary consumes the declarations after lexical
    resolution and before generic and ordinary effect checking. -/
def prepare (items : List SItemTief) (literals : List (FnSig × SAnw)) :
    Except String (List SItemTief × List (FnSig × SAnw)) := do
  let groups := items.filterMap group
  if groups.isEmpty then return (items, literals)
  let carriers := items.filterMap carrierName
  let names := items.filterMap Aufloesung.itemName
  for (name, effects) in groups do
    if (names.filter (· == name)).length != 1 then
      throw ("effect group: duplicate declaration " ++ name)
    if !(effects.all (isCarrierEffect carriers)) then
      throw ("effect group: expected reads or writes of declared carriers in " ++ name)
  let targets ← EffectGroups.items groups (items.filter fun decl => (group decl).isNone)
  let literals ← literals.mapM fun (sig, body) => return (← signature groups [] sig, body)
  pure (targets, literals)

end Gabbro.Grammatik.Parser.EffectGroups
