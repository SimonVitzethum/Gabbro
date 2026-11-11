module

public import Grammatik.Parser.Spec.Items

@[expose] public section
namespace Gabbro.Grammatik.Parser.Dyn

/-- Internal collection request for a producer whose bound can be inferred from context.
    This marker cannot be written as an effect list. -/
def inferredBound : String := "#inferred"

mutual
def expressionUses : SExpr → List STyp
  | .ext .dyn [spec] es => .dyn spec (some inferredBound) :: expressionsUses es
  | .field e _ | .arrow e _ | .un _ e | .old e => expressionUses e
  | .index a b | .bin _ a b => expressionUses a ++ expressionUses b
  | .call _ es | .built _ es | .ext _ _ es => expressionsUses es
  | _ => []
def expressionsUses : List SExpr → List STyp
  | [] => []
  | e :: es => expressionUses e ++ expressionsUses es
end

mutual
def statementProducers : SAnw → List STyp
  | .bind _ _ _ e | .bindAxiomOpt _ _ e | .await _ _ e _ | .swap _ _ e _
  | .shift e _ _ | .free e | .trimReq e _ => expressionUses e
  | .bindElse _ _ e _ s | .bindAxiomOptElse _ _ e _ s =>
    expressionUses e ++ statementProducers s
  | .bindLib _ _ _ c | .lcall c => expressionsUses c.args
  | .set a _ b | .emit a b _ => expressionUses a ++ expressionUses b
  | .callIndElse p es _ body => expressionUses p ++ expressionsUses es ++ statementProducers body
  | .callElse _ es _ body => expressionsUses es ++ statementProducers body
  | .call _ es => expressionsUses es
  | .cond e s arms none => expressionUses e ++ statementProducers s ++ statementsProducers arms
  | .cond e s arms (some other) =>
    expressionUses e ++ statementProducers s ++ statementsProducers arms ++ statementProducers other
  | .elsif e s | .trim e _ s | .locks _ e s | .grow _ e s =>
    expressionUses e ++ statementProducers s
  | .cases e arms => expressionUses e ++ statementsProducers arms
  | .arm _ _ s | .retry _ s | .loop _ s | .waive _ s | .watch _ s | .child s =>
    statementProducers s
  | .each _ start _ subject _ _ inv s =>
    expressionsUses (start.toList ++ [subject] ++ inv.toList) ++ statementProducers s
  | .alloc _ _ _ _ e none => expressionUses e
  | .alloc _ _ _ _ e (some s) => expressionUses e ++ statementProducers s
  | .reset _ range => range.toList.flatMap fun (a, b) => expressionUses a ++ expressionUses b
  | .ret e => e.toList.flatMap expressionUses
  | .block ss ending =>
    statementsProducers ss ++ ending.toList.flatMap (fun
      | .ret e => e.toList.flatMap expressionUses | _ => [])
  | _ => []
termination_by statement => sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals omega
def statementsProducers : List SAnw → List STyp
  | [] => []
  | s :: ss => statementProducers s ++ statementsProducers ss
termination_by statements => sizeOf statements
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def constantUses : SKonstWert → List STyp
  | .one e => expressionUses e
  | .rows values => values.flatMap constantUses
termination_by v => sizeOf v

/-- Collect written dynamic types before erasing their abstract identity. -/
def typeUses : STyp → List STyp
  | t@(.dyn ..) => [t]
  | .ptr _ _ t | .range t _ _ _ | .array t _ | .wrap t | .embed t _ _ => typeUses t
  | .entry _ none => []
  | .entry _ (some t) => typeUses t
  | _ => []

def signatureUses (s : FnSig) : List STyp :=
  (s.params.map Prod.snd ++ s.res.toList).flatMap typeUses

mutual
def statementUses : SAnw → List STyp
  | .bind _ _ t _ | .bindLib _ _ t _ | .await _ t _ _ | .swap _ t _ _
  | .allocVon _ _ t _ | .bindAxiomOpt _ t _ => t.toList.flatMap typeUses
  | .bindElse _ t _ _ s | .bindAxiomOptElse _ t _ _ s =>
    t.toList.flatMap typeUses ++ statementUses s
  | .alloc _ _ t _ _ none => t.toList.flatMap typeUses
  | .alloc _ _ t _ _ (some s) => t.toList.flatMap typeUses ++ statementUses s
  | .cond _ s arms none => statementUses s ++ statementsUses arms
  | .cond _ s arms (some other) => statementUses s ++ statementsUses arms ++ statementUses other
  | .cases _ arms => statementsUses arms
  | .elsif _ s | .arm _ _ s | .each _ _ _ _ _ _ _ s | .retry _ s | .loop _ s
  | .waive _ s | .trim _ _ s | .locks _ _ s | .watch _ s | .grow _ _ s | .child s =>
    statementUses s
  | .callIndElse _ _ _ body | .callElse _ _ _ body => statementUses body
  | .block ss _ => statementsUses ss
  | _ => []
termination_by statement => sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals omega
def statementsUses : List SAnw → List STyp
  | [] => []
  | s :: ss => statementUses s ++ statementsUses ss
termination_by statements => sizeOf statements
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def tableUses : STabTeil → List STyp
  | .tSlot fs => fs.flatMap fun f => typeUses f.ftyp
  | .tConst _ t _ => typeUses t
  | _ => []

mutual
def itemUses : SItemTief → List STyp
  | .fnT s body | .transT _ s body => signatureUses s ++ statementUses body ++ statementProducers body
  | .protoT s | .specT s _ | .asmT s _ => signatureUses s
  | .typeT _ _ ts _ t => (ts ++ t.toList).flatMap typeUses
  | .constT _ t v | .globT _ _ t v _ _ _ => typeUses t ++ constantUses v
  | .atomT _ t _ _ _ | .accT _ t _ _ _
  | .arenaT _ _ _ _ t _ => typeUses t
  | .formatT _ _ _ fs => fs.flatMap fun f => typeUses f.ftyp
  | .tableT _ _ _ _ _ _ ps _ => ps.flatMap tableUses
  | .axiomT _ ps t _ _ _ => (ps.map Prod.snd ++ t.toList).flatMap typeUses
  | .callT c => (c.params.map Prod.snd ++ c.res.toList).flatMap typeUses
  | .devT _ ps _ parts => ps.flatMap (fun p => typeUses p.2) ++ parts.flatMap (fun
      | .reg r => typeUses r.rtyp | _ => [])
  | .walkT w => typeUses w.node
  | .modT _ its | .implGroupT _ _ _ its => itemsUses its
  | .specGroupT _ _ _ fs => fs.flatMap signatureUses
  | .pubT it | .gateT it | .taggedByT it _ => itemUses it
  | _ => []
def itemsUses : List SItemTief → List STyp
  | [] => []
  | it :: its => itemUses it ++ itemsUses its
end

/-- Preserve declaration order; repeated spellings share one generated sum. -/
def uniqueTypes (types : List STyp) : List STyp :=
  types.foldl (fun acc t => if acc.any (beqSTyp t) then acc else acc ++ [t]) []

end Gabbro.Grammatik.Parser.Dyn
