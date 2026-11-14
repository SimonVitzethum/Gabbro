module
public import Grammatik.Parser.Elab.Tuples.Bodies
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples
open Uebersetze

def expandEffect (k : Context) (locals : Spec.Locals) : SEffekt → ExpandM SEffekt
  | .reads value => return .reads (← expandExpr k locals none 1000 value)
  | .writes value => return .writes (← expandExpr k locals none 1000 value)
  | .locks shared value => return .locks shared (← expandExpr k locals none 1000 value)
  | .takes value => return .takes (← expandExpr k locals none 1000 value)
  | .posts value => return .posts (← expandExpr k locals none 1000 value)
  | effect => pure effect

def expandClause (k : Context) (locals : Spec.Locals) : SKlausel → ExpandM SKlausel
  | .needs value => return .needs (← expandExpr k locals none 1000 value)
  | .gives value => return .gives (← expandExpr k locals none 1000 value)
  | .cost value => return .cost (← expandExpr k locals none 1000 value)
  | .drops value => return .drops (← expandExpr k locals none 1000 value)
  | .effs effects => return .effs (← effects.mapM (expandEffect k locals))
  | clause => pure clause

def expandSignature (k : Context) (sig : FnSig) : ExpandM FnSig := do
  let params ← sig.params.mapM fun (name, ty) => return (name, ← expandType k 1000 ty)
  let result ← sig.res.mapM (expandType k 1000)
  let locals := result.toList.map (fun ty => ("#tuple-result", ty)) ++ params
  pure { sig with
    params := params
    res := result
    klauseln := ← sig.klauseln.mapM (expandClause k locals) }

def expandConstant (k : Context) (expected : Option STyp) : Nat → SKonstWert → ExpandM SKonstWert
  | 0, _ => lift (.error "tuple expansion: constant fuel exhausted")
  | fuel + 1, .one value => return .one (← expandExpr k [] expected fuel value)
  | fuel + 1, .rows rows =>
    let element := expected.bind fun ty => match ty with
      | .array ty _ => some ty
      | _ => none
    return .rows (← rows.mapM (expandConstant k element fuel))
termination_by structural fuel => fuel

/-- Field text stays intact, including all metadata. Only tuple schema discovery is performed
    here; the ordinary record collector later reads the original fields and checks every duty. -/
def discoverFields (k : Context) (fields : List SFeld) : ExpandM Unit := do
  for field in fields do
    let _ ← expandType k 1000 field.ftyp

def expandItem (k : Context) : Nat → SItemTief → ExpandM SItemTief
  | 0, _ => lift (.error "tuple expansion: item fuel exhausted")
  | fuel + 1, item => do
    let ty := expandType k 1000
    let ex := expandExpr k [] none 1000
    match item with
    | .fnT sig body =>
      let sig ← expandSignature k sig
      let locals := sig.res.toList.map (fun ty => ("#tuple-result", ty)) ++ sig.params
      let statements ← expandStatement k locals sig.res 100000 body
      pure (.fnT sig (match statements with | [body] => body | ss => .block ss none))
    | .protoT sig => return .protoT (← expandSignature k sig)
    | .specT sig value =>
      let sig ← expandSignature k sig
      return .specT sig (← expandExpr k sig.params sig.res 1000 value)
    | .typeT flags name args order (some (.raw text)) =>
      if text.startsWith "{" && !flags.contains "tagged" && !flags.contains "linear" then
        discoverFields k (← lift (uRecordFields text))
      pure (.typeT flags name args order (some (.raw text)))
    | .typeT flags name args order result =>
      return .typeT flags name (← args.mapM ty) order (← result.mapM ty)
    | .constT name annotation value =>
      let annotation ← ty annotation
      return .constT name annotation (← expandConstant k (some annotation) 1000 value)
    | .globT mu name annotation value aligned sectionName shared =>
      let annotation ← ty annotation
      return .globT mu name annotation (← expandConstant k (some annotation) 1000 value)
        (← aligned.mapM ex) sectionName shared
    | .tableT name source count backed owner shared parts space =>
      let parts ← parts.mapM fun
        | .tSlot fields => do
          discoverFields k fields
          pure (.tSlot fields)
        | .tConst name annotation value => do
          let annotation ← ty annotation
          return .tConst name annotation (← expandConstant k (some annotation) 1000 value)
        | part => pure part
      return .tableT name source (← count.mapM ex) backed owner shared parts space
    | .formatT name version endian fields =>
      discoverFields k fields
      return .formatT name (← version.mapM ex) endian fields
    | .arenaT name lo hi maximum annotation provider =>
      return .arenaT name (← ex lo) (← ex hi) (← maximum.mapM ex) (← ty annotation) provider
    | .atomT name annotation payload order observer =>
      return .atomT name (← ty annotation) (← payload.mapM (fun es => es.mapM ex)) order observer
    | .callT call =>
      let params ← call.params.mapM fun (name, annotation) => return (name, ← ty annotation)
      return .callT { call with
        params := params
        res := ← call.res.mapM ty }
    | .axiomT name params result predicate effects hardware =>
      let params ← params.mapM fun (name, annotation) => return (name, ← ty annotation)
      return .axiomT name params (← result.mapM ty)
        (← predicate.mapM (expandExpr k params none 1000)) (← effects.mapM (expandEffect k params)) hardware
    | .modT name items => return .modT name (← items.mapM (expandItem k fuel))
    | .pubT item => return .pubT (← expandItem k fuel item)
    | .gateT item => return .gateT (← expandItem k fuel item)
    | item => pure item
termination_by structural fuel => fuel

/-- The interning context of a unit: constants, aliases and the ordinary source types. -/
def prepareContext (items : List SItemTief) : Context :=
  let constants := uConstsRech (uKonstFns items) items []
  let aliases := uAliase constants items ++ uAliasBreiten items ++
    constants.map (fun entry => (entry.1, (entry.2, entry.2)))
  -- A partial view is only an interning aid; the complete canonical collector still runs later.
  let ordinary := items.filter fun
    | .typeT _ _ _ _ (some (.tuple _)) => false
    | _ => true
  let sourceTypes := (uTypes constants aliases [] ordinary).toOption.getD { types := [] }
  { items := items
    constants := constants
    aliases := aliases
    sourceTypes := sourceTypes }

/-- The tuple pass runs after static instantiation and before call lifting. It returns the actual
    generated declarations for the shared name-hygiene gate. No kernel or IR rule is introduced. -/
def expand (items : List SItemTief) : Except String (List SItemTief × List String) := do
  let k := prepareContext items
  let (items, state) ← (items.mapM (expandItem k 100000)).run {}
  pure (state.records.map Record.declaration ++ items, state.records.map (·.name))

end Gabbro.Grammatik.Parser.Tuples
