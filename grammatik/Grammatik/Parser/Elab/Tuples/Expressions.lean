module
public import Grammatik.Parser.Elab.Tuples.Types
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples

def expandExpr (k : Context) (locals : Spec.Locals) (expected : Option STyp) :
    Nat → SExpr → ExpandM SExpr
  | 0, _ => lift (.error "tuple expansion: expression fuel exhausted")
  | fuel + 1, expr => do
    let recur := expandExpr k locals none fuel
    match expr with
    | .built "#tuple" values =>
      let state ← get
      let elements ← match expected with
        | some ty => match tupleElements k state ty with
          | some elements => pure elements
          | none => lift (.error "tuple expression: expected a tuple type")
        | none => lift (values.mapM fun value =>
          match infer k state locals fuel value with
          | some ty => pure ty
          | none => .error "tuple expression: element type cannot be inferred; add a tuple annotation")
      if values.length != elements.length then
        lift (.error "tuple expression: arity mismatch")
      let elements ← elements.mapM (expandType k fuel)
      let .atom name ← intern k elements | lift (.error "tuple expansion: generated type expected")
      let fields ← (values.zip elements).zipIdx.mapM fun ((value, ty), index) => do
        let value ← expandExpr k locals (some ty) fuel value
        pure (.ext .label ["_" ++ toString index] [value])
      pure (.call name fields)
    | .field base field =>
      let base ← recur base
      match natural? field with
      | none => pure (.field base field)
      | some index =>
        let state ← get
        let some ty := infer k state locals fuel base
          | lift (.error "tuple field: base type cannot be inferred")
        let some elements := tupleElements k state ty
          | lift (.error "tuple field: positional access requires a tuple")
        if index >= elements.length then lift (.error "tuple field: index out of range")
        pure (.field base ("_" ++ toString index))
    | .call name args =>
      let params := ((k.environment.heads.finde name).map (·.params)).getD []
      let fields := (recordFields k (.atom name)).getD []
      let args ← args.zipIdx.mapM fun (arg, index) => do
        match arg with
        | .ext .label [label] [value] =>
          let ty := (fields.find? (fun field => strEq field.fname label)).map (·.ftyp)
          return .ext .label [label] [← expandExpr k locals ty fuel value]
        | _ => expandExpr k locals ((params[index]?).map (·.2)) fuel arg
      pure (.call name args)
    | .index base index => return .index (← recur base) (← recur index)
    | .arrow base field => return .arrow (← recur base) field
    | .un op value => return .un op (← recur value)
    | .bin op a b => return .bin op (← recur a) (← recur b)
    | .old value => return .old (← recur value)
    | .built name args => return .built name (← args.mapM recur)
    | .ext .array names args =>
      let element := expected.bind fun ty => match canonical k 128 ty with
        | .array element _ => some element
        | _ => none
      return .ext .array names (← args.mapM (expandExpr k locals element fuel))
    | .ext kind names args => return .ext kind names (← args.mapM recur)
    | expr => pure expr
termination_by structural fuel => fuel

end Gabbro.Grammatik.Parser.Tuples
