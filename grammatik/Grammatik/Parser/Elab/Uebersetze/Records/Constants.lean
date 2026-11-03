module
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

mutual
/-- Route explicit constructor fields through their canonical declared types. Numeric leaves
    use the existing exact-range evaluator, including its const-call contracts. This traversal
    introduces no arithmetic evaluator, defaults, casts or alternate record schema. -/
def uRecordConstant (records : List URecord) (alias : List (String × (Int × Int)))
    (fns : List UKonstFn) (consts : List (String × Int)) (ty : Ty) (source : SExpr) : Option USide :=
  match ty, source with
  | .bool, .tru => some (.truth true)
  | .bool, .fls => some (.truth false)
  | .prod identity fields, .call name args => do
    let schema ← (uRecordOf records (.prod identity fields)).toOption
    if !strEq schema.val.name name then none else do
    let values ← uRecordConstantFields records alias fns consts schema.val.fields args
    (uRecordValues schema.val values).toOption
  | τ, expr => uKonstZeile alias fns consts τ (.one expr)
termination_by sizeOf source

/-- Read and evaluate labelled arguments in source order before the existing schema arranger
    checks completeness/uniqueness and puts the values in declaration order. -/
def uRecordConstantFields (records : List URecord) (alias : List (String × (Int × Int)))
    (fns : List UKonstFn) (consts : List (String × Int)) (fields : List (String × Ty)) :
    List SExpr → Option (List (String × USide))
  | [] => some []
  | .ext .label [label] [value] :: rest => do
    let field ← fields.find? (fun field => strEq field.1 label)
    let side ← uRecordConstant records alias fns consts field.2 value
    let tail ← uRecordConstantFields records alias fns consts fields rest
    pure ((label, side) :: tail)
  | _ => none
termination_by source => sizeOf source
end

/-- The exact nominal type names consumed by constant validation and collection. -/
def uRecordConstantTypes (records : List URecord) : List (String × Ty) :=
  records.map (fun record => (record.name, record.ty))

end Gabbro.Grammatik.Parser.Uebersetze
