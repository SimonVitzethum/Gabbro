module

public import Grammatik.Parser.Size.Basic
public meta import Lean
public meta import Lean.Util.SCC

public meta section
namespace Gabbro.Grammatik.Parser.Size.Derive
open Lean Meta Elab Command Parser.Term

private structure Node where
  type : Expr
  functionName : Name
  successors : List Nat := []
  deriving Inhabited

private def primitive (type : Expr) : Option Name :=
  if type.isConstOf ``Nat then some ``Gabbro.Grammatik.Parser.Size.nat
  else if type.isConstOf ``Bool then some ``Gabbro.Grammatik.Parser.Size.bool
  else if type.isConstOf ``String then some ``Gabbro.Grammatik.Parser.Size.string
  else none

/-- Collect only actual closed container applications, including nested tuples. -/
private def containers : Expr → Array Expr
  | type@(.app f a) =>
    let inner := containers f ++ containers a
    if type.isAppOfArity ``List 1 || type.isAppOfArity ``Option 1 ||
        type.isAppOfArity ``Prod 2 then inner.push type else inner
  | _ => #[]

private def unique (types : Array Expr) : Array Expr :=
  types.foldl (fun result type => if result.contains type then result else result.push type) #[]

/-- Instantiate constructor parameters before inspecting any field. Source families
    have no indices or dependent fields; unsupported changes stop this derivation. -/
private def fieldTypes (type : Expr) (ctorName : Name) : MetaM (Array Expr) := do
  let info ← getConstInfoCtor ctorName
  let levels := type.getAppFn.constLevels!
  let ctorType := info.type.instantiateLevelParams info.levelParams levels
  forallTelescopeReducing ctorType fun args _ => do
    let params := args.extract 0 info.numParams
    let mut fields := #[]
    for field in args.extract info.numParams args.size do
      -- Constructor defaults use optParam; its carrier is the same original
      -- field type and sizeOf instance, not a second representation.
      let fieldType ← whnf ((← inferType field).replaceFVars params type.getAppArgs)
      if fieldType.hasFVar then throwError "exact source size: dependent constructor field in {ctorName}"
      if ← isProp fieldType then throwError "exact source size: unexpected proof field in {ctorName}"
      fields := fields.push fieldType
    return fields

private def constructors (type : Expr) : MetaM (List Name) := do
  let info ← getConstInfoInduct type.getAppFn.constName!
  if info.numIndices != 0 then throwError "exact source size: indexed family {info.name}"
  return info.ctors

private def indexOf (nodes : Array Node) (type : Expr) : MetaM Nat :=
  match nodes.findIdx? (fun node => node.type == type) with
  | some index => pure index
  | none => throwError "exact source size: missing original field type {type}"

private def producer (nodes : Array Node) (type : Expr) : MetaM Name := do
  if let some name := primitive type then return name
  return nodes[← indexOf nodes type]!.functionName

private def makeNodes (types : Array Expr) (baseName : Name) : MetaM (Array Node) := do
  let mut allTypes := types
  for type in types do
    for ctorName in ← constructors type do
      for fieldType in ← fieldTypes type ctorName do
        allTypes := allTypes ++ containers fieldType
  allTypes := unique allTypes
  let mut nodes := allTypes.mapIdx fun index type =>
    { type, functionName := baseName.appendAfter ("_part_" ++ toString index) : Node }
  for index in [:nodes.size] do
    let mut successors := []
    for ctorName in ← constructors nodes[index]!.type do
      for fieldType in ← fieldTypes nodes[index]!.type ctorName do
        if (primitive fieldType).isNone then
          successors := (← indexOf nodes fieldType) :: successors
    nodes := nodes.modify index fun node => { node with successors }
  return nodes

private def makeAlternative (nodes : Array Node) (type : Expr) (ctorName : Name) :
    TermElabM (TSyntax ``matchAlt) := do
  let info ← getConstInfoCtor ctorName
  let fields ← fieldTypes type ctorName
  let mut patterns : Array Term := #[]
  for _ in [:info.numParams] do patterns := patterns.push (← `(term| _))
  let mut certificates : Array (Ident × Term) := #[]
  let mut sum : Term ← `(term| (1 : Nat))
  let mut canonical : Term ← `(term| (1 : Nat))
  let mut proof : Term ← `(term| rfl)
  for index in [:fields.size] do
    let argument := mkIdent (← mkFreshUserName `field)
    let certificate := mkIdent (← mkFreshUserName `size)
    patterns := patterns.push argument
    let call ← `(term| $(mkIdent (← producer nodes fields[index]!)) $argument)
    certificates := certificates.push (certificate, call)
    sum ← `(term| $sum + ($certificate:ident).val)
    canonical ← `(term| $canonical + sizeOf $argument)
    proof ← `(term| congr (congrArg Nat.add $proof) ($certificate:ident).property)
  let spec ← `(Parser.Tactic.simpLemma| $(mkIdent (ctorName ++ `sizeOf_spec)):term)
  let mut rhs ← `(term| ⟨$sum, by
    simpa only [$spec] using (show $sum = $canonical from $proof)⟩)
  for (certificate, call) in certificates.reverse do
    rhs ← `(term| let $certificate := $call; $rhs)
  let pattern ← `(term| @$(mkIdent ctorName) $patterns:term*)
  `(matchAltExpr| | $pattern => $rhs)

private def makeDefinition (nodes : Array Node) (index : Nat) (recursive : Bool) :
    TermElabM (TSyntax `command) := do
  let node := nodes[index]!
  let type ← PrettyPrinter.delab node.type
  let functionName := mkIdent node.functionName
  let major := mkIdent (← mkFreshUserName `value)
  let binder ← `(Lean.Parser.Term.bracketedBinderF| ($major : $type))
  let binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[⟨binder.raw⟩]
  let discriminant ← `(Lean.Parser.Term.matchDiscr| $major:term)
  let discriminants := #[discriminant]
  let resultType ← `(term| { n : Nat // n = sizeOf $major })
  let mut alternatives := #[]
  for ctorName in ← constructors node.type do
    alternatives := alternatives.push (← makeAlternative nodes node.type ctorName)
  let body ← `(term| match $[$discriminants],* with $alternatives:matchAlt*)
  let termSuffix ← if recursive
    then `(Lean.Parser.Termination.suffix|
      termination_by sizeOf $major
      decreasing_by
        all_goals simp_wf
        all_goals omega)
    else `(Lean.Parser.Termination.suffix|)
  `(command| private def $functionName:ident $binders:bracketedBinder* :
      $resultType:term := $body:term
    $termSuffix:suffix)

/-- Emit each dependency component separately; recursive calls consume actual
    constructor children. Every result carries its canonical constructor-sum proof. -/
private def emit (output : Ident) (types : Array Expr) (root : Expr) : CommandElabM Unit := do
  let baseName := output.getId
  let nodes ← liftTermElabM <| makeNodes (types.push root) baseName
  let groups := Lean.SCC.scc (List.range nodes.size) (fun index => nodes[index]!.successors)
  for group in groups do
    let recursive := group.length > 1 || group.any (fun index => nodes[index]!.successors.contains index)
    let mut definitions : Array (TSyntax `command) := #[]
    for index in group do
      definitions := definitions.push (← liftTermElabM <| makeDefinition nodes index recursive)
    if recursive then
      elabCommand (← `(command| mutual $definitions:command* end))
    else
      for definition in definitions do elabCommand definition
  let functionName ← liftTermElabM <| producer nodes root
  let type ← liftTermElabM <| PrettyPrinter.delab root
  elabCommand (← `(command| @[no_expose] public def $output:ident (input : $type:term) :
    { n : Nat // n = sizeOf input } := $(mkIdent functionName) input))

syntax (name := deriveSourceSize) "derive_source_size " ident " for " ident
  " with " "[" ident,* "]" : command

@[command_elab deriveSourceSize] def elaborate : CommandElab := fun stx => do
  let `(command| derive_source_size $output for $root with [$names:ident,*]) := stx
    | throwUnsupportedSyntax
  let types ← liftTermElabM <| names.getElems.mapM (fun name => Term.elabType name)
  let type ← liftTermElabM <| Term.elabType root
  let root := mkApp (mkConst ``List [Level.zero]) type
  emit output types root

end Gabbro.Grammatik.Parser.Size.Derive
