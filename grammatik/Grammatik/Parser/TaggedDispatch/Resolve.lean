module

public import Grammatik.Parser.TaggedDispatch.Signature
public import Grammatik.Parser.Spec.Expand
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- A checked overload, selected by the receiver's declared sum type. -/
structure TaggedBinding where
  source : String
  receiver : Nat
  sumName : String
  signature : FnSig
  deriving Repr

def taggedDispatchName (sumName spec member : String) : String :=
  "#tagged-" ++ sumName ++ "::" ++ spec ++ "::" ++ member

def taggedCanonicalSignature (parameter : String) (sig : FnSig) : FnSig :=
  { sig with
    params := sig.params.map fun (n, t) => (n, taggedSubstituteType parameter (.atom "Self") t)
    res := sig.res.map (taggedSubstituteType parameter (.atom "Self")) }

/-- Return and reason propagation use existing source constructs. Each reason arm
    returns its named reason, preserving the ordinary reason-channel checks. -/
def taggedCallBody (items : List SItemTief) (sig : FnSig) (call : SExpr) : SAnw :=
  let result := sig.res.map (fun _ => SExpr.variable "#dispatch-result")
  let statement := match sig.fehler with
    | none => match sig.res, call with
      | none, .call target args => SAnw.call target args
      | _, _ => .bind false "#dispatch-result" none call
    | some reason =>
      let cases := items.filterMap fun
        | .whyT n cs _ => if strEq n reason then some cs else none
        | _ => none
      let arms := cases.flatten.map fun c =>
        SAnw.arm c.1 none (.block [] (some (.ret (some (.why reason c.1)))))
      .bindElse "#dispatch-result" none call "#dispatch-error"
        (.block [.cases (.variable "#dispatch-error") arms] none)
  .block [statement] (some (.ret result))

/-- Check and expand one parsed `by` declaration. Contracts remain written spec
    clauses; only effects are replaced by the union of the actual case effects.
    The ordinary elaborator and proof obligations check all generated functions. -/
def resolveTaggedDeclaration (items : List SItemTief) (decl : SItemTief) (spec : String) :
    Except String (List SItemTief × List TaggedBinding) := do
  let (sumName, variants) ← match decl with
    | .typeT ["tagged"] name [] [] (some (.raw _)) => do
      let schemas ← Uebersetze.uSumSchemas [decl]
      match schemas with
      | [schema] => pure (name, schema.cases)
      | _ => throw ("tagged-dispatch-invalid-declaration: " ++ name)
    | _ => throw "tagged-dispatch-invalid-declaration"
  let group ← match items.filterMap (fun
      | .specGroupT n ps es fs => if strEq n spec then some (Spec.Group.mk n ps es fs) else none
      | _ => none) with
    | [entry] => pure entry
    | [] => throw ("tagged-dispatch-unknown-spec: " ++ spec)
    | _ => throw ("tagged-dispatch-duplicate-spec: " ++ spec)
  let [parameter] := group.types | throw "tagged-dispatch-type-arity"
  let functions := group.functions
  let impls := (Spec.instances items).zipIdx.filterMap fun (instance, index) =>
    match instance.types with
    | [ty] =>
      if strEq instance.group spec then some (TaggedImplementation.mk ty
        (instance.functions.filterMap fun
          | .fnT sig _ => some (sig.name, { sig with name := Spec.implementationName index sig.name })
          | _ => none)) else none
    | _ => none
  let checked ← checkTaggedGroup (functions.map (taggedCanonicalSignature parameter)) variants impls
  let mut output := [decl]
  let mut bindings := []
  for (sig, cases) in checked do
    let receiver := (sig.params.takeWhile (fun p => !beqSTyp p.2 (.atom "Self"))).length
    let args := sig.params.map (fun p => SExpr.variable p.1)
    let effects := cases.flatMap fun c =>
      (impls.flatMap (·.functions)).flatMap fun (_, actual) =>
        if c.implementation == some actual.name then
          actual.klauseln.flatMap (fun | .effs es => es | _ => []) else []
    let generated := { sig with art := "impl", name := taggedDispatchName sumName spec sig.name,
      params := sig.params.map fun (n, t) => (n, taggedSubstituteSelf (.atom sumName) t),
      klauseln := sig.klauseln.filter (fun | .effs _ => false | _ => true) ++ [.effs effects] }
    let body ← expandTaggedDispatch (.variable ((sig.params[receiver]?).getD ("", .atom "")).1)
      (args.take receiver) (args.drop (receiver + 1)) cases (taggedCallBody items generated)
    output := output ++ [.fnT generated (.block [body] none)]
    bindings := bindings ++ [⟨spec ++ "::" ++ sig.name, receiver, sumName, generated⟩]
  pure (output, bindings)

end Gabbro.Grammatik.Parser
