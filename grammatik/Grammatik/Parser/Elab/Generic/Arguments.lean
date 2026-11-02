module
public import Grammatik.Parser.Elab.Generic.Closure
public import Grammatik.Parser.Elab.Generic.Literals
public import Grammatik.Parser.Elab.Generic.PointerTypes
public import Grammatik.Parser.Print.Item.Teil1a
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Simultaneous bindings of an instance. Value binders are removed on entering their scopes. -/
structure Bindings where
  types : List (String × STyp) := []
  values : List (String × SExpr) := []
  functions : List (String × String) := []
  functionArguments : List (String × String) := []
  literals : List (FnSig × SAnw) := []
  requirements : List (STyp × String) := []

/-- Hide constant parameters under value binders; type parameters occupy their own namespace. -/
def Bindings.without (bindings : Bindings) (names : List String) : Bindings :=
  { bindings with
    values := bindings.values.filter (fun p => !names.contains p.1)
    functions := bindings.functions.filter (fun p => !names.contains p.1)
    functionArguments := bindings.functionArguments.filter (fun p => !names.contains p.1) }

/-- Compilation context, shared by argument normalization and body rewriting. -/
structure Environment where
  declarations : List (FnSig × SAnw)
  constants : List (String × Int)
  constantFunctions : List Uebersetze.UKonstFn
  aliases : List (String × (Int × Int))
  globals : List String := []
  /-- Module substitution precedes function instantiation and therefore retains applications. -/
  deferApplications : Bool := false

def tokens (text : String) : Except String (List Token) :=
  match lex text with
  | .ok ts => .ok ts
  | .error _ => .error "generic argument does not lex"

def readType (text : String) : Except String STyp := do
  let ts ← tokens text
  let (ty, rest) ← parseTyp (ts.length * 4 + 32) ts
  match rest with
  | [.ende] => pure ty
  | _ => throw "generic type argument has trailing tokens"

def readValue (text : String) : Except String SExpr := do
  let ts ← tokens text
  let (value, rest) ← parseOr (ts.length * 4 + 32) ts
  match rest with
  | [.ende] => pure value
  | _ => throw "generic constant argument has trailing tokens"

def typeSpelling (ty : STyp) : String := String.intercalate " " ((druckTyp ty).map zeigeTok)

def integerExpression (n : Int) : SExpr :=
  if n < 0 then .un "-" (.lit n.natAbs) else .lit n.toNat

/-- Raw proof and header tails contain tokens rather than binders. Substitution is simultaneous;
    library input regions are deliberately excluded from this operation. -/
def substituteRaw (bindings : Bindings) (text : String) : Except String String := do
  let input ← tokens text
  let output := input.flatMap fun token => match nameText token with
    | some name => match bindings.types.find? (fun p => strEq p.1 name) with
      | some (_, ty) => druckTyp ty
      | none => match bindings.values.find? (fun p => strEq p.1 name) with
        | some (_, value) => druckToks value
        | none => match bindings.functions.find? (fun p => strEq p.1 name) with
          | some (_, target) => [.ident target]
          | none => [token]
    | none => match token with
      | .ende => []
      | _ => [token]
  pure (String.intercalate " " (output.map zeigeTok))

/-- Keep a forwarded static argument in source form until its own instantiation phase. A lifted
    literal's internal name is not source syntax and must never be reparsed as an argument. -/
def substituteArgument (bindings : Bindings) (word : String) : Except String String :=
  match bindings.functionArguments.find? (fun entry => strEq entry.1 word) with
  | some (_, canonical) => .ok canonical
  | none => substituteRaw bindings word

/-- A declaration must be unique even when its generic body is unreachable. -/
def declaration (env : Environment) (name : String) : Except String (FnSig × SAnw) :=
  match env.declarations.filter (fun p => strEq p.1.name name) with
  | [entry] => .ok entry
  | [] => .error ("unknown generic function: " ++ name)
  | _ => .error ("duplicate generic function: " ++ name)

/-- A static parameter type must keep the existing named contract gate until O43 lands. -/
def staticParameterType (bindings : Bindings) (ty : STyp) : Except String STyp := do
  match ty with
  | .raw text =>
    let raw ← substituteRaw bindings text
    let sig ← Uebersetze.uZeigerSig raw
    Uebersetze.uZeigerVertrag sig.klauseln
    pure (.raw raw)
  | _ => throw "static function parameter requires a function-pointer type"

/-- Normalize by the declared kind. Every static function requirement is retained for the
    canonical SigPasst check over the complete elaborated unit, before export succeeds. -/
def normalizeArguments (env : Environment) (outer : Bindings) :
    List SGenericParam → List String → Bindings → Except String (List String × Bindings)
  | [], [], bindings => .ok ([], bindings)
  | .type name [] :: ps, word :: ws, bindings => do
    let ty := surfaceType outer.types outer.values (← readType word)
    let (tail, result) ← normalizeArguments env outer ps ws
      { bindings with types := bindings.types ++ [(name, ty)] }
    pure (typeSpelling ty :: tail, result)
  | .constant name ty :: ps, word :: ws, bindings => do
    let ty := surfaceType bindings.types bindings.values ty
    let numeric ← Uebersetze.uTyp env.aliases [] ty
    let (lo, hi) ← match numeric with
      | .int lo hi => pure (lo, hi)
      | _ => throw "generic constant parameter requires an integer type"
    let value ← constantArgument lo hi env.constantFunctions env.constants
      (expression outer.values (← readValue word))
    let (tail, result) ← normalizeArguments env outer ps ws
      { bindings with values := bindings.values ++ [(name, integerExpression value)] }
    pure (toString value :: tail, result)
  | .type _ (_ :: _) :: _, _, _ => .error "generic spec bounds: conformance rule unavailable"
  | .function name ty :: ps, word :: ws, bindings => do
    let expected ← staticParameterType bindings ty
    let word := match outer.functionArguments.find? (fun p => strEq p.1 word) with
      | some (_, argument) => argument
      | none => word
    let (canonical, argument) ← functionArgument word
    let (target, literals, canonical) ← match argument with
      | .path path => do
        let target := String.intercalate "::" path
        let (sig, _) ← declaration env target
        if !sig.generics.isEmpty then
          throw ("static function argument requires an ordinary function: " ++ target)
        pure (target, [], target)
      | .literal sig body => do
        checkLiteral env.globals sig body
        let target := literalName canonical
        pure (target, [({ sig with name := target }, body)], canonical)
    let (tail, result) ← normalizeArguments env outer ps ws
      { bindings with
        functions := bindings.functions ++ [(name, target)]
        functionArguments := bindings.functionArguments ++ [(name, canonical)]
        literals := bindings.literals ++ literals
        requirements := bindings.requirements ++ [(expected, target)] }
    pure (canonical :: tail, result)
  | _, _, _ => .error "generic argument count does not match declaration"

def normalize (env : Environment) (outer : Bindings) (name : String) (words : List String) :
    Except String Instance := do
  let (sig, _) ← declaration env name
  if sig.generics.isEmpty then throw ("explicit instantiation of non-generic function: " ++ name)
  let (arguments, _) ← normalizeArguments env outer sig.generics words {}
  pure ⟨name, arguments⟩

end Gabbro.Grammatik.Parser.Generic
