module
public import Grammatik.Parser.Elab.Konst.Values.Quotation
public import Grammatik.Parser.Elab.Konst.Scalar.Export

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values
open Uebersetze Scalar

/-- A portable result uses the ordinary typed return and both original contracts. -/
structure Function (params : List Ty) (result : Ty) where
  pre : Code (declaration params result) params .bool
  body : Code (declaration params result) params result
  post : Code (declaration params result) (result :: params) .bool

namespace Function
variable {params : List Ty} {result : Ty}

def program (fn : Function params result) : Programm (declaration params result) where
  invariante := fun i => i.elim
  requires := fun _ => fn.pre.expr
  ensures := fun _ => fn.post.expr
  rumpf := fun _ => .ret (.val fn.body.expr) (List.Perm.refl [])

/-- No result encoding or special execution rule: this is G's ordinary call. -/
theorem call_equation (fn : Function params result)
    (args : Env (declaration params result) params) (σ : World (declaration params result))
    (O : Orakel (declaration params result)) (passes depth : Nat) :
    rufAt fn.program O passes (depth + 1) () σ args =
      if fn.pre.denote args = false then .logik (.vorbedingung ()) else
      if fn.post.denote (.cons (fn.body.denote args) args) = false then .logik (.nachbedingung ())
      else .ok σ (fn.body.denote args) := by
  simp only [rufAt, program, footprint, World.lese, List.map_nil, World.merke,
    List.nil_append, Code.equation, wahr?]
  split
  · rfl
  · simp only [execEnd, ErgExpr.orte, footprint, World.lese, List.map_nil, World.merke,
      List.nil_append, evalErg, Code.equation, EndAusgang.schrumpf, ergEnv, wahr?]
    rfl

structure Certificate (fn : Function params result)
    (args : Env (declaration params result) params)
    (value : Wert (declaration params result) result) where
  body : fn.body.denote args = value
  requires : fn.pre.denote args = true
  ensures : fn.post.denote (.cons value args) = true

theorem Certificate.sound {fn : Function params result}
    {args : Env (declaration params result) params} {value : Wert (declaration params result) result}
    (certificate : Certificate fn args value) (σ : World (declaration params result))
    (O : Orakel (declaration params result)) (passes depth : Nat) :
    rufAt fn.program O passes (depth + 1) () σ args = .ok σ value := by
  rw [call_equation]
  simp only [certificate.requires, Bool.true_eq_false, ↓reduceIte,
    certificate.body, certificate.ensures]

end Function

/-- Source equations retain the body, declared type and original clause list. -/
structure SourceFunction (k : UKonstFn) where
  source : SExpr
  sourceBody : k.rumpf = .block [] (some (.ret (some source)))
  model : Function (k.params.map Prod.snd) k.erg
  bodySource : expression (locals k.params) k.constants (resultSchemas k) 64 k.erg source = .ok model.body
  preSource : normalizeClauses (locals k.params) k.constants false k.signature.klauseln = .ok model.pre
  postSource : normalizeClauses (locals (("result", k.erg) :: k.params)) k.constants true
    k.signature.klauseln = .ok model.post

def elaborate (k : UKonstFn) : Except String (SourceFunction k) :=
  match hb : k.rumpf with
  | .block [] (some (.ret (some source))) => do
    match he : expression (D := declaration (k.params.map Prod.snd) k.erg)
        (locals k.params) k.constants (resultSchemas k) 64 k.erg source with
    | .error error => throw error
    | .ok body =>
      match hp : normalizeClauses (D := declaration (k.params.map Prod.snd) k.erg)
          (locals k.params) k.constants false k.signature.klauseln with
      | .error error => throw error
      | .ok pre =>
        match hq : normalizeClauses (D := declaration (k.params.map Prod.snd) k.erg)
            (locals (("result", k.erg) :: k.params)) k.constants true k.signature.klauseln with
        | .error error => throw error
        | .ok post => return ⟨source, hb, ⟨pre, body, post⟩, he, hp, hq⟩
  | _ => .error ("const body without a certified value G derivation at `" ++ k.name ++ "`")

/-- Preserve the original spellings available for exact short-string quotation. -/
def textLiterals : SExpr → List String
  | .ext .text [text] [] => [text]
  | .field value _ | .index value _ | .arrow value _ | .un _ value | .old value => textLiterals value
  | .bin _ a b => textLiterals a ++ textLiterals b
  | .call _ args | .built _ args | .ext _ _ args => args.flatMap textLiterals
  | _ => []

/-- The candidate is canonical G evaluation. Its literal is certified separately,
    retaining the complete value and its exact source constructor. -/
structure CheckedCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) where
  function : SourceFunction k
  values : List Int
  evaluated : Scalar.argumentValues fns env k.params sources = .ok values
  argumentsMeaning : ArgumentMeaning fns env k.params sources values
  args : Env (declaration (k.params.map Prod.snd) k.erg) (k.params.map Prod.snd)
  bound : arguments (declaration (k.params.map Prod.snd) k.erg) k.params values = .ok args
  value : Wert (declaration (k.params.map Prod.snd) k.erg) k.erg
  computed : eval (world _ _) function.model.body.expr (world _ _) args = value
  certificate : Function.Certificate function.model args value
  quoted : Reified (declaration (k.params.map Prod.snd) k.erg)
    (k.params.map Prod.snd) (resultSchemas k) k.erg value

/-- Evaluate once in G, check both predicates, then produce the exact typed literal. -/
def checkCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) : Except String (CheckedCall k fns env sources) := do
  let fn ← elaborate k
  match hv : checkArguments fns env k.params sources with
  | .error error => throw ("const argument failure at `" ++ k.name ++ "`: " ++ error)
  | .ok checkedArguments =>
    let values := checkedArguments.values
    have evaluated : Scalar.argumentValues fns env k.params sources = .ok values := by
      simp only [Scalar.argumentValues, hv, Except.map]
    match ha : arguments (declaration (k.params.map Prod.snd) k.erg) k.params values with
    | .error error => throw error
    | .ok args =>
      if hp : fn.model.pre.denote args = true then
        let value := fn.model.body.denote args
        if hq : fn.model.post.denote (.cons value args) = true then
          let quoted ← reify (resultSchemas k) (textLiterals fn.source) 64 k.erg value
          return ⟨fn, values, evaluated, checkedArguments.meaning, args, ha, value, fn.model.body.equation _ _ _,
            ⟨rfl, hp, hq⟩, quoted⟩
        else throw ("const contract violated at `" ++ k.name ++ "`: ensures failed")
      else throw ("const contract violated at `" ++ k.name ++ "`: requires failed")

/-- Both call evaluation and literal evaluation yield the same complete typed
    result, for every world, oracle, pass budget and positive recursion depth. -/
theorem CheckedCall.sound (call : CheckedCall k fns env sources)
    (σ : World (declaration (k.params.map Prod.snd) k.erg))
    (O : Orakel (declaration (k.params.map Prod.snd) k.erg)) (passes depth : Nat) :
    rufAt call.function.model.program O passes (depth + 1) () σ call.args = .ok σ call.value ∧
      eval σ call.quoted.expr σ call.args = call.value ∧
      LiteralMeaning (declaration (k.params.map Prod.snd) k.erg) (resultSchemas k) k.erg
        call.quoted.syntax call.value :=
  ⟨call.certificate.sound σ O passes depth, call.quoted.equation σ σ call.args, call.quoted.source⟩

end Gabbro.Grammatik.Parser.Konst.Values
