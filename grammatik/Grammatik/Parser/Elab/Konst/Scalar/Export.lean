module
public import Grammatik.Parser.Elab.Konst.Scalar.Call
public import Grammatik.Parser.Elab.Konst.Scalar.Quotation

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Uebersetze

/-- The actual source elaboration equations accompany the typed call model.
    In particular, neither predicate can be replaced by an unproved `true`. -/
structure SourceFunction (k : UKonstFn) (lo hi : Int) where
  resultType : k.erg = .int lo hi
  source : SExpr
  sourceBody : k.rumpf = .block [] (some (.ret (some source)))
  model : Function (k.params.map Prod.snd) lo hi
  bodySource : expression (locals k.params) source = .ok ⟨_, model.body.2.2⟩
  preSource : clauses (locals k.params) false k.signature.klauseln = .ok model.pre
  postSource : clauses (locals (("result", .int lo hi) :: k.params)) true
    k.signature.klauseln = .ok model.post

/-- Elaborate the original body and both original contracts before computing a candidate. -/
def elaborate (k : UKonstFn) :
    Except String (Sigma fun lo : Int => Sigma fun hi : Int => SourceFunction k lo hi) :=
  match hr : k.erg, hb : k.rumpf with
  | .int lo hi, .block [] (some (.ret (some source))) => do
    match he : expression (D := declaration (k.params.map Prod.snd) (.int lo hi))
        (locals k.params) source with
    | .error error => throw error
    | .ok ⟨.int lower upper, body⟩ =>
      match hp : clauses (D := declaration (k.params.map Prod.snd) (.int lo hi))
          (locals k.params) false k.signature.klauseln with
      | .error error => throw error
      | .ok pre =>
        match hq : clauses (D := declaration (k.params.map Prod.snd) (.int lo hi))
            (locals (("result", .int lo hi) :: k.params)) true k.signature.klauseln with
        | .error error => throw error
        | .ok post =>
          return ⟨lo, hi, ⟨hr, source, hb, ⟨pre, ⟨lower, upper, body⟩, post⟩, he, hp, hq⟩⟩
    | .ok _ => throw ("const type failure at `" ++ k.name ++ "`: integer result expected")
  | _, _ => .error ("const body without a certified scalar G derivation at `" ++ k.name ++ "`")

/-- Evaluate each argument at its own declared type, rather than at the callee's
    result type. A result narrower than a parameter must not truncate its argument. -/
def argumentValues (fns : List UKonstFn) (env : List (String × Int)) :
    List (String × Ty) → List SExpr → Except String (List Int)
  | [], [] => .ok []
  | (_, .int lo hi) :: rest, source :: sources => do
    match uKonstWert lo hi fns env 64 source with
    | none => throw "const argument is not a compile-time value in its declared range"
    | some value => return value :: (← argumentValues fns env rest sources)
  | _, _ => .error "const argument type or arity mismatch"

/-- Every delivered value carries its exact source elaboration and a generic G call
    certificate. `uKonstWert` is an untrusted candidate, checked for agreement here. -/
structure CheckedCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) where
  lo : Int
  hi : Int
  function : SourceFunction k lo hi
  values : List Int
  evaluated : argumentValues fns env k.params sources = .ok values
  args : Env (declaration (k.params.map Prod.snd) (.int lo hi)) (k.params.map Prod.snd)
  bound : arguments (declaration (k.params.map Prod.snd) (.int lo hi)) k.params values = .ok args
  bindings : List (String × Int)
  boundNames : uKonstBinde k.params values = some bindings
  value : Int
  candidate : uKonstWert lo hi fns bindings 64 function.source = some value
  certificate : Function.Certificate function.model args value
  quoted : Quoted args function.model.body.2.2.expr
  syntaxValue : quoted.syntax.evalInt = some value

/-- The sole call-site folding entry point. Every failure names the source callee. -/
def checkCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) :
    Except String (CheckedCall k fns env sources) := do
  let ⟨lo, hi, fn⟩ ← elaborate k
  match hv : argumentValues fns env k.params sources with
  | .error error => throw ("const open argument at `" ++ k.name ++ "`: " ++ error)
  | .ok values =>
    match ha : arguments (declaration (k.params.map Prod.snd) (.int lo hi)) k.params values with
    | .error error => throw error
    | .ok args =>
      if fn.model.pre.denote args = false then
        throw ("const contract violated at `" ++ k.name ++ "`: requires failed")
      else
      match hn : uKonstBinde k.params values with
      | none => throw ("const argument binding failed at `" ++ k.name ++ "`")
      | some bindings =>
        match hc : uKonstWert lo hi fns bindings 64 fn.source with
        | none => throw ("const range failure at `" ++ k.name ++ "`: arithmetic overflow or no value")
        | some value =>
          let cert ← Function.certify k.name fn.model args value
          let quoted ← quote fn.model.body.2.2.expr args
          have syntaxValue : quoted.syntax.evalInt = some value := by
            rw [quoted.equation (world _ _) (world _ _), fn.model.body.2.2.equation, cert.body]
          return ⟨lo, hi, fn, values, hv, args, ha, bindings, hn, value, hc, cert, quoted, syntaxValue⟩

/-- Every value the actual replacement entry point can obtain denotes the ordinary
    machine G call of its source-derived body, with both contracts retained. -/
theorem CheckedCall.sound (call : CheckedCall k fns env sources)
    (σ : World (declaration (k.params.map Prod.snd) (.int call.lo call.hi)))
    (O : Orakel (declaration (k.params.map Prod.snd) (.int call.lo call.hi)))
    (passes depth : Nat) :
    rufAt call.function.model.program O passes (depth + 1) () σ call.args =
      .ok σ (⟨call.value, call.certificate.range.1, call.certificate.range.2⟩ : Zahl call.lo call.hi) :=
  call.certificate.sound σ O passes depth

end Gabbro.Grammatik.Parser.Konst.Scalar
