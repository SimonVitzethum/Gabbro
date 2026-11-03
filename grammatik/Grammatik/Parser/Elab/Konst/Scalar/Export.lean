module
public import Grammatik.Parser.Elab.Konst.Scalar.Arguments
public import Grammatik.Parser.Elab.Konst.Scalar.KExpr

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar

/-- The declared result range is retained separately from the body's inferred interval.
    G's existing required narrowing checks the return; it never clips an integer. -/
structure Function (params : List Ty) (lo hi : Int) where
  pre : Code (declaration params (.int lo hi)) params .bool
  body : Sigma fun lower => Sigma fun upper =>
    Code (declaration params (.int lo hi)) params (.int lower upper)
  post : Code (declaration params (.int lo hi)) (.int lo hi :: params) .bool

namespace Function
variable {params : List Ty} {lo hi : Int}

def program (fn : Function params lo hi) : Programm (declaration params (.int lo hi)) where
  invariante := fun i => i.elim
  requires := fun _ => fn.pre.expr
  ensures := fun _ => fn.post.expr
  rumpf := fun _ => .narrowRequired fn.body.2.2.expr lo hi
    (.ret (.val (.var .here)) (List.Perm.refl _))

/-- Generic denotation of a source const body, including both predicates and
    the exact declared return range. It uses machine G's ordinary call rule. -/
theorem call_equation (fn : Function params lo hi)
    (args : Env (declaration params (.int lo hi)) params)
    (σ : World (declaration params (.int lo hi)))
    (O : Orakel (declaration params (.int lo hi))) (passes depth : Nat) :
    rufAt fn.program O passes (depth + 1) () σ args =
      if fn.pre.denote args = false then .logik (.vorbedingung ()) else
      if h : lo ≤ (fn.body.2.2.denote args).n ∧ (fn.body.2.2.denote args).n ≤ hi then
        let value : Zahl lo hi := ⟨(fn.body.2.2.denote args).n, h.1, h.2⟩
        if fn.post.denote (.cons value args) = false then .logik (.nachbedingung ())
        else .ok σ value
      else .logik .kapazitaet := by
  simp only [rufAt, program, footprint, World.lese, List.map_nil, World.merke,
    List.nil_append, Code.equation, wahr?]
  split
  · rfl
  · simp only [execEnd, footprint, World.lese, List.map_nil, World.merke,
      List.nil_append, Code.equation]
    split
    · simp only [execEnd, Expr.orte, World.lese, List.map_nil, World.merke,
        List.nil_append, evalErg, eval, Env.get, EndAusgang.schrumpf,
        footprint, Code.equation, ergEnv, wahr?]
      rfl
    · rfl

/-- A successful call is certified at its original argument and result types.
    The generic equation includes all worlds, oracles, budgets and positive depths. -/
structure Certificate (fn : Function params lo hi)
    (args : Env (declaration params (.int lo hi)) params) (value : Int) where
  range : lo ≤ value ∧ value ≤ hi
  body : (fn.body.2.2.denote args).n = value
  requires : fn.pre.denote args = true
  ensures : fn.post.denote (.cons ⟨value, range.1, range.2⟩ args) = true

theorem Certificate.sound {fn : Function params lo hi}
    {args : Env (declaration params (.int lo hi)) params} {value : Int}
    (cert : Certificate fn args value)
    (σ : World (declaration params (.int lo hi)))
    (O : Orakel (declaration params (.int lo hi))) (passes depth : Nat) :
    rufAt fn.program O passes (depth + 1) () σ args =
      .ok σ (⟨value, cert.range.1, cert.range.2⟩ : Zahl lo hi) := by
  rw [call_equation]
  simp only [cert.requires, Bool.true_eq_false, ↓reduceIte, cert.body]
  simp only [cert.range, ↓reduceDIte, cert.ensures, Bool.true_eq_false, ↓reduceIte]

/-- Checking is deterministic and proof-producing; failures retain a named reason. -/
def certify (name : String) (fn : Function params lo hi)
    (args : Env (declaration params (.int lo hi)) params) (value : Int) :
    Except String (Certificate fn args value) :=
  if hr : lo ≤ value ∧ value ≤ hi then
    if hb : (fn.body.2.2.denote args).n = value then
      if hp : fn.pre.denote args = true then
        if hq : fn.post.denote (.cons ⟨value, hr.1, hr.2⟩ args) = true then
          .ok ⟨hr, hb, hp, hq⟩
        else .error ("const contract violated at `" ++ name ++ "`: ensures failed")
      else .error ("const contract violated at `" ++ name ++ "`: requires failed")
    else .error ("const evaluator mismatch at `" ++ name ++ "`: candidate differs from machine G")
  else .error ("const range failure at `" ++ name ++ "`: result outside declared type")

end Function
end Gabbro.Grammatik.Parser.Konst.Scalar
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Uebersetze

/-- The actual source elaboration equations accompany the typed call model.
    In particular, neither predicate can be replaced by an unproved `true`. -/
structure SourceFunction (k : UKonstFn) (lo hi : Int) where
  resultType : k.erg = .int lo hi
  source : SExpr
  sourceBody : k.rumpf = .block [] (some (.ret (some source)))
  model : Function (k.params.map Prod.snd) lo hi
  normalization : Normalized (D := declaration (k.params.map Prod.snd) (.int lo hi))
    (locals k.params) k.constants source
  bodySource : normalization.code = ⟨_, model.body.2.2⟩
  preSource : normalizeClauses (locals k.params) k.constants false k.signature.klauseln = .ok model.pre
  postSource : normalizeClauses (locals (("result", .int lo hi) :: k.params)) k.constants true
    k.signature.klauseln = .ok model.post

/-- The source-expression induction reaches the exact body retained by the call
    certificate, not an independently supplied post-normalization elaboration. -/
theorem SourceFunction.normalized (fn : SourceFunction k lo hi) :
    expression (locals k.params) (normalizeNames (locals k.params) k.constants fn.source) =
      .ok ⟨_, fn.model.body.2.2⟩ := by
  simpa only [fn.bodySource] using fn.normalization.meaning.normalized

/-- Elaborate the original body and both original contracts before computing a candidate. -/
def elaborate (k : UKonstFn) :
    Except String (Sigma fun lo : Int => Sigma fun hi : Int => SourceFunction k lo hi) :=
  match hr : k.erg, hb : k.rumpf with
  | .int lo hi, .block [] (some (.ret (some source))) => do
    let normalized ← normalize (D := declaration (k.params.map Prod.snd) (.int lo hi))
      (locals k.params) k.constants source
    match he : normalized.code with
    | ⟨.int lower upper, body⟩ =>
      match hp : normalizeClauses (D := declaration (k.params.map Prod.snd) (.int lo hi))
          (locals k.params) k.constants false k.signature.klauseln with
      | .error error => throw error
      | .ok pre =>
        match hq : normalizeClauses (D := declaration (k.params.map Prod.snd) (.int lo hi))
            (locals (("result", .int lo hi) :: k.params)) k.constants true k.signature.klauseln with
        | .error error => throw error
        | .ok post =>
          return ⟨lo, hi, ⟨hr, source, hb, ⟨pre, ⟨lower, upper, body⟩, post⟩, normalized, he, hp, hq⟩⟩
    | _ => throw ("const type failure at `" ++ k.name ++ "`: integer result expected")
  | _, _ => .error ("const body without a certified scalar G derivation at `" ++ k.name ++ "`")

/-- Every delivered value carries its exact source elaboration and a generic G call
    certificate. `uKonstWert` is an untrusted candidate, checked for agreement here. -/
structure CheckedCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) where
  lo : Int
  hi : Int
  function : SourceFunction k lo hi
  values : List Int
  evaluated : argumentValues fns env k.params sources = .ok values
  argumentsMeaning : ArgumentMeaning fns env k.params sources values
  args : Env (declaration (k.params.map Prod.snd) (.int lo hi)) (k.params.map Prod.snd)
  bound : arguments (declaration (k.params.map Prod.snd) (.int lo hi)) k.params values = .ok args
  bindings : List (String × Int)
  boundNames : uKonstBinde k.params values = some bindings
  value : Int
  candidate : uKonstWert lo hi fns bindings 64
    (normalizeNames (locals k.params) k.constants function.source) = some value
  certificate : Function.Certificate function.model args value
  quoted : Quoted args function.model.body.2.2.expr
  syntaxValue : quoted.syntax.evalInt = some value

/-- The sole call-site folding entry point. Every failure names the source callee. -/
def checkCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) :
    Except String (CheckedCall k fns env sources) := do
  let ⟨lo, hi, fn⟩ ← elaborate k
  match hv : checkArguments fns env k.params sources with
  | .error error => throw ("const argument failure at `" ++ k.name ++ "`: " ++ error)
  | .ok checkedArguments =>
    let values := checkedArguments.values
    have evaluated : argumentValues fns env k.params sources = .ok values := by
      simp only [argumentValues, hv, Except.map]
    match ha : arguments (declaration (k.params.map Prod.snd) (.int lo hi)) k.params values with
    | .error error => throw error
    | .ok args =>
      if fn.model.pre.denote args = false then
        throw ("const contract violated at `" ++ k.name ++ "`: requires failed")
      else
      match hn : uKonstBinde k.params values with
      | none => throw ("const argument binding failed at `" ++ k.name ++ "`")
      | some bindings =>
        match hc : uKonstWert lo hi fns bindings 64
            (normalizeNames (locals k.params) k.constants fn.source) with
        | none => throw ("const range failure at `" ++ k.name ++ "`: arithmetic overflow or no value")
        | some value =>
          let cert ← Function.certify k.name fn.model args value
          let quoted ← quote fn.model.body.2.2.expr args
          have syntaxValue : quoted.syntax.evalInt = some value := by
            rw [quoted.equation (world _ _) (world _ _), fn.model.body.2.2.equation, cert.body]
          return ⟨lo, hi, fn, values, evaluated, checkedArguments.meaning, args, ha, bindings, hn, value, hc, cert, quoted, syntaxValue⟩

/-- Every value the actual replacement entry point can obtain denotes the ordinary
    machine G call of its source-derived body, with both contracts retained. -/
theorem CheckedCall.sound (call : CheckedCall k fns env sources)
    (σ : World (declaration (k.params.map Prod.snd) (.int call.lo call.hi)))
    (O : Orakel (declaration (k.params.map Prod.snd) (.int call.lo call.hi)))
    (passes depth : Nat) :
    rufAt call.function.model.program O passes (depth + 1) () σ call.args =
      .ok σ (⟨call.value, call.certificate.range.1, call.certificate.range.2⟩ : Zahl call.lo call.hi) :=
  call.certificate.sound σ O passes depth

/-- The normalized canonical candidate denotes the original source-derived G body.
    The source derivation and candidate agreement are produced by checkCall. -/
theorem CheckedCall.normalized_denotation (call : CheckedCall k fns env sources)
    (before after : World (declaration (k.params.map Prod.snd) (.int call.lo call.hi))) :
    uKonstWert call.lo call.hi fns call.bindings 64
      (normalizeNames (locals k.params) k.constants call.function.source) =
        some (eval before call.function.model.body.2.2.expr after call.args).n := by
  rw [call.function.model.body.2.2.equation, call.certificate.body]
  exact call.candidate

end Gabbro.Grammatik.Parser.Konst.Scalar
