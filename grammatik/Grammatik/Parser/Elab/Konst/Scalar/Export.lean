module
public import Grammatik.Parser.Elab.Konst.Scalar.Names
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
/-- The canonical evaluator of the normalized expression equals evaluation of
    the original source-derived G body. No denotation premise is left to callers:
    normalization, candidate evaluation and agreement were produced by checkCall. -/
theorem CheckedCall.normalized_denotation (call : CheckedCall k fns env sources)
    (before after : World (declaration (k.params.map Prod.snd) (.int call.lo call.hi))) :
    uKonstWert call.lo call.hi fns call.bindings 64
      (normalizeNames (locals k.params) k.constants call.function.source) =
        some (eval before call.function.model.body.2.2.expr after call.args).n := by
  have structural := call.function.normalization.meaning.normalized
  rw [call.function.model.body.2.2.equation, call.certificate.body]
  exact call.candidate

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