module
public import Grammatik.Parser.Elab.Konst.Scalar.Expression

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
