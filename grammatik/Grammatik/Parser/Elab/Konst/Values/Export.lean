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
      (letI : Decidable (@Eq Bool (fn.pre.denote args) false) := Bool.decEq _ _
       if @Eq Bool (fn.pre.denote args) false then .logik (.vorbedingung ()) else
         letI : Decidable (@Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) false) :=
           Bool.decEq _ _
         if @Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) false then
           .logik (.nachbedingung ())
         else .ok σ (fn.body.denote args) : RufAusgang (D := declaration params result) ()) := by
  have prePlaces : (fn.program.requires ()).orte = [] := by
    change fn.pre.expr.orte = []
    exact footprint _
  have postPlaces : (fn.program.ensures ()).orte = [] := by
    change fn.post.expr.orte = []
    exact footprint _
  have preEval (before after : World (declaration params result)) :
      eval before (fn.program.requires ()) after args = fn.pre.denote args :=
    fn.pre.equation before after args
  have postEval (before after : World (declaration params result))
      (value : Wert (declaration params result) result) :
      eval before (fn.program.ensures ()) after
        (ergEnv ((declaration params result).erg ()) value args) =
          fn.post.denote (.cons value args) :=
    fn.post.equation before after (.cons value args)
  have preRead :
      σ.lese (Signatur.anfang (declaration params result)
        ((declaration params result).signatur ())) (fn.program.requires ()).orte = σ := by
    rw [prePlaces] <;> rfl
  have preCheck :
      wahr? (eval
        (σ.lese (Signatur.anfang (declaration params result)
          ((declaration params result).signatur ())) (fn.program.requires ()).orte)
        (fn.program.requires ())
        (σ.lese (Signatur.anfang (declaration params result)
          ((declaration params result).signatur ())) (fn.program.requires ()).orte) args) =
        fn.pre.denote args := preEval _ _
  have postRead (after : World (declaration params result)) :
      after.lese (vertragVon (declaration params result) ()).ende
        (fn.program.ensures ()).orte = after := by
    rw [postPlaces] <;> rfl
  have postCheck (before after : World (declaration params result))
      (value : Wert (declaration params result) result) :
      wahr? (eval before (fn.program.ensures ())
        (after.lese (vertragVon (declaration params result) ()).ende
          (fn.program.ensures ()).orte)
        (ergEnv ((declaration params result).erg ()) value args)) =
        fn.post.denote (.cons value args) := postEval _ _ _
  have bodyPlaces : fn.body.expr.orte = [] := footprint _
  have endEquation :
      execEnd O passes (rufAt fn.program O passes depth) (fn.program.rumpf ()) σ args =
        (.zurueck σ (fn.body.denote args) :
          EndAusgang (vertragVon (declaration params result) ()) false params) := by
    change execEnd (V := vertragVon (declaration params result) ()) (l := false)
      O passes (rufAt fn.program O passes depth)
      (.ret (.val fn.body.expr) (List.Perm.refl [])) σ args = _
    simp only [execEnd, ErgExpr.orte, bodyPlaces, World.lese, List.map_nil,
      World.merke, List.nil_append, evalErg, fn.body.equation] <;> rfl
  have noInvariants : (declaration params result).invs = [] := rfl
  erw [rufAt.eq_def]
  dsimp only
  rw [preCheck, preRead]
  letI : Decidable (@Eq Bool (fn.pre.denote args) false) := Bool.decEq _ _
  by_cases hp : @Eq Bool (fn.pre.denote args) false
  · simp only [ite_eq_left hp] <;> rfl
  · simp only [ite_eq_right hp]
    rw [endEquation]
    dsimp only
    rw [postCheck σ σ (fn.body.denote args)]
    letI : Decidable (@Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) false) :=
      Bool.decEq _ _
    by_cases hq : @Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) false
    · simp only [ite_eq_left hq] <;> rfl
    · simp only [ite_eq_right hq, noInvariants, List.filter_nil, List.foldl_nil,
        List.find?_nil, postRead] <;> rfl

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
  have hp : ¬ @Eq Bool (fn.pre.denote args) false := by
    intro wrong
    have impossible : (true : Bool) = false := certificate.requires.symm.trans wrong
    cases impossible
  have postBody : @Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) true :=
    (congrArg (fun answer : Wert (declaration params result) result =>
      fn.post.denote (.cons answer args)) certificate.body).trans certificate.ensures
  have hq : ¬ @Eq Bool (fn.post.denote (.cons (fn.body.denote args) args)) false := by
    intro wrong
    have impossible : (true : Bool) = false := postBody.symm.trans wrong
    cases impossible
  rw [call_equation]
  simp only [ite_eq_right hp, ite_eq_right hq]
  exact congrArg (fun answer : Wert (declaration params result) result =>
    (RufAusgang.ok σ answer : RufAusgang (D := declaration params result) ())) certificate.body

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
termination_by e => sizeOf e

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
  costs : CostBounds (locals k.params) k.constants
    (kostenExpr function.model.body.expr) args k.signature.klauseln

/-- Evaluate once in G, check both predicates, then produce the exact typed literal. -/
def checkCall (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) : Except String (CheckedCall k fns env sources) := do
  let fn ← elaborate k
  match hv : checkArguments fns env k.params sources with
  | .error error => throw ("const argument failure at `" ++ k.name ++ "`: " ++ error)
  | .ok checkedArguments =>
    let values := checkedArguments.values
    have evaluated : Scalar.argumentValues fns env k.params sources = .ok values := by
      simp only [Scalar.argumentValues, hv, Except.map] <;> rfl
    match ha : arguments (declaration (k.params.map Prod.snd) k.erg) k.params values with
    | .error error => throw error
    | .ok args => do
      letI : Decidable (@Eq Bool (fn.model.pre.denote args) true) := Bool.decEq _ _
      if hp : @Eq Bool (fn.model.pre.denote args) true then do
        let costs ← checkCosts k.name (locals k.params) k.constants
          (kostenExpr fn.model.body.expr) args k.signature.klauseln
        let value := fn.model.body.denote args
        letI : Decidable (@Eq Bool (fn.model.post.denote (.cons value args)) true) := Bool.decEq _ _
        if hq : @Eq Bool (fn.model.post.denote (.cons value args)) true then do
          let quoted ← reify (D := declaration (k.params.map Prod.snd) k.erg)
            (Γ := k.params.map Prod.snd) (resultSchemas k) (textLiterals fn.source) 64 k.erg value
          return ⟨fn, values, evaluated, checkedArguments.meaning, args, ha, value, fn.model.body.equation _ _ _,
            ⟨rfl, hp, hq⟩, quoted, costs⟩
        else throw ("const contract violated at `" ++ k.name ++ "`: ensures failed")
      else throw ("const contract violated at `" ++ k.name ++ "`: requires failed")

/-- Portable results carry the same source-bound certificate as scalar results. -/
theorem CheckedCall.cost_bound (call : CheckedCall k fns env sources) (source : SExpr)
    (member : SKlausel.cost source ∈ k.signature.klauseln) :
    ∃ (lower upper : Int) (code : Code (declaration (k.params.map Prod.snd) k.erg)
        (k.params.map Prod.snd) (.int lower upper)),
      SourceMeaning (locals k.params) k.constants source ⟨_, code⟩ ∧
      ∀ before after, (kostenExpr call.function.model.body.expr : Int) ≤
        (eval before code.expr after call.args).n :=
  call.costs.bound source member

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
