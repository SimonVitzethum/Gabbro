module
public import Grammatik.Parser.Elab.Konst.ErsetzungTor

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values.WitnessReaders
open Uebersetze Scalar
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/- Pin the result type in each whole reader equation. This lets cbv select the
   canonical branch without rewriting a dependent Code index in place. -/
theorem reader_bool {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat) (source : SExpr) :
    Values.expression (D := D) names globals schemas (fuel + 1) .bool source =
      (do
        let normalized ← Scalar.normalize names globals source
        Values.adapt .bool normalized.code) := by rw [Values.expression] <;> simp

theorem reader_int {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat) (lo hi : Int) (source : SExpr) :
    Values.expression (D := D) names globals schemas (fuel + 1) (.int lo hi) source =
      (do
        let normalized ← Scalar.normalize names globals source
        Values.adapt (.int lo hi) normalized.code) := by rw [Values.expression] <;> simp

theorem reader_text {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel n : Nat) (text : String) :
    Values.expression (D := D) names globals schemas (fuel + 1) (.str n) (.ext .text [text] []) =
      (if n > 1 then .error "const string result exceeds the A28 one-byte maximum"
       else match UebersetzeAllg.bytesZahl (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) with
       | none => .error "const string literal contains a non-byte value"
       | some bytes =>
         if h : bytes.length ≤ n then
           .ok ⟨.strLit bytes h, fun _ => ⟨bytes, h⟩, by intros; rfl⟩
         else .error "const string literal exceeds its declared maximum") := by
  rw [Values.expression]
  by_cases wide : n > 1
  · simp only [if_pos wide]
  · simp only [if_neg wide]
    all_goals
      cases decoded : UebersetzeAllg.bytesZahl
          (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) with
      | none => simp only [decoded]
      | some bytes => simp only [decoded] <;> split <;> rfl

theorem reader_sum {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat)
    (cases : List (Option Ty)) (source : SExpr) :
    Values.expression (D := D) names globals schemas (fuel + 1) (.sum cases) source =
      (do
        let schema ← match schemas.find? (fun schema => schema.spec = cases) with
          | some schema => pure schema
          | none => throw "const tagged result has no resolved schema"
        let (name, payload) ← match source with
          | .variable name => pure (name, none)
          | .call name [value] => pure (name, some value)
          | _ => throw "const tagged result needs a named constructor"
        let some index := schema.cases.findIdx? (fun entry => strEq entry.1 name)
          | throw ("const tagged constructor is unknown: " ++ name)
        if hi : index < cases.length then
          let i : Fin cases.length := ⟨index, hi⟩
          let value ← Values.payloadExpression names globals schemas fuel (cases.get i) payload
          return ⟨.case cases i value.expr,
            fun args => ⟨i, Fall.ofNutzlast D.Fn D.passt cases i (value.denote args)⟩,
            by intros; simp only [eval, value.equation] <;> rfl⟩
        else throw "const tagged constructor lies outside its declared schema") := by
  rw [Values.expression]
  cases selected : schemas.find? (fun schema => schema.spec = cases) <;>
    simp only [selected, bind, Except.bind, pure, Except.pure] <;> rfl

theorem reader_payload {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat) (τ : Ty) (source : SExpr) :
    Values.payloadExpression (D := D) names globals schemas (fuel + 1) (some τ) (some source) =
      (do
        let code ← Values.expression names globals schemas fuel τ source
        return ⟨.val code.expr, code.denote, by intros; simp only [evalNutz, code.equation] <;> rfl⟩) := by
  rw [Values.payloadExpression]

theorem reader_empty {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat) :
    Values.payloadExpression (D := D) names globals schemas (fuel + 1) none none =
      .ok ⟨.empty, fun _ => (), by intros; rfl⟩ := by rw [Values.payloadExpression]

theorem reader_missing {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (schemas : List USum) (fuel : Nat) (τ : Ty) :
    Values.payloadExpression (D := D) names globals schemas (fuel + 1) (some τ) none =
      .error "const tagged constructor payload does not match its declared type" := by
  rw [Values.payloadExpression] <;> simp

/-- Replaying an already certified source function preserves its complete model,
    including both original contracts, before any denotation is projected. -/
theorem elaborate_certified {k : UKonstFn} (certificate : Values.SourceFunction k) :
    Values.elaborate k = .ok certificate := by
  rcases k with ⟨name, params, result, statement, signature, globals, schemas⟩
  rcases certificate with ⟨source, body, ⟨preCode, bodyCode, postCode⟩, typed, pre, post⟩
  dsimp only at body
  cases body
  simp only [Values.elaborate, typed, pre, post, pure, Except.pure]

/-- Substitute the whole elaboration result into the actual checker continuation.
    In particular, do not rewrite inside an abstract Code's Boolean projection. -/
theorem checkCall_elaborated {k : UKonstFn} (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr)
    (fn : Values.SourceFunction k) (accepted : Values.elaborate k = .ok fn) :
    Values.checkCall k fns env sources =
      (match hv : checkArguments fns env k.params sources with
      | .error error => throw ("const argument failure at `" ++ k.name ++ "`: " ++ error)
      | .ok checkedArguments =>
        let values := checkedArguments.values
        have evaluated : Scalar.argumentValues fns env k.params sources = .ok values := by
          simp only [Scalar.argumentValues, hv, Except.map] <;> rfl
        match ha : arguments (declaration (k.params.map Prod.snd) k.erg) k.params values with
        | .error error => throw error
        | .ok args => do
          letI : Decidable (@Eq Bool (fn.model.pre.denote args) true) := Bool.decEq _ _
          if hp : @Eq Bool (fn.model.pre.denote args) true then
            let value := fn.model.body.denote args
            letI : Decidable (@Eq Bool (fn.model.post.denote (.cons value args)) true) := Bool.decEq _ _
            if hq : @Eq Bool (fn.model.post.denote (.cons value args)) true then do
              let quoted ← Values.reify (D := declaration (k.params.map Prod.snd) k.erg)
                (Γ := k.params.map Prod.snd) (Values.resultSchemas k)
                (Values.textLiterals fn.source) 64 k.erg value
              return ⟨fn, values, evaluated, checkedArguments.meaning, args, ha, value,
                fn.model.body.equation _ _ _, ⟨rfl, hp, hq⟩, quoted⟩
            else throw ("const contract violated at `" ++ k.name ++ "`: ensures failed")
          else throw ("const contract violated at `" ++ k.name ++ "`: requires failed") :
        Except String (Values.CheckedCall k fns env sources)) := by
  have transport (next : Values.SourceFunction k → Except String (Values.CheckedCall k fns env sources)) :
      (Values.elaborate k).bind next = (Except.ok fn).bind next :=
    congrArg (fun result : Except String (Values.SourceFunction k) => result.bind next) accepted
  exact transport _

theorem checkCall_failed {k : UKonstFn} (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) (error : String)
    (refused : Values.elaborate k = .error error) :
    Values.checkCall k fns env sources = .error error := by
  have transport (next : Values.SourceFunction k → Except String (Values.CheckedCall k fns env sources)) :
      (Values.elaborate k).bind next = (Except.error error).bind next :=
    congrArg (fun result : Except String (Values.SourceFunction k) => result.bind next) refused
  exact transport _

private theorem portable_projection {k : UKonstFn} {fns : List UKonstFn}
    {env : List (String × Int)} {sources : List SExpr}
    (answer : Except String (Values.CheckedCall k fns env sources)) :
    (do
      let replacement ← (do
        let checked ← answer
        pure (⟨checked.quoted.syntax, .portable checked⟩ : Replacement k fns env sources))
      pure replacement.syntax) = answer.map (fun checked => checked.quoted.syntax) := by
  cases answer <;> rfl

/-- The existing substitution prefix exposes the complete portable call result.
    These premises are phase equations for the original source, not new gates. -/
theorem substitute_portable (fns : List UKonstFn) (name : String)
    (sources args : List SExpr) (k : UKonstFn)
    (arguments : ersetzeSExprListIn [] fns sources = .ok args)
    (callee : fns.find? (fun fn => strEq fn.name name) = some k)
    (constants : k.constants = [])
    (closed : geschlossenSExprListB
      (args.map (normalizeNames ([] : Locals []) [])) = true)
    (portable : Values.resultType k.erg = true) :
    ersetzeSExpr fns (.call name sources) =
      (Values.checkCall k fns [] args).map (fun checked => checked.quoted.syntax) := by
  rcases k with ⟨fnName, params, result, statement, signature, globals, schemas⟩
  dsimp only at constants portable
  cases constants
  simp only [ersetzeSExpr, ersetzeSExprIn, arguments, callee,
    List.filter_nil, closed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases result <;> try {
    have impossible : False := by
      simpa only [Values.resultType, Bool.false_eq_true] using portable
    exact impossible.elim }
  all_goals
    simp only [checkReplacement, portable, Bool.true_eq_true, ↓reduceIte]
    exact portable_projection _


end Gabbro.Grammatik.Parser.Konst.Values.WitnessReaders
