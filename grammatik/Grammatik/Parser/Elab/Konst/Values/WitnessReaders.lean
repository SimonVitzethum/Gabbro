module
public import Grammatik.Parser.Elab.Konst.Values.Expression

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


end Gabbro.Grammatik.Parser.Konst.Values.WitnessReaders

