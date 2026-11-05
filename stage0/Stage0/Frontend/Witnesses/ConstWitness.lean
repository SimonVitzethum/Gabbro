module
public import Stage0.Frontend.Witnesses.Constants.Scalar
public import Stage0.Frontend.Witnesses.Constants.IntegerPrograms
import all Grammatik.Parser.Elab.Generic.Substitution
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
import all Grammatik.Parser.Elab.Konst.Ersetzung
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Konst.Scope
import all Grammatik.Parser.Elab.Konst.Replacement
import all Grammatik.Parser.Elab.Konst.Scalar.Model
import all Grammatik.Parser.Elab.Konst.Scalar.Expression
import all Grammatik.Parser.Elab.Konst.Scalar.Names
import all Grammatik.Parser.Elab.Konst.Scalar.Arguments
import all Grammatik.Parser.Elab.Konst.Scalar.KExpr
import all Grammatik.Parser.Elab.Konst.Scalar.Export
import all Grammatik.Parser.Elab.Konst.Values.Expression
import all Grammatik.Parser.Elab.Konst.Values.Quotation
import all Grammatik.Parser.Elab.Konst.Values.Export

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- This is the actual source collector, not a manually supplied different function. -/
theorem collected_zeuge :
    uKonstFns [.fnT signature function.rumpf] = [function] := by cbv

/-- Two different arguments yield their checked exact results through the production pass. -/
theorem two_values_zeuge :
    ersetzeSExpr [function] (.call "increment" [.lit 3]) = .ok (.lit 4) ∧
    ersetzeSExpr [function] (.call "increment" [.lit 5]) = .ok (.lit 6) := by
  exact ⟨ConstPhases.increment_three_value, ConstPhases.increment_five_value⟩

/-- Both source-derived certificates and KExpr denotations are generated together. -/
theorem two_certificates_zeuge :
    ∃ first : Scalar.CheckedCall function [function] [] [.lit 3],
    ∃ second : Scalar.CheckedCall function [function] [] [.lit 5],
      Scalar.checkCall function [function] [] [.lit 3] = .ok first ∧
      Scalar.checkCall function [function] [] [.lit 5] = .ok second ∧
      first.value = 4 ∧ second.value = 6 ∧
      first.quoted.syntax.evalInt = some 4 ∧ second.quoted.syntax.evalInt = some 6 := by
  obtain ⟨first, firstChecked, firstValue⟩ := ConstPhases.increment_three
  obtain ⟨second, secondChecked, secondValue⟩ := ConstPhases.increment_five
  refine ⟨first, second, firstChecked, secondChecked, firstValue, secondValue, ?_, ?_⟩
  · simpa only [firstValue] using first.syntaxValue
  · simpa only [secondValue] using second.syntaxValue

/-- A requires failure is a named contract refusal, never a literal. -/
theorem requires_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.lit 0]) =
      .error "const contract violated at `increment`: requires failed" := by cbv

/-- A false ensures clause is checked on the computed return value. -/
theorem ensures_refused_zeuge :
    ersetzeSExpr [wrongPost] (.call "increment" [.lit 3]) =
      .error "const contract violated at `increment`: ensures failed" := by cbv

/-- The C17 design keeps a runtime argument refused at the const boundary. -/
theorem open_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.variable "runtime"]) =
      .error "const open argument at `increment`: certified substitution needs closed arguments" := by cbv

/-- Intermediate overflow cannot be cancelled into an apparently valid result. -/
theorem overflow_refused_zeuge :
    ersetzeSExpr [overflows] (.call "increment" [.lit 3]) =
      .error "const range failure at `increment`: arithmetic overflow or no value" := by cbv

/-- Parser-to-checker witness: two const calls with an actual contract in source text. -/
theorem compiled_zeuge : (compile text).toOption.isSome = true := by
  obtain ⟨output, compiled, _⟩ := ConstPhases.increment_compiled
  rw [compiled]
  rfl

def result : Compiled text := (compile text).toOption.get compiled_zeuge

/-- The same checked result goes through AkzeptiertX and the ordinary lowering endpoint. -/
theorem source_pipeline_zeuge :
    compile text = .ok result ∧ CanonicalSourceProgram result ∧
      result.unit.fns.length = 1 ∧ OldSource.accepts result.unit result.program = .ok true := by
  obtain ⟨output, compiled, count⟩ := ConstPhases.increment_compiled
  have same : output = result := Except.ok.inj
    (compiled.symm.trans (except_ok_get compiled_zeuge))
  refine ⟨except_ok_get compiled_zeuge, compile_source_program text result, ?_, result.accepted⟩
  rw [← same]
  exact count

/-- The whole-image theorem remains the production one; const folding adds no runner. -/
theorem image_pipeline_zeuge [Runner.IR.Kern] [Senke.CloneOK]
    (K : Nat) (bytes : List Runner.B) (emitted : irBild text K = .ok bytes) :
    ∃ output : Emitted text K,
      emit text K = .ok output ∧ output.bytes = bytes ∧ output.Correct := by
  obtain ⟨output, he, hb, hc, _⟩ := irBild_correct text K bytes emitted
  exact ⟨output, he, hb, hc⟩

/-- A contracted const call in an initializer uses the same checked source path. -/
theorem initializer_compiled_zeuge :
    (compile initializerText).toOption.isSome = true := by
  obtain ⟨output, compiled, _⟩ := ConstPhases.initializer_compiled
  rw [compiled]
  rfl

/-- An outer constant cannot turn a same-named runtime parameter into a closed argument. -/
theorem parameter_shadow_zeuge :
    let items := [SItemTief.constT "x" (.atom "u8") (.one (.lit 3)),
      .fnT signature function.rumpf,
      .fnT { art := "impl"
        name := "main"
        params := [("x", .atom "u8")]
        res := some (.atom "u8")
        fehler := none
        klauseln := [] }
        (.block [] (some (.ret (some (.call "increment" [.variable "x"])))))]
    konstErsetzePipeline items =
      .error "const open argument at `increment`: certified substitution needs closed arguments" := by cbv

/-- Else-arm reason binders also shadow compile-time constant names. -/
theorem reason_shadow_zeuge :
    let env : Generic.Environment :=
      { declarations := [], constants := [], constantFunctions := [], aliases := [] }
    let bindings : Generic.Bindings := { values := [("reason", .lit 3)] }
    let body := SAnw.bindElse "value" none (.call "foreign" []) "reason"
      (.block [] (some (.ret (some (.call "increment" [.variable "reason"])))) )
    (Generic.rewriteBody env bindings body).run [] = .ok (body, []) := by cbv

/-- Generic specialization cannot bypass the original const contract. -/
theorem generic_contract_refused_zeuge :
    Generic.constantArgument 0 255 [function] [] (.call "increment" [.lit 0]) =
      .error "const contract violated at `increment`: requires failed" := by
  unfold Generic.constantArgument
  change (do
    let replaced ← ersetzeSExpr [function] (.call "increment" [.lit 0])
    match uKonstWert 0 255 [] [] 64 replaced with
    | some n => pure n
    | none => throw "generic constant argument: C17 evaluation failed or exceeded its bound") = _
  rw [requires_refused_zeuge]
  rfl

/-- Boolean truth is not silently accepted as the integer one. -/
theorem argument_type_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.tru]) =
      .error "const argument failure at `increment`: const type failure: expected an integer expression" := by cbv

end Gabbro.Stage0.Frontend.ConstWitness
