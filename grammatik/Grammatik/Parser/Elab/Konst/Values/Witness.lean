module
public import Grammatik.Parser.Elab.Konst.Values.WitnessData
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import Grammatik.Parser.Elab.Konst.Values.WitnessPhases
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

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values.Witness
open Uebersetze Scalar WitnessReaders
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/- Use the whole unfolding equations when dependent fixture projections prevent
   the structural cbv matcher from seeing a constructor-specific reader rule. -/
attribute [local cbv_eval] Values.expression.eq_def Values.payloadExpression.eq_def
attribute [local cbv_eval] reader_bool reader_int reader_text reader_sum
  reader_payload reader_empty reader_missing


namespace Phases

private theorem elaborate_refused {k : UKonstFn} {source : SExpr} {error : String}
    (body : k.rumpf = .block [] (some (.ret (some source))))
    (refused : Values.expression (D := declaration (k.params.map Prod.snd) k.erg)
      (locals k.params) k.constants (Values.resultSchemas k) 64 k.erg source = .error error) :
    Values.elaborate k = .error error := by
  rcases k with ⟨name, params, result, statement, signature, globals, schemas⟩
  dsimp only at body
  cases body
  dsimp only at refused
  unfold Values.elaborate
  dsimp only
  split
  · rename_i actualError found
    have same : actualError = error := Except.error.inj (found.symm.trans refused)
    subst actualError
    rfl
  · rename_i code found
    cases found.symm.trans refused

private theorem wrongTypeSource :
    Values.elaborate { positive with rumpf := .block [] (some (.ret (some (.lit 1)))) } = .error "const value has a different declared type" := by
  apply elaborate_refused (source := (.lit 1)) rfl
  change Values.expression (D := declaration [.int 0 10] .bool)
    (locals [("x", .int 0 10)]) [] [] 64 .bool (.lit 1) = .error _
  rfl

private theorem wrongPayloadSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) } = .error "const value has a different declared type" := by
  apply elaborate_refused (source := (.call "Data" [.tru])) rfl
  change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
    (locals []) [] [{ name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.call "Data" [.tru]) = .error _
  rfl

private theorem unknownTagSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) } = .error "const tagged constructor is unknown: Foreign" := by
  apply elaborate_refused (source := (.variable "Foreign")) rfl
  change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
    (locals []) [] [{ name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.variable "Foreign") = .error _
  rfl

private theorem longTextSource :
    Values.elaborate (shortText "é") = .error "const string literal exceeds its declared maximum" := by
  apply elaborate_refused (source := (.ext .text ["é"] [])) rfl
  change Values.expression (D := declaration [] (.str 1))
    (locals []) [] [] 64 (.str 1) (.ext .text ["é"] []) = .error _
  rfl

private theorem missingPayloadSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) } = .error "const tagged constructor payload does not match its declared type" := by
  apply elaborate_refused (source := (.variable "Data")) rfl
  change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
    (locals []) [] [{ name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.variable "Data") = .error _
  rfl

public theorem wrong_type_result :
    ersetzeSExpr [{ positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }] (.call "positive" [.lit 3]) = .error "const value has a different declared type" := by
  rw [substitute_portable [{ positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }] "positive" [.lit 3] [.lit 3] { positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_failed [{ positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }] [] [.lit 3] "const value has a different declared type" wrongTypeSource]
  rfl

public theorem wrong_payload_result :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }] (.call "tagged" []) = .error "const value has a different declared type" := by
  rw [substitute_portable [{ emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }] "tagged" [] [] { emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_failed [{ emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }] [] [] "const value has a different declared type" wrongPayloadSource]
  rfl

public theorem unknown_tag_result :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }] (.call "tagged" []) = .error "const tagged constructor is unknown: Foreign" := by
  rw [substitute_portable [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }] "tagged" [] [] { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_failed [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }] [] [] "const tagged constructor is unknown: Foreign" unknownTagSource]
  rfl

public theorem long_text_result :
    ersetzeSExpr [(shortText "é")] (.call "shortText" []) = .error "const string literal exceeds its declared maximum" := by
  rw [substitute_portable [(shortText "é")] "shortText" [] [] (shortText "é")
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_failed [(shortText "é")] [] [] "const string literal exceeds its declared maximum" longTextSource]
  rfl

public theorem missing_payload_result :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) }] (.call "tagged" []) = .error "const tagged constructor payload does not match its declared type" := by
  rw [substitute_portable [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) }] "tagged" [] [] { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_failed [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) }] [] [] "const tagged constructor payload does not match its declared type" missingPayloadSource]
  rfl

end Phases

/-- Both Boolean values are delivered, with the original ensures retained. -/
theorem bool_values_zeuge :
    ersetzeSExpr [positive] (.call "positive" [.lit 3]) = .ok .tru ∧
    ersetzeSExpr [positive] (.call "positive" [.lit 0]) = .ok .fls := by
  exact Phases.bool_results

/-- Option absence and the actual present index remain distinct typed values. -/
theorem option_values_zeuge :
    ersetzeSExpr [optional] (.call "optional" [.lit 3]) = .ok (.call "Some" [.lit 3]) ∧
    ersetzeSExpr [absent] (.call "absent" []) = .ok (.call "None" []) := by cbv

/-- Tag identity and complete numeric/Boolean/string payloads survive quotation. -/
theorem tag_values_zeuge :
    ersetzeSExpr [tagged] (.call "tagged" [.lit 4]) = .ok (.call "Data" [.lit 5]) ∧
    ersetzeSExpr [emptyTag] (.call "tagged" []) = .ok (.variable "Empty") ∧
    ersetzeSExpr [flagTag] (.call "tagged" []) = .ok (.call "Flag" [.tru]) ∧
    ersetzeSExpr [textTag] (.call "tagged" []) = .ok (.call "Text" [.ext .text ["Z"] []]) := by
  exact Phases.tag_results

/-- Empty and one-byte results preserve the actual UTF-8 spelling and length. -/
theorem string_values_zeuge :
    ersetzeSExpr [shortText ""] (.call "shortText" []) = .ok (.ext .text [""] []) ∧
    ersetzeSExpr [shortText "A"] (.call "shortText" []) = .ok (.ext .text ["A"] []) := by
  exact Phases.text_results

/-- The production collector binds the Boolean fixture to its actual source signature. -/
theorem bool_collected_zeuge :
    collectFunctions [.fnT positive.signature positive.rumpf] = .ok [positive] := by cbv

/-- A zero-byte maximum is checked separately from an empty string under maximum one. -/
theorem zero_string_zeuge :
    ersetzeSExpr [shortText "" 0] (.call "shortText" []) = .ok (.ext .text [""] []) := by
  exact Phases.zero_text_result

/-- Ordinary reason-tag values keep both their owner and the exact selected case. -/
theorem reason_value_zeuge :
    ersetzeSExpr [reasonTag] (.call "reasonTag" []) = .ok (.why "Reason" "Second") := by cbv

theorem foreign_reason_refused_zeuge :
    ersetzeSExpr [{ reasonTag with rumpf := .block [] (some (.ret (some (.why "Foreign" "Second")))) }]
      (.call "reasonTag" []) = .error "const reason owner is unknown: Foreign" := by cbv

/-- The witnesses instantiate the generic G/literal theorem jointly with a
    successfully generated certificate and a checked complete result value. -/
theorem portable_call_sound_zeuge :
    ∃ call : Values.CheckedCall optional [optional] [] [.lit 3],
      Values.checkCall optional [optional] [] [.lit 3] = .ok call ∧
      call.value = some (⟨3, by decide, by decide⟩ : Zahl 0 3) ∧
      ∀ σ O passes depth,
        rufAt call.function.model.program O passes (depth + 1) () σ call.args = .ok σ call.value ∧
        eval σ call.quoted.expr σ call.args = call.value := by
  have checked : ∃ call : Values.CheckedCall optional [optional] [] [.lit 3],
      Values.checkCall optional [optional] [] [.lit 3] = .ok call ∧
        call.value = some (⟨3, by decide, by decide⟩ : Zahl 0 3) := by
    refine ⟨?call, ?success, ?value⟩
    case success => cbv <;> exact Eq.refl _
    case value => cbv
  obtain ⟨call, success, value⟩ := checked
  refine ⟨call, success, value, ?_⟩
  intro σ O passes depth
  exact ⟨(call.sound σ O passes depth).1, (call.sound σ O passes depth).2.1⟩

/-- The wrong result type never becomes a neutral integer or a success. -/
theorem bool_type_refused_zeuge :
    ersetzeSExpr [{ positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }]
      (.call "positive" [.lit 3]) = .error "const value has a different declared type" := by
  exact Phases.wrong_type_result

theorem option_bound_refused_zeuge :
    ersetzeSExpr [{ optional with
      params := []
      rumpf := .block [] (some (.ret (some (.call "Some" [.lit 4])))) }]
      (.call "optional" []) = .error "const value interval is outside its declared type" := by cbv

theorem tag_payload_refused_zeuge :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }]
      (.call "tagged" []) = .error "const value has a different declared type" := by
  exact Phases.wrong_payload_result

theorem tag_unknown_refused_zeuge :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }]
      (.call "tagged" []) = .error "const tagged constructor is unknown: Foreign" := by
  exact Phases.unknown_tag_result

theorem string_utf8_bound_refused_zeuge :
    ersetzeSExpr [shortText "é"] (.call "shortText" []) =
      .error "const string literal exceeds its declared maximum" := by
  exact Phases.long_text_result

theorem wide_string_refused_zeuge :
    ersetzeSExpr [shortText "A" 2] (.call "shortText" []) =
      .error "const result type without a certified replacement at `shortText`" := by cbv

theorem portable_post_refused_zeuge :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }]
      (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: ensures failed" := by
  exact Phases.post_refused_result

theorem portable_requires_refused_zeuge :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.needs .fls] } }]
      (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: requires failed" := by
  exact Phases.pre_refused_result

theorem tag_missing_payload_refused_zeuge :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) }]
      (.call "tagged" []) =
      .error "const tagged constructor payload does not match its declared type" := by
  exact Phases.missing_payload_result

/-- Statement-position calls keep their call-log-sensitive refusal after value expansion. -/
theorem portable_statement_refused_zeuge :
    let signature : FnSig :=
      { art := "impl"
        name := "main"
        params := []
        res := none
        fehler := none
        klauseln := []
        generics := [] }
    let items := [SItemTief.fnT positive.signature positive.rumpf,
      .fnT signature (.block [.call "positive" [.lit 3]] (some (.ret none)))]
    checkErsetzt items items =
      .error "const call without certified value: refusing runtime export" := by cbv

/-- Original global names in both body and arguments reach their certificates.
    The parameter x shadows the captured global x even in the body derivation. -/
theorem qualified_normalization_zeuge :
    ersetzeSExpr [captured] (.call "captured" [.bin "+" (.variable "math::K") (.lit 1)]) =
      .ok (.lit 11) := by cbv

theorem normalization_denotation_zeuge :
    ∃ call : Scalar.CheckedCall captured [captured] captured.constants
        [.bin "+" (.variable "math::K") (.lit 1)],
      Scalar.checkCall captured [captured] captured.constants
        [.bin "+" (.variable "math::K") (.lit 1)] = .ok call ∧ call.value = 11 ∧
      ∀ before after,
        uKonstWert call.lo call.hi [captured] call.bindings 64
          (normalizeNames (locals captured.params) captured.constants call.function.source) =
          some (eval before call.function.model.body.2.2.expr after call.args).n := by
  have checked : ∃ call : Scalar.CheckedCall captured [captured] captured.constants
      [.bin "+" (.variable "math::K") (.lit 1)],
      Scalar.checkCall captured [captured] captured.constants
        [.bin "+" (.variable "math::K") (.lit 1)] = .ok call ∧ call.value = 11 := by
    refine ⟨?call, ?success, ?value⟩
    case success => cbv <;> exact Eq.refl _
    case value => cbv
  obtain ⟨call, success, value⟩ := checked
  exact ⟨call, success, value, call.normalized_denotation⟩

/-- Runtime binders cannot be closed using a same-named global. -/
theorem original_parameter_refused_zeuge :
    ersetzeSAnwIn ["x"] [captured]
      (.ret (some (.call "captured" [.variable "x"]))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" := by cbv

/-- Quantifier variables, sequential locals and pattern payloads also remain open. -/
theorem binder_refused_zeuge :
    ersetzeSExpr [captured] (.ext .all ["x", "slots", "Slots"]
      [.call "captured" [.variable "x"]]) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" ∧
    ersetzeSAnw [captured] (.block [.bind false "x" none (.lit 2)]
      (some (.ret (some (.call "captured" [.variable "x"]))))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" ∧
    ersetzeSAnw [captured] (.arm "Data" (some "x")
      (.ret (some (.call "captured" [.variable "x"])))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" := by cbv

/-- The normalization induction has a non-degenerate original qualified-name fixture. -/
theorem source_meaning_normalized_zeuge :
    let D := declaration [] (.int 0 10)
    let source := SExpr.bin "+" (.variable "module::K") (.lit 1)
    ∃ normalized : Normalized (D := D) (Γ := []) [] [("module::K", 5)] source,
      normalize [] [("module::K", 5)] source = .ok normalized ∧
      Scalar.expression [] (normalizeNames ([] : Locals []) [("module::K", 5)] source) =
        .ok normalized.code ∧ normalized.code.1 = .int 6 6 := by
  dsimp only
  let normalized := (normalize (D := declaration [] (.int 0 10)) (Γ := []) [] [("module::K", 5)]
    (.bin "+" (.variable "module::K") (.lit 1))).toOption.get (by decide +kernel)
  exact ⟨normalized, by rfl, normalized.meaning.normalized, by rfl⟩

theorem integer_argument_normalized_denotation_zeuge :
    ∃ argument : IntegerArgument [] [("module::K", 5)] 0 10
        (.bin "+" (.variable "module::K") (.lit 1)) 6,
      ∀ before after,
        uKonstWert 0 10 [] [] 64
          (normalizeNames ([] : Locals []) [("module::K", 5)]
            (.bin "+" (.variable "module::K") (.lit 1))) =
          some (eval before argument.code.expr after .nil).n := by
  let normalized := (normalize (D := declaration [] (.int 0 10)) (Γ := []) [] [("module::K", 5)]
    (.bin "+" (.variable "module::K") (.lit 1))).toOption.get (by decide +kernel)
  let argument : IntegerArgument [] [("module::K", 5)] 0 10
      (.bin "+" (.variable "module::K") (.lit 1)) 6 :=
    ⟨normalized, 6, 6, Code.add (Code.literal 5) (Code.literal 1), by rfl, by rfl, by rfl⟩
  exact ⟨argument, argument.normalized_denotation⟩

/-- The common replacement theorem has success, exact value and soundness jointly. -/
theorem replacement_sound_zeuge :
    ∃ replacement : Replacement optional [optional] [] [.lit 3],
      checkReplacement optional [optional] [] [.lit 3] = .ok replacement ∧
      replacement.syntax = .call "Some" [.lit 3] ∧ replacement.evidence.Sound := by
  have checked : ∃ replacement : Replacement optional [optional] [] [.lit 3],
      checkReplacement optional [optional] [] [.lit 3] = .ok replacement ∧
        replacement.syntax = .call "Some" [.lit 3] := by
    refine ⟨?replacement, ?success, ?literal⟩
    case success => cbv <;> exact Eq.refl _
    case literal => cbv
  obtain ⟨replacement, success, literal⟩ := checked
  exact ⟨replacement, success, literal, replacement.sound⟩

/-- The production theorem derives the certificate from actual substitution success. -/
theorem substitution_certified_zeuge :
    ∃ checked : Replacement optional [optional] [] [.lit 3],
      checkReplacement optional [optional] [] [.lit 3] = .ok checked ∧
      SExpr.call "Some" [.lit 3] = checked.syntax ∧ checked.evidence.Sound := by
  exact ersetzeSExpr_call_certified [] [optional] "optional" [.lit 3] [.lit 3]
    optional (.call "Some" [.lit 3]) (by cbv) (by cbv) (by cbv)

/-- Generic quotation is instantiated with a complete noninteger G value. -/
theorem reify_denotes_zeuge :
    let D := declaration [] .bool
    ∃ literal : Reified D [] [] .bool true,
      reify [] [] 64 .bool true = .ok literal ∧ literal.syntax = .tru ∧
      ∀ before after, eval before literal.expr after .nil = true := by
  dsimp only
  let literal := (reify (D := declaration [] .bool) (Γ := []) [] [] 64 .bool true).toOption.get (by decide +kernel)
  exact ⟨literal, by rfl, by rfl, fun before after => reify_denotes literal before after .nil⟩

theorem source_function_normalized_zeuge :
    ∃ fn : Scalar.SourceFunction captured 0 20,
      Scalar.elaborate captured = .ok ⟨0, 20, fn⟩ ∧
      Scalar.expression (locals captured.params)
        (normalizeNames (locals captured.params) captured.constants fn.source) =
          .ok ⟨_, fn.model.body.2.2⟩ := by
  have checked : ∃ fn : Scalar.SourceFunction captured 0 20,
      Scalar.elaborate captured = .ok ⟨0, 20, fn⟩ := by
    refine ⟨?fn, ?success⟩
    case success => cbv <;> exact Eq.refl _
  obtain ⟨fn, success⟩ := checked
  exact ⟨fn, success, fn.normalized⟩

end Gabbro.Grammatik.Parser.Konst.Values.Witness
