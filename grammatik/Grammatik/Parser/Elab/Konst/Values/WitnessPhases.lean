module
public import Grammatik.Parser.Elab.Konst.Values.WitnessData
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
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


namespace Gabbro.Grammatik.Parser.Konst.Values.Witness.Phases
open Uebersetze Scalar WitnessReaders
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Each packet retains the actual body and both contracts. Reader normalization
-- happens here, before the checker projects any Boolean denotation.

private def positiveSource : Values.SourceFunction positive := by
  refine {
    source := (.bin ">" (.variable "x") (.lit 0))
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [.int 0 10] .bool)
      (locals [("x", .int 0 10)]) [] [] 64 .bool (.bin ">" (.variable "x") (.lit 0)) = .ok _
    rw [reader_bool]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def postFalseSource : Values.SourceFunction
    { positive with signature := { positive.signature with klauseln := [.gives .fls] } } := by
  refine {
    source := (.bin ">" (.variable "x") (.lit 0))
    sourceBody := rfl
    model := ⟨?preCode, positiveSource.model.body, ?postCode⟩
    bodySource := positiveSource.bodySource
    preSource := ?preEq
    postSource := ?postEq }
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def preFalseSource : Values.SourceFunction
    { positive with signature := { positive.signature with klauseln := [.needs .fls] } } := by
  refine {
    source := (.bin ">" (.variable "x") (.lit 0))
    sourceBody := rfl
    model := ⟨?preCode, positiveSource.model.body, ?postCode⟩
    bodySource := positiveSource.bodySource
    preSource := ?preEq
    postSource := ?postEq }
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def taggedSource : Values.SourceFunction tagged := by
  refine {
    source := (.call "Data" [.bin "+" (.variable "x") (.lit 1)])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [.int 0 10] (.sum schema.spec))
      (locals [("x", .int 0 10)]) [] [schema] 64 (.sum schema.spec) (.call "Data" [.bin "+" (.variable "x") (.lit 1)]) = .ok _
    rw [reader_sum]
    cbv <;> dsimp only
    all_goals try simp only [reader_payload, reader_empty, reader_missing]
    all_goals cbv <;> dsimp only
    all_goals try simp only [reader_int, reader_bool, reader_text]
    all_goals cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def emptyTagSource : Values.SourceFunction emptyTag := by
  refine {
    source := (.variable "Empty")
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.sum schema.spec))
      (locals []) [] [schema] 64 (.sum schema.spec) (.variable "Empty") = .ok _
    rw [reader_sum]
    cbv <;> dsimp only
    all_goals try simp only [reader_payload, reader_empty, reader_missing]
    all_goals cbv <;> dsimp only
    all_goals try simp only [reader_int, reader_bool, reader_text]
    all_goals cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def flagTagSource : Values.SourceFunction flagTag := by
  refine {
    source := (.call "Flag" [.tru])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.sum schema.spec))
      (locals []) [] [schema] 64 (.sum schema.spec) (.call "Flag" [.tru]) = .ok _
    rw [reader_sum]
    cbv <;> dsimp only
    all_goals try simp only [reader_payload, reader_empty, reader_missing]
    all_goals cbv <;> dsimp only
    all_goals try simp only [reader_int, reader_bool, reader_text]
    all_goals cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def textTagSource : Values.SourceFunction textTag := by
  refine {
    source := (.call "Text" [.ext .text ["Z"] []])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.sum schema.spec))
      (locals []) [] [schema] 64 (.sum schema.spec) (.call "Text" [.ext .text ["Z"] []]) = .ok _
    rw [reader_sum]
    cbv <;> dsimp only
    all_goals try simp only [reader_payload, reader_empty, reader_missing]
    all_goals cbv <;> dsimp only
    all_goals try simp only [reader_int, reader_bool, reader_text]
    all_goals cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def emptyTextSource : Values.SourceFunction (shortText "") := by
  refine {
    source := (.ext .text [""] [])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.str 1))
      (locals []) [] [] 64 (.str 1) (.ext .text [""] []) = .ok _
    rw [reader_text]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def oneTextSource : Values.SourceFunction (shortText "A") := by
  refine {
    source := (.ext .text ["A"] [])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.str 1))
      (locals []) [] [] 64 (.str 1) (.ext .text ["A"] []) = .ok _
    rw [reader_text]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def zeroTextSource : Values.SourceFunction (shortText "" 0) := by
  refine {
    source := (.ext .text [""] [])
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Values.expression (D := declaration [] (.str 0))
      (locals []) [] [] 64 (.str 0) (.ext .text [""] []) = .ok _
    rw [reader_text]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private theorem wrongTypeSource :
    Values.elaborate { positive with rumpf := .block [] (some (.ret (some (.lit 1)))) } = .error "const value has a different declared type" := by
  cbv <;> dsimp only <;> simp only [reader_bool] <;> cbv

private theorem wrongPayloadSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) } = .error "const value has a different declared type" := by
  cbv <;> dsimp only <;> simp only [reader_sum] <;> cbv
  all_goals simp only [reader_payload]
  all_goals cbv <;> dsimp only
  all_goals simp only [reader_int]
  all_goals cbv

private theorem unknownTagSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) } = .error "const tagged constructor is unknown: Foreign" := by
  cbv <;> dsimp only <;> simp only [reader_sum] <;> cbv

private theorem longTextSource :
    Values.elaborate (shortText "é") = .error "const string literal exceeds its declared maximum" := by
  cbv <;> dsimp only <;> simp only [reader_text] <;> cbv

private theorem missingPayloadSource :
    Values.elaborate { emptyTag with rumpf := .block [] (some (.ret (some (.variable "Data")))) } = .error "const tagged constructor payload does not match its declared type" := by
  cbv <;> dsimp only <;> simp only [reader_sum] <;> cbv
  all_goals simp only [reader_missing]
  all_goals cbv

public theorem bool_results :
    ersetzeSExpr [positive] (.call "positive" [.lit 3]) = .ok .tru ∧
    ersetzeSExpr [positive] (.call "positive" [.lit 0]) = .ok .fls := by
  refine ⟨?positive, ?zero⟩
  case positive =>
    rw [substitute_portable [positive] "positive" [.lit 3] [.lit 3] positive
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [positive] [] [.lit 3] positiveSource
      (elaborate_certified positiveSource)]
    cbv
  case zero =>
    rw [substitute_portable [positive] "positive" [.lit 0] [.lit 0] positive
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [positive] [] [.lit 0] positiveSource
      (elaborate_certified positiveSource)]
    cbv

public theorem tag_results :
    ersetzeSExpr [tagged] (.call "tagged" [.lit 4]) = .ok (.call "Data" [.lit 5]) ∧
    ersetzeSExpr [emptyTag] (.call "tagged" []) = .ok (.variable "Empty") ∧
    ersetzeSExpr [flagTag] (.call "tagged" []) = .ok (.call "Flag" [.tru]) ∧
    ersetzeSExpr [textTag] (.call "tagged" []) = .ok (.call "Text" [.ext .text ["Z"] []]) := by
  refine ⟨?data, ?empty, ?flag, ?text⟩
  case data =>
    rw [substitute_portable [tagged] "tagged" [.lit 4] [.lit 4] tagged
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [tagged] [] [.lit 4] taggedSource
      (elaborate_certified taggedSource)]
    cbv
  case empty =>
    rw [substitute_portable [emptyTag] "tagged" [] [] emptyTag
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [emptyTag] [] [] emptyTagSource
      (elaborate_certified emptyTagSource)]
    cbv
  case flag =>
    rw [substitute_portable [flagTag] "tagged" [] [] flagTag
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [flagTag] [] [] flagTagSource
      (elaborate_certified flagTagSource)]
    cbv
  case text =>
    rw [substitute_portable [textTag] "tagged" [] [] textTag
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [textTag] [] [] textTagSource
      (elaborate_certified textTagSource)]
    cbv

public theorem text_results :
    ersetzeSExpr [shortText ""] (.call "shortText" []) = .ok (.ext .text [""] []) ∧
    ersetzeSExpr [shortText "A"] (.call "shortText" []) = .ok (.ext .text ["A"] []) := by
  refine ⟨?empty, ?one⟩
  case empty =>
    rw [substitute_portable [(shortText "")] "shortText" [] [] (shortText "")
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [(shortText "")] [] [] emptyTextSource
      (elaborate_certified emptyTextSource)]
    cbv
  case one =>
    rw [substitute_portable [(shortText "A")] "shortText" [] [] (shortText "A")
      (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
    rw [checkCall_elaborated [(shortText "A")] [] [] oneTextSource
      (elaborate_certified oneTextSource)]
    cbv

public theorem zero_text_result :
    ersetzeSExpr [shortText "" 0] (.call "shortText" []) = .ok (.ext .text [""] []) := by
  rw [substitute_portable [(shortText "" 0)] "shortText" [] [] (shortText "" 0)
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_elaborated [(shortText "" 0)] [] [] zeroTextSource
    (elaborate_certified zeroTextSource)]
  cbv

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

public theorem post_refused_result :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }] (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: ensures failed" := by
  rw [substitute_portable [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }] "positive" [.lit 3] [.lit 3] { positive with signature := { positive.signature with klauseln := [.gives .fls] } }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_elaborated [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }] [] [.lit 3] postFalseSource
    (elaborate_certified postFalseSource)]
  cbv

public theorem pre_refused_result :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.needs .fls] } }] (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: requires failed" := by
  rw [substitute_portable [{ positive with signature := { positive.signature with klauseln := [.needs .fls] } }] "positive" [.lit 3] [.lit 3] { positive with signature := { positive.signature with klauseln := [.needs .fls] } }
    (by cbv) (by cbv) (by rfl) (by cbv) (by cbv)]
  rw [checkCall_elaborated [{ positive with signature := { positive.signature with klauseln := [.needs .fls] } }] [] [.lit 3] preFalseSource
    (elaborate_certified preFalseSource)]
  cbv

end Gabbro.Grammatik.Parser.Konst.Values.Witness.Phases
