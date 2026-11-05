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

private def postFalseInput : UKonstFn :=
  { positive with signature := { positive.signature with klauseln := [.gives .fls] } }

private def preFalseInput : UKonstFn :=
  { positive with signature := { positive.signature with klauseln := [.needs .fls] } }

private def postFalseSource : Values.SourceFunction postFalseInput := by
  refine {
    source := (.bin ">" (.variable "x") (.lit 0))
    sourceBody := rfl
    model := ⟨?preCode, positiveSource.model.body, ?postCode⟩
    bodySource := positiveSource.bodySource
    preSource := ?preEq
    postSource := ?postEq }
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private def preFalseSource : Values.SourceFunction preFalseInput := by
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
    change Values.expression (D := declaration [.int 0 10] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
      (locals [("x", .int 0 10)]) [] [{
         name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.call "Data" [.bin "+" (.variable "x") (.lit 1)]) = .ok _
    cbv <;> exact Eq.refl _
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
    change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
      (locals []) [] [{
         name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.variable "Empty") = .ok _
    cbv <;> exact Eq.refl _
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
    change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
      (locals []) [] [{
         name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.call "Flag" [.tru]) = .ok _
    cbv <;> exact Eq.refl _
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
    change Values.expression (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)]))
      (locals []) [] [{
         name := "Choice"
         cases := [("Empty", none), ("Data", some (.int 0 255)),
           ("Flag", some .bool), ("Text", some (.str 1))] }] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) (.call "Text" [.ext .text ["Z"] []]) = .ok _
    cbv <;> exact Eq.refl _
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

private abbrev QuotationResult {D : Deklaration} {Γ : Ctx} (schemas : List USum)
    (texts : List String) (fuel : Nat) (τ : Ty) (value : Wert D τ) (expected : SExpr) : Prop :=
  ∃ literal : Values.Reified D Γ schemas τ value,
    Values.reify schemas texts fuel τ value = .ok literal ∧ literal.syntax = expected

private theorem quotation_text {D : Deklaration} {Γ : Ctx} {schemas : List USum}
    {fuel n : Nat} {bytes : List (Zahl 0 255)} (text : String)
    (bound : bytes.length ≤ n) (small : n ≤ 1)
    (decoded : UebersetzeAllg.bytesZahl
      (text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) = some bytes) :
    QuotationResult (D := D) (Γ := Γ) schemas [text] (fuel + 1) (.str n)
      ⟨bytes, bound⟩ (.ext .text [text] []) := by
  have found : Values.findText bytes [text] = .ok ⟨text, decoded⟩ := by
    unfold Values.findText
    split
    · rename_i missing
      cases missing.symm.trans decoded
    · rename_i actual selected
      have same : actual = bytes := Option.some.inj (selected.symm.trans decoded)
      subst actual
      split
      · rfl
      · rename_i different
        exact False.elim (different rfl)
  refine ⟨{
    «syntax» := .ext .text [text] []
    expr := .strLit bytes bound
    source := .text text bytes decoded bound
    equation := by intros; rfl }, ?_, rfl⟩
  erw [Values.reify.eq_def]
  dsimp only
  have narrow : ¬ n > 1 := by omega
  simp only [narrow, ↓reduceIte, found, bind, Except.bind, pure, Except.pure]

private theorem payload_syntax {D : Deklaration} {Γ : Ctx} {schemas : List USum}
    {texts : List String} {fuel : Nat} {τ : Ty} {value : Wert D τ} {expected : SExpr}
    (quoted : QuotationResult (D := D) (Γ := Γ) schemas texts fuel τ value expected) :
    (Values.reifyPayload (D := D) (Γ := Γ) schemas texts (fuel + 1) (some τ) value).map
      (fun payload => payload.syntax) = .ok (some expected) := by
  obtain ⟨literal, produced, spelling⟩ := quoted
  simp only [Values.reifyPayload, produced, bind, Except.bind, pure, Except.pure,
    Except.map, spelling]

private theorem quotation_tag {D : Deklaration} {Γ : Ctx} {schemas : List USum}
    {texts : List String} {fuel : Nat} {cases : List (Option Ty)} (schema : USum)
    {i : Fin cases.length} {value : Fall D.Fn D.passt cases i} (name : String)
    (payloadSource : Option SExpr)
    (selected : schemas.find? (fun actual => actual.spec = cases) = some schema)
    (shape : schema.spec = cases)
    (named : (schema.cases[i.val]?).map Prod.fst = some name)
    (payload : (Values.reifyPayload (D := D) (Γ := Γ) schemas texts fuel (cases.get i)
      (Fall.toNutzlast D.Fn D.passt cases i value)).map
        (fun actual => actual.syntax) = .ok payloadSource) :
    QuotationResult (D := D) (Γ := Γ) schemas texts (fuel + 1) (.sum cases)
      ⟨i, value⟩ (Values.tagSyntax name payloadSource) := by
  cases produced : Values.reifyPayload (D := D) (Γ := Γ) schemas texts fuel (cases.get i)
      (Fall.toNutzlast D.Fn D.passt cases i value) with
  | error error =>
    have impossible : (Except.error error : Except String (Option SExpr)) = .ok payloadSource := by
      simpa only [produced, Except.map] using payload
    cases impossible
  | ok actual =>
    have spelling : actual.syntax = payloadSource := Except.ok.inj
      (by simpa only [produced, Except.map] using payload)
    refine ⟨{
      «syntax» := Values.tagSyntax name actual.syntax
      expr := .case cases i actual.expr
      source := by simpa only [Fall.of_to] using
        (Values.LiteralMeaning.tag schema (List.mem_of_find?_eq_some selected) shape i name named
          actual.syntax _ actual.source)
      equation := by intros; simp only [eval, actual.equation, Fall.of_to] <;> rfl }, ?_, ?_⟩
    · erw [Values.reify.eq_def]
      dsimp only
      split
      · rename_i missing
        cases missing.symm.trans selected
      · rename_i actualSchema found
        have same : actualSchema = schema := Option.some.inj (found.symm.trans selected)
        subst actualSchema
        split
        · split
          · rename_i missing
            cases missing.symm.trans named
          · rename_i actualName found
            have same : actualName = name := Option.some.inj (found.symm.trans named)
            subst actualName
            simp only [produced, bind, Except.bind, pure, Except.pure] <;> rfl
        · rename_i different
          exact False.elim (different shape)
    · exact congrArg (Values.tagSyntax name) spelling

-- Normalize the Reified index and producer input together, realizing the
-- certified body value before introducing its complete quotation packet.
private theorem taggedQuotation :
    QuotationResult (D := declaration (tagged.params.map Prod.snd) tagged.erg)
      (Γ := tagged.params.map Prod.snd) (Values.resultSchemas tagged) [] 64 tagged.erg
      (taggedSource.model.body.denote (.cons (⟨4, by decide, by decide⟩ : Zahl 0 10) .nil)) (.call "Data" [.lit 5]) := by
  change QuotationResult (D := declaration [.int 0 10] (.sum [none, some (.int 0 255), some .bool, some (.str 1)])) (Γ := [.int 0 10])
    [{
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] }] [] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) ⟨⟨1, by decide⟩, (⟨5, by decide, by decide⟩ : Zahl 0 255)⟩ (.call "Data" [.lit 5])
  refine quotation_tag {
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] } "Data" (some (.lit 5)) (by cbv) (by rfl) (by cbv) ?_
  cbv <;> exact Eq.refl _

private theorem emptyTagQuotation :
    QuotationResult (D := declaration (emptyTag.params.map Prod.snd) emptyTag.erg)
      (Γ := emptyTag.params.map Prod.snd) (Values.resultSchemas emptyTag) [] 64 emptyTag.erg
      (emptyTagSource.model.body.denote .nil) (.variable "Empty") := by
  change QuotationResult (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)])) (Γ := [])
    [{
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] }] [] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) ⟨⟨0, by decide⟩, ()⟩ (.variable "Empty")
  refine quotation_tag {
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] } "Empty" none (by cbv) (by rfl) (by cbv) ?_
  cbv <;> exact Eq.refl _

private theorem flagTagQuotation :
    QuotationResult (D := declaration (flagTag.params.map Prod.snd) flagTag.erg)
      (Γ := flagTag.params.map Prod.snd) (Values.resultSchemas flagTag) [] 64 flagTag.erg
      (flagTagSource.model.body.denote .nil) (.call "Flag" [.tru]) := by
  change QuotationResult (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)])) (Γ := [])
    [{
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] }] [] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) ⟨⟨2, by decide⟩, true⟩ (.call "Flag" [.tru])
  refine quotation_tag {
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] } "Flag" (some .tru) (by cbv) (by rfl) (by cbv) ?_
  cbv <;> exact Eq.refl _

private theorem textTagQuotation :
    QuotationResult (D := declaration (textTag.params.map Prod.snd) textTag.erg)
      (Γ := textTag.params.map Prod.snd) (Values.resultSchemas textTag) ["Z"] 64 textTag.erg
      (textTagSource.model.body.denote .nil) (.call "Text" [.ext .text ["Z"] []]) := by
  change QuotationResult (D := declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)])) (Γ := [])
    [{
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] }] ["Z"] 64 (.sum [none, some (.int 0 255), some .bool, some (.str 1)]) ⟨⟨3, by decide⟩, (⟨[⟨90, by decide, by decide⟩], by decide⟩ : Wert (declaration [] (.sum [none, some (.int 0 255), some .bool, some (.str 1)])) (.str 1))⟩ (.call "Text" [.ext .text ["Z"] []])
  refine quotation_tag {
      name := "Choice"
      cases := [("Empty", none), ("Data", some (.int 0 255)), ("Flag", some .bool), ("Text", some (.str 1))] } "Text" (some (.ext .text ["Z"] [])) (by cbv) (by rfl) (by cbv) ?_
  apply payload_syntax
  exact quotation_text "Z" (by decide) (by decide) (by cbv)

private theorem emptyTextQuotation :
    QuotationResult (D := declaration ((shortText "").params.map Prod.snd) (shortText "").erg)
      (Γ := (shortText "").params.map Prod.snd) (Values.resultSchemas (shortText "")) [""] 64 (shortText "").erg
      (emptyTextSource.model.body.denote .nil) (.ext .text [""] []) := by
  change QuotationResult (D := declaration [] (.str 1)) (Γ := [])
    [] [""] 64 (.str 1) ⟨[], by decide⟩ (.ext .text [""] [])
  exact quotation_text "" (by decide) (by decide) (by cbv)

private theorem oneTextQuotation :
    QuotationResult (D := declaration ((shortText "A").params.map Prod.snd) (shortText "A").erg)
      (Γ := (shortText "A").params.map Prod.snd) (Values.resultSchemas (shortText "A")) ["A"] 64 (shortText "A").erg
      (oneTextSource.model.body.denote .nil) (.ext .text ["A"] []) := by
  change QuotationResult (D := declaration [] (.str 1)) (Γ := [])
    [] ["A"] 64 (.str 1) ⟨[⟨65, by decide, by decide⟩], by decide⟩ (.ext .text ["A"] [])
  exact quotation_text "A" (by decide) (by decide) (by cbv)

private theorem zeroTextQuotation :
    QuotationResult (D := declaration ((shortText "" 0).params.map Prod.snd) (shortText "" 0).erg)
      (Γ := (shortText "" 0).params.map Prod.snd) (Values.resultSchemas (shortText "" 0)) [""] 64 (shortText "" 0).erg
      (zeroTextSource.model.body.denote .nil) (.ext .text [""] []) := by
  change QuotationResult (D := declaration [] (.str 0)) (Γ := [])
    [] [""] 64 (.str 0) ⟨[], by decide⟩ (.ext .text [""] [])
  exact quotation_text "" (by decide) (by decide) (by cbv)

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

section QuotationResults
attribute [local cbv_opaque] Values.reify

public theorem tag_results :
    ersetzeSExpr [tagged] (.call "tagged" [.lit 4]) = .ok (.call "Data" [.lit 5]) ∧
    ersetzeSExpr [emptyTag] (.call "tagged" []) = .ok (.variable "Empty") ∧
    ersetzeSExpr [flagTag] (.call "tagged" []) = .ok (.call "Flag" [.tru]) ∧
    ersetzeSExpr [textTag] (.call "tagged" []) = .ok (.call "Text" [.ext .text ["Z"] []]) := by
  refine ⟨?data, ?empty, ?flag, ?text⟩
  case data =>
    obtain ⟨literal, produced, spelling⟩ := taggedQuotation
    rw [substitute_portable [tagged] "tagged" [.lit 4] [.lit 4] tagged (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [tagged] [] [.lit 4] taggedSource (elaborate_certified taggedSource)]
    cbv
    erw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]
  case empty =>
    obtain ⟨literal, produced, spelling⟩ := emptyTagQuotation
    rw [substitute_portable [emptyTag] "tagged" [] [] emptyTag (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [emptyTag] [] [] emptyTagSource (elaborate_certified emptyTagSource)]
    cbv
    rw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]
  case flag =>
    obtain ⟨literal, produced, spelling⟩ := flagTagQuotation
    rw [substitute_portable [flagTag] "tagged" [] [] flagTag (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [flagTag] [] [] flagTagSource (elaborate_certified flagTagSource)]
    cbv
    rw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]
  case text =>
    obtain ⟨literal, produced, spelling⟩ := textTagQuotation
    rw [substitute_portable [textTag] "tagged" [] [] textTag (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [textTag] [] [] textTagSource (elaborate_certified textTagSource)]
    cbv
    rw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]

public theorem text_results :
    ersetzeSExpr [shortText ""] (.call "shortText" []) = .ok (.ext .text [""] []) ∧
    ersetzeSExpr [shortText "A"] (.call "shortText" []) = .ok (.ext .text ["A"] []) := by
  refine ⟨?empty, ?one⟩
  case empty =>
    obtain ⟨literal, produced, spelling⟩ := emptyTextQuotation
    rw [substitute_portable [(shortText "")] "shortText" [] [] (shortText "") (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [(shortText "")] [] [] emptyTextSource (elaborate_certified emptyTextSource)]
    cbv
    rw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]
  case one =>
    obtain ⟨literal, produced, spelling⟩ := oneTextQuotation
    rw [substitute_portable [(shortText "A")] "shortText" [] [] (shortText "A") (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
      checkCall_elaborated [(shortText "A")] [] [] oneTextSource (elaborate_certified oneTextSource)]
    cbv
    rw [produced]
    simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]

public theorem zero_text_result :
    ersetzeSExpr [shortText "" 0] (.call "shortText" []) = .ok (.ext .text [""] []) := by
  obtain ⟨literal, produced, spelling⟩ := zeroTextQuotation
  rw [substitute_portable [(shortText "" 0)] "shortText" [] [] (shortText "" 0) (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
    checkCall_elaborated [(shortText "" 0)] [] [] zeroTextSource (elaborate_certified zeroTextSource)]
  cbv
  rw [produced]
  simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]

end QuotationResults

public theorem post_refused_result :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }] (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: ensures failed" := by
  change ersetzeSExpr [postFalseInput] (.call "positive" [.lit 3]) = _
  rw [substitute_portable [postFalseInput] "positive" [.lit 3] [.lit 3] postFalseInput (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
    checkCall_elaborated [postFalseInput] [] [.lit 3] postFalseSource (elaborate_certified postFalseSource)]
  cbv

public theorem pre_refused_result :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.needs .fls] } }] (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: requires failed" := by
  change ersetzeSExpr [preFalseInput] (.call "positive" [.lit 3]) = _
  rw [substitute_portable [preFalseInput] "positive" [.lit 3] [.lit 3] preFalseInput (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
    checkCall_elaborated [preFalseInput] [] [.lit 3] preFalseSource (elaborate_certified preFalseSource)]
  cbv

end Gabbro.Grammatik.Parser.Konst.Values.Witness.Phases
