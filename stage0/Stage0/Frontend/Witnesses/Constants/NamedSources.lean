module
public import Stage0.Frontend.Witnesses.Constants.SourcePackets
public import Stage0.Frontend.Witnesses.Constants.Lexical
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import Init.Data.String.Lemmas.Intercalate
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
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

import all Stage0.Profil
import all Stage0.Frontend.AliasOrder
import all Stage0.Frontend.Correctness
import all Stage0.Frontend.Environments
import all Stage0.Frontend.EnvironmentsPart1
import all Stage0.Frontend.DependentScopes
import all Stage0.Frontend.DependentScopesa
import all Stage0.Frontend.Functions
import all Stage0.Frontend.Guard
import all Stage0.Frontend.Constants.ConstantScopes
import all Stage0.Frontend.Constants.ConstantMeaning

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- These are the existing generic typed reader equations used by the green const witnesses.
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
attribute [local cbv_eval] Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
attribute [local cbv_eval]
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

-- Keep the unused float target and the generic normalization proof symbolic.
attribute [local cbv_opaque] uFloatLimit Frontend.normalize
attribute [local cbv_eval] String.intercalate_singleton

/-- The canonical parser still supplies the public selected item list. -/
theorem tagText_parsed :
    (parseTopTief (tagTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def tagTextItems : List SItemTief :=
  (parseTopTief (tagTextScan.tokens ++ [.ende])).toOption.get tagText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def tagTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.tagText := by
  refine {
    tokens := tagTextScan.tokens ++ [.ende]
    items := ?items
    lexed := tagText_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

/-- The public getter receives the already proved whole profile result by exact-domain transport. -/
theorem tagText_prepared :
    (Profil.prepareItems {} tagTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected tagTextInput tagText_lexed
      (items := tagTextItems) (by exact Gabbro.Grammatik.except_ok_get tagText_parsed)
  rw [origin]
  rfl

private def tagDescriptor : UKonstFn := {
  name := "selected"
  params := [("x", .int 0 10)]
  erg := .sum [none, some (.int 0 255)]
  rumpf := .block [] (some (.ret (some (.call "Data" [.bin "+" (.variable "x") (.lit 1)]))))
  signature := {
    art := "const"
    name := "selected"
    params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
    res := some (.atom "Choice")
    fehler := none
    klauseln := []
    generics := [] }
  constants := []
  sums := [{ name := "Choice", cases := [("Empty", none), ("Data", some (.int 0 255))] }] }

private theorem tag_collected :
    Konst.collectFunctions tagTextInput.original = .ok [tagDescriptor] := by
  cbv <;> rfl

private def tagFunction : Konst.Values.SourceFunction tagDescriptor := by
  refine {
    source := .call "Data" [.bin "+" (.variable "x") (.lit 1)]
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Konst.Values.expression
      (D := Konst.Scalar.declaration [.int 0 10] (.sum [none, some (.int 0 255)]))
      (Konst.Scalar.locals [("x", .int 0 10)]) []
      [{ name := "Choice", cases := [("Empty", none), ("Data", some (.int 0 255))] }]
      64 (.sum [none, some (.int 0 255)])
      (.call "Data" [.bin "+" (.variable "x") (.lit 1)]) = .ok _
    rw [Konst.Values.WitnessReaders.reader_sum]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private theorem tag_elaborated : Konst.Values.elaborate tagDescriptor = .ok tagFunction :=
  Konst.Values.WitnessReaders.elaborate_certified tagFunction

attribute [local cbv_eval] tag_elaborated

-- Realize the certified function value before introducing the dependent
-- quotation result. The payload still comes from the canonical reify producer.
private theorem tag_quoted :
    ∃ literal : Konst.Values.Reified
        (Konst.Scalar.declaration (tagDescriptor.params.map Prod.snd) tagDescriptor.erg)
        (tagDescriptor.params.map Prod.snd) (Konst.Values.resultSchemas tagDescriptor)
        tagDescriptor.erg
        (tagFunction.model.body.denote (.cons (⟨4, by decide, by decide⟩ : Zahl 0 10) .nil)),
      Konst.Values.reify (Konst.Values.resultSchemas tagDescriptor) [] 64 tagDescriptor.erg
        (tagFunction.model.body.denote (.cons (⟨4, by decide, by decide⟩ : Zahl 0 10) .nil)) =
          .ok literal ∧ literal.syntax = .call "Data" [.lit 5] := by
  let schema : USum := {
    name := "Choice"
    cases := [("Empty", none), ("Data", some (.int 0 255))] }
  let caseTypes := [none, some (Ty.int 0 255)]
  let D := Konst.Scalar.declaration [.int 0 10] (.sum caseTypes)
  let i : Fin caseTypes.length := ⟨1, by decide⟩
  let value : Zahl 0 255 := ⟨5, by decide, by decide⟩
  change ∃ literal : Konst.Values.Reified D [.int 0 10] [schema] (.sum caseTypes) ⟨i, value⟩,
    Konst.Values.reify [schema] [] 64 (.sum caseTypes) ⟨i, value⟩ = .ok literal ∧
      literal.syntax = .call "Data" [.lit 5]
  have payload : ∃ literal : Konst.Values.ReifiedPayload D [.int 0 10] [schema]
      (some (.int 0 255)) value,
      Konst.Values.reifyPayload [schema] [] 63 (some (.int 0 255)) value = .ok literal ∧
        literal.syntax = some (.lit 5) := by
    refine ⟨?_, ?_, ?_⟩
    · cbv <;> rfl
    · rfl
  obtain ⟨payload, produced, spelling⟩ := payload
  have selected : [schema].find? (fun actual => actual.spec = caseTypes) = some schema := by cbv
  have named : (schema.cases[i.val]?).map Prod.fst = some "Data" := rfl
  refine ⟨{
    «syntax» := Konst.Values.tagSyntax "Data" payload.syntax
    expr := .case caseTypes i payload.expr
    source := Konst.Values.LiteralMeaning.tag schema (by simp) rfl i "Data" named
      payload.syntax value payload.source
    equation := by intros; simp only [eval, payload.equation] <;> rfl }, ?_, ?_⟩
  · erw [Konst.Values.reify.eq_def]
    dsimp only
    split
    · rename_i missing
      cases missing.symm.trans selected
    · rename_i actual found
      have same : actual = schema := Option.some.inj (found.symm.trans selected)
      subst actual
      split
      · split
        · rename_i missing
          cases missing.symm.trans named
        · rename_i actualName found
          have same : actualName = "Data" := Option.some.inj (found.symm.trans named)
          subst actualName
          simp only [produced, bind, Except.bind, pure, Except.pure] <;> rfl
      · rename_i different
        exact False.elim (different rfl)
  · exact congrArg (Konst.Values.tagSyntax "Data") spelling

section
attribute [local cbv_opaque] Konst.Values.elaborate Konst.Values.reify

private theorem tag_metadata :
    Konst.checkSourceMetadata tagTextInput.original = .ok () := by
  obtain ⟨literal, quoted, spelling⟩ := tag_quoted
  unfold Konst.checkSourceMetadata Konst.konstErsetzePipeline
  rw [tag_collected]
  cbv <;> (erw [tag_elaborated]; cbv)
  erw [quoted]
  simp only [spelling, bind, Except.bind, pure, Except.pure, Except.map] <;> cbv

end

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def tagTextTail : SourceTail tagTextInput := by
  refine {
    metadata := by exact tag_metadata
    order := ?order
    ordered := ?ordered
    derived := ?derived
    elaborated := ?elaborated
    aliases := ?aliases
    constants := ?constants }
  case ordered => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case aliases => cbv
  case constants => cbv

theorem tagText_metadata :
    Konst.checkSourceMetadata tagTextInput.original = .ok () := tagTextTail.metadata

theorem tagText_ordered :
    (Frontend.orderAliases tagTextInput.original).toOption.isSome = true := by
  rw [tagTextTail.ordered]
  rfl

theorem tagText_scopes :
    (Frontend.elaborateConstantScopes tagTextInput.original).toOption.isSome = true := by
  rw [tagTextTail.elaborated]
  rfl

/-- The canonical parser still supplies the public selected item list. -/
theorem stringText_parsed :
    (parseTopTief (stringTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def stringTextItems : List SItemTief :=
  (parseTopTief (stringTextScan.tokens ++ [.ende])).toOption.get stringText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def stringTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.stringText := by
  refine {
    tokens := stringTextScan.tokens ++ [.ende]
    items := ?items
    lexed := stringText_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

/-- The public getter receives the already proved whole profile result by exact-domain transport. -/
theorem stringText_prepared :
    (Profil.prepareItems {} stringTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected stringTextInput stringText_lexed
      (items := stringTextItems) (by exact Gabbro.Grammatik.except_ok_get stringText_parsed)
  rw [origin]
  rfl

private def textDescriptor : UKonstFn := {
  name := "selected"
  params := []
  erg := .str 1
  rumpf := .block [] (some (.ret (some (.ext .text ["A"] []))))
  signature := {
    art := "const"
    name := "selected"
    params := []
    res := some (.str (.lit 1))
    fehler := none
    klauseln := []
    generics := [] }
  constants := []
  sums := [] }

private theorem text_collected :
    Konst.collectFunctions stringTextInput.original = .ok [textDescriptor] := by
  cbv <;> rfl

private def textFunction : Konst.Values.SourceFunction textDescriptor := by
  refine {
    source := .ext .text ["A"] []
    sourceBody := rfl
    model := ⟨?preCode, ?bodyCode, ?postCode⟩
    bodySource := ?bodyEq
    preSource := ?preEq
    postSource := ?postEq }
  case bodyEq =>
    change Konst.Values.expression (D := Konst.Scalar.declaration [] (.str 1))
      (Konst.Scalar.locals []) [] [] 64 (.str 1) (.ext .text ["A"] []) = .ok _
    rw [Konst.Values.WitnessReaders.reader_text]
    cbv <;> rfl
  case preEq => cbv <;> rfl
  case postEq => cbv <;> rfl

private theorem text_elaborated : Konst.Values.elaborate textDescriptor = .ok textFunction :=
  Konst.Values.WitnessReaders.elaborate_certified textFunction

attribute [local cbv_eval] text_elaborated

-- Keep the exact UTF-8 decoding equation together with the typed body value;
-- no string spelling is inferred from an unchecked numeric result.
private theorem text_quoted :
    ∃ literal : Konst.Values.Reified
        (Konst.Scalar.declaration (textDescriptor.params.map Prod.snd) textDescriptor.erg)
        (textDescriptor.params.map Prod.snd) (Konst.Values.resultSchemas textDescriptor)
        textDescriptor.erg (textFunction.model.body.denote .nil),
      Konst.Values.reify (Konst.Values.resultSchemas textDescriptor) ["A"] 64 textDescriptor.erg
        (textFunction.model.body.denote .nil) = .ok literal ∧
          literal.syntax = .ext .text ["A"] [] := by
  let D := Konst.Scalar.declaration [] (.str 1)
  let value : Wert D (.str 1) := textFunction.model.body.denote .nil
  change ∃ literal : Konst.Values.Reified D [] [] (.str 1) value,
    Konst.Values.reify [] ["A"] 64 (.str 1) value = .ok literal ∧
      literal.syntax = .ext .text ["A"] []
  have decoded : bytesZahl ("A".toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)) =
      some value.val := by cbv
  have found : Konst.Values.findText value.val ["A"] = .ok ⟨"A", decoded⟩ := by
    unfold Konst.Values.findText
    split
    · rename_i missing
      cases missing.symm.trans decoded
    · rename_i actual selected
      have same : actual = value.val := Option.some.inj (selected.symm.trans decoded)
      subst actual
      split
      · rfl
      · rename_i different
        exact False.elim (different rfl)
  refine ⟨{
    «syntax» := .ext .text ["A"] []
    expr := .strLit value.val value.property
    source := .text "A" value.val decoded value.property
    equation := by intros; rfl }, ?_, rfl⟩
  erw [Konst.Values.reify.eq_def]
  dsimp only
  simp only [show ¬ (1 : Nat) > 1 by decide, ↓reduceIte, found,
    bind, Except.bind, pure, Except.pure]

section
attribute [local cbv_opaque] Konst.Values.elaborate Konst.Values.reify

private theorem text_metadata :
    Konst.checkSourceMetadata stringTextInput.original = .ok () := by
  obtain ⟨literal, quoted, spelling⟩ := text_quoted
  unfold Konst.checkSourceMetadata Konst.konstErsetzePipeline
  rw [text_collected]
  cbv <;> (erw [text_elaborated]; cbv)
  erw [quoted]
  simp only [spelling, bind, Except.bind, pure, Except.pure, Except.map] <;> cbv

end

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def stringTextTail : SourceTail stringTextInput := by
  refine {
    metadata := by exact text_metadata
    order := ?order
    ordered := ?ordered
    derived := ?derived
    elaborated := ?elaborated
    aliases := ?aliases
    constants := ?constants }
  case ordered => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case aliases => cbv
  case constants => cbv

theorem stringText_metadata :
    Konst.checkSourceMetadata stringTextInput.original = .ok () := stringTextTail.metadata

theorem stringText_ordered :
    (Frontend.orderAliases stringTextInput.original).toOption.isSome = true := by
  rw [stringTextTail.ordered]
  rfl

theorem stringText_scopes :
    (Frontend.elaborateConstantScopes stringTextInput.original).toOption.isSome = true := by
  rw [stringTextTail.elaborated]
  rfl

end Gabbro.Stage0.Frontend.ConstPhases
