module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.NamedSources
import all Stage0.Frontend.Witnesses.Constants.NamedSources
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
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
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- These are the existing generic typed reader equations used by the green const witnesses.
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
attribute [local cbv_eval] Konst.Values.reifyPayload.eq_def
attribute [local cbv_eval]
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

-- Select a used field of the actual fuel record instead of expanding its unused operations.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit Frontend.normalize
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct
  uKonstZeile.eq_def uKonstZeilen.eq_def lowLit.eq_def

attribute [local cbv_eval] tagText_metadata stringText_metadata

section tagCompilation
attribute [local cbv_eval] tag_collected tag_elaborated
attribute [local cbv_opaque] Konst.Values.elaborate Konst.Values.reify

-- Replay the actual const call before the unit elaborator consumes its syntax.
-- The whole quotation retains its canonical value, schema and payload evidence.
@[local cbv_eval] private theorem tagText_replaced :
    Konst.ersetzeSExprIn [] [tagDescriptor] (.call "selected" [.lit 4]) =
      .ok (.call "Data" [.lit 5]) := by
  change Konst.ersetzeSExpr [tagDescriptor] (.call "selected" [.lit 4]) =
    .ok (.call "Data" [.lit 5])
  obtain ⟨literal, produced, spelling⟩ := tag_quoted
  rw [Konst.Values.WitnessReaders.substitute_portable [tagDescriptor] "selected"
    [.lit 4] [.lit 4] tagDescriptor (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
    Konst.Values.WitnessReaders.checkCall_elaborated [tagDescriptor] [] [.lit 4]
      tagFunction tag_elaborated]
  cbv
  erw [produced]
  simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]

-- Normalize the actual source and all three supplied scope fields together,
-- before the Header introduces a candidate or any dependent code projection.
private def tagTextData :
    { actual : List SItemTief × List (String × Int) ×
        List (String × (Int × Int)) × List UKonstFn //
      (pre108 tagTextInput.prepared.elaborierbar, tagTextTail.derived.scope.values,
        tagTextTail.derived.scope.types, tagTextTail.derived.scope.functions) = actual } := by
  refine ⟨(?items, ?values, ?types, ?functions), ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def tagTextExpansion :
    { actual : List SItemTief × List (STyp × String) //
      Modules.prepare tagTextData.val.1 = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def tagTextElaboration :
    { actual : UProg //
      ((Frontend.elabWithScopes tagTextData.val.1 tagTextData.val.2.1
        tagTextData.val.2.2.1 tagTextData.val.2.2.2
        (Frontend.tableWithEmpty tagTextData.val.2.1 tagTextData.val.2.2.1)).bind
          (Profil.selectUnit {})) = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced =>
    unfold Frontend.elabWithScopes
    rw [show expandU tagTextData.val.1 = .ok tagTextExpansion.val from tagTextExpansion.property]
    dsimp only [bind, Except.bind]
    obtain ⟨literal, quoted, spelling⟩ := tag_quoted
    cbv <;> (
      try erw [tag_elaborated]
      cbv <;> first
        | (erw [quoted]
           simp only [spelling, bind, Except.bind, pure, Except.pure, Except.map] <;>
             cbv <;> exact Eq.refl _)
        | exact Eq.refl _)

private def tagTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.tagText where
  source := sourceFrom tagTextInput tagTextTail
  sourceEq := sourceFrom_eq tagTextInput tagTextTail
  expanded := tagTextExpansion.val.1
  requirements := tagTextExpansion.val.2
  expansion := (congrArg (fun data => Modules.prepare data.1) tagTextData.property).trans
    tagTextExpansion.property
  constants := by
    change Konst.checkSourceConstants tagTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact tagTextTail.metadata
    · rfl
  ordinary := by cbv
  metadata := tagTextTail.metadata
  candidate := tagTextElaboration.val
  elaborated := by
    have inputs := congrArg
      (fun data : List SItemTief × List (String × Int) ×
          List (String × (Int × Int)) × List UKonstFn =>
        (Frontend.elabWithScopes data.1 data.2.1 data.2.2.1 data.2.2.2
          (Frontend.tableWithEmpty data.2.1 data.2.2.1)).bind (Profil.selectUnit {}))
      tagTextData.property
    exact inputs.trans tagTextElaboration.property

private theorem tagText_count : tagTextHeader.unit.fns.length = 1 := by cbv

private def tagTextMain : Fin tagTextHeader.unit.fns.length :=
  ⟨0, by have count := tagText_count; omega⟩

private theorem tagText_only_main (f : Fin tagTextHeader.unit.fns.length) :
    f = tagTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [tagText_count] using f.isLt
  change f.val = 0
  omega

private def tagTextCode :
    { value : EnsTy tagTextHeader.unit tagTextMain × RumpTy tagTextHeader.unit tagTextMain ×
        ReqTy tagTextHeader.unit tagTextMain //
      lowerFnAt tagTextHeader.unit tagTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem tagText_code_eq :
    lowerFnAt tagTextHeader.unit tagTextMain = .ok tagTextCode.val := tagTextCode.property

private def tagTextFunctions : Functions tagTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := tagText_only_main f
    subst f
    rw [tagText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := tagText_only_main f
      subst f
      cbv) (by cbv)

-- Check the actual original declaration spine. Neither the tagged schema nor
-- either function is an array initializer; all const-function gates remain above.
private theorem tagText_arrays_ready :
    (Frontend.checkArrays tagTextHeader.unit tagTextHeader.source.scopes
      tagTextInput.original).toOption.isSome = true := by
  have nonConstants : tagTextInput.original.all
      (fun | .constT _ _ _ => false | _ => true) = true := by cbv
  apply checked_array_items
  intro item member
  have shape := List.all_eq_true.mp nonConstants item member
  cases item
  case constT name ty value =>
    change (false : Bool) = true at shape
    cases shape
  all_goals rfl

private theorem tagText_entry_free (f : Fin tagTextHeader.unit.fns.length) :
    (OldSource.clauses tagTextHeader.expanded (fnAt tagTextHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := tagText_only_main f
  subst f
  cbv

private theorem tagText_restored :
    OldSource.restore (pre108 tagTextHeader.source.prepared.elaborierbar)
      tagTextHeader.unit tagTextFunctions.program = .ok tagTextFunctions.program :=
  restore_entry_free _ tagTextHeader.expanded tagTextHeader.requirements
    tagTextHeader.unit tagTextFunctions.program tagTextHeader.expansion tagText_entry_free

private theorem tagText_accepted :
    OldSource.accepts tagTextHeader.unit tagTextFunctions.program = .ok true := by
  apply accepts_function_results tagTextFunctions
  intro invariants pointers foreigns
  cbv

private def tagTextBody : Body tagTextHeader where
  functions := tagTextFunctions
  main := tagTextMain
  entry := by cbv
  initializers := by cbv
  arrays := (Frontend.checkArrays tagTextHeader.unit tagTextHeader.source.scopes
    tagTextInput.original).toOption.get tagText_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get tagText_arrays_ready
  program := tagTextFunctions.program
  restored := tagText_restored
  accepted := tagText_accepted

private theorem tagText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.tagText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨tagTextHeader, tagText_count, ⟨tagTextBody⟩⟩

theorem tagText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.tagText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.tagText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := tagText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end tagCompilation

section textCompilation
attribute [local cbv_eval] text_collected text_elaborated
attribute [local cbv_opaque] Konst.Values.elaborate Konst.Values.reify

@[local cbv_eval] private theorem stringText_replaced :
    Konst.ersetzeSExprIn [] [textDescriptor] (.call "selected" []) =
      .ok (.ext .text ["A"] []) := by
  change Konst.ersetzeSExpr [textDescriptor] (.call "selected" []) =
    .ok (.ext .text ["A"] [])
  obtain ⟨literal, produced, spelling⟩ := text_quoted
  rw [Konst.Values.WitnessReaders.substitute_portable [textDescriptor] "selected"
    [] [] textDescriptor (by cbv) (by cbv) (by rfl) (by cbv) (by cbv),
    Konst.Values.WitnessReaders.checkCall_elaborated [textDescriptor] [] []
      textFunction text_elaborated]
  cbv
  erw [produced]
  simpa only [spelling, bind, Except.bind, pure, Except.pure, Except.map]

private def stringTextData :
    { actual : List SItemTief × List (String × Int) ×
        List (String × (Int × Int)) × List UKonstFn //
      (pre108 stringTextInput.prepared.elaborierbar, stringTextTail.derived.scope.values,
        stringTextTail.derived.scope.types, stringTextTail.derived.scope.functions) = actual } := by
  refine ⟨(?items, ?values, ?types, ?functions), ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def stringTextExpansion :
    { actual : List SItemTief × List (STyp × String) //
      Modules.prepare stringTextData.val.1 = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def stringTextElaboration :
    { actual : UProg //
      ((Frontend.elabWithScopes stringTextData.val.1 stringTextData.val.2.1
        stringTextData.val.2.2.1 stringTextData.val.2.2.2
        (Frontend.tableWithEmpty stringTextData.val.2.1 stringTextData.val.2.2.1)).bind
          (Profil.selectUnit {})) = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced =>
    unfold Frontend.elabWithScopes
    rw [show expandU stringTextData.val.1 = .ok stringTextExpansion.val from
      stringTextExpansion.property]
    dsimp only [bind, Except.bind]
    obtain ⟨literal, quoted, spelling⟩ := text_quoted
    cbv <;> (
      try erw [text_elaborated]
      cbv <;> first
        | (erw [quoted]
           simp only [spelling, bind, Except.bind, pure, Except.pure, Except.map] <;>
             cbv <;> exact Eq.refl _)
        | exact Eq.refl _)

private def stringTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.stringText where
  source := sourceFrom stringTextInput stringTextTail
  sourceEq := sourceFrom_eq stringTextInput stringTextTail
  expanded := stringTextExpansion.val.1
  requirements := stringTextExpansion.val.2
  expansion := (congrArg (fun data => Modules.prepare data.1) stringTextData.property).trans
    stringTextExpansion.property
  constants := by
    change Konst.checkSourceConstants stringTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact stringTextTail.metadata
    · rfl
  ordinary := by cbv
  metadata := stringTextTail.metadata
  candidate := stringTextElaboration.val
  elaborated := by
    have inputs := congrArg
      (fun data : List SItemTief × List (String × Int) ×
          List (String × (Int × Int)) × List UKonstFn =>
        (Frontend.elabWithScopes data.1 data.2.1 data.2.2.1 data.2.2.2
          (Frontend.tableWithEmpty data.2.1 data.2.2.1)).bind (Profil.selectUnit {}))
      stringTextData.property
    exact inputs.trans stringTextElaboration.property

private theorem stringText_count : stringTextHeader.unit.fns.length = 1 := by cbv

private def stringTextMain : Fin stringTextHeader.unit.fns.length :=
  ⟨0, by have count := stringText_count; omega⟩

private theorem stringText_only_main (f : Fin stringTextHeader.unit.fns.length) :
    f = stringTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [stringText_count] using f.isLt
  change f.val = 0
  omega

private def stringTextCode :
    { value : EnsTy stringTextHeader.unit stringTextMain × RumpTy stringTextHeader.unit stringTextMain ×
        ReqTy stringTextHeader.unit stringTextMain //
      lowerFnAt stringTextHeader.unit stringTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem stringText_code_eq :
    lowerFnAt stringTextHeader.unit stringTextMain = .ok stringTextCode.val := stringTextCode.property

private def stringTextFunctions : Functions stringTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := stringText_only_main f
    subst f
    rw [stringText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := stringText_only_main f
      subst f
      cbv) (by cbv)

private theorem stringText_arrays_ready :
    (Frontend.checkArrays stringTextHeader.unit stringTextHeader.source.scopes
      stringTextInput.original).toOption.isSome = true := by
  have nonConstants : stringTextInput.original.all
      (fun | .constT _ _ _ => false | _ => true) = true := by cbv
  apply checked_array_items
  intro item member
  have shape := List.all_eq_true.mp nonConstants item member
  cases item
  case constT name ty value =>
    change (false : Bool) = true at shape
    cases shape
  all_goals rfl

private theorem stringText_entry_free (f : Fin stringTextHeader.unit.fns.length) :
    (OldSource.clauses stringTextHeader.expanded (fnAt stringTextHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := stringText_only_main f
  subst f
  cbv

private theorem stringText_restored :
    OldSource.restore (pre108 stringTextHeader.source.prepared.elaborierbar)
      stringTextHeader.unit stringTextFunctions.program = .ok stringTextFunctions.program :=
  restore_entry_free _ stringTextHeader.expanded stringTextHeader.requirements
    stringTextHeader.unit stringTextFunctions.program stringTextHeader.expansion stringText_entry_free

private theorem stringText_accepted :
    OldSource.accepts stringTextHeader.unit stringTextFunctions.program = .ok true := by
  apply accepts_function_results stringTextFunctions
  intro invariants pointers foreigns
  cbv

private def stringTextBody : Body stringTextHeader where
  functions := stringTextFunctions
  main := stringTextMain
  entry := by cbv
  initializers := by cbv
  arrays := (Frontend.checkArrays stringTextHeader.unit stringTextHeader.source.scopes
    stringTextInput.original).toOption.get stringText_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get stringText_arrays_ready
  program := stringTextFunctions.program
  restored := stringText_restored
  accepted := stringText_accepted

private theorem stringText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.stringText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨stringTextHeader, stringText_count, ⟨stringTextBody⟩⟩

theorem stringText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.stringText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.stringText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := stringText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end textCompilation

end Gabbro.Stage0.Frontend.ConstPhases
