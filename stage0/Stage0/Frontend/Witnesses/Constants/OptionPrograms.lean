module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.OptionSources
import all Stage0.Frontend.Witnesses.Constants.OptionSources
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
attribute [local cbv_eval] Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
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

-- Replay the actual source gates instead of recomputing their metadata models.
attribute [local cbv_eval] boolText_metadata optionText_metadata noneText_metadata

-- Reuse the green source owner's complete model certificate. Its private
-- helpers are accessed only by this private proof slice, never by a new
-- source witness or an alternative elaborator.
section boolCompilation
attribute [local cbv_eval] bool_reader_fuel bool_adapt bool_quote_fuel
attribute [local cbv_eval] positive_collected positive_elaborated
attribute [local cbv_opaque] Konst.Values.elaborate

-- Retain the canonical Header before any dependent function projection.
private def boolTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.boolText := by
  refine {
    source := sourceFrom boolTextInput boolTextTail
    sourceEq := sourceFrom_eq boolTextInput boolTextTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by cbv
    metadata := boolTextTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants boolTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact boolTextTail.metadata
    · rfl
  case elaborated =>
    cbv <;> first
      | exact Eq.refl _
      | (erw [positive_elaborated]; cbv <;> exact Eq.refl _)

private theorem boolText_count : boolTextHeader.unit.fns.length = 1 := by cbv

private def boolTextMain : Fin boolTextHeader.unit.fns.length :=
  ⟨0, by have count := boolText_count; omega⟩

private theorem boolText_only_main (f : Fin boolTextHeader.unit.fns.length) :
    f = boolTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [boolText_count] using f.isLt
  change f.val = 0
  omega

-- The actual complete lowering result is fixed before of_success selects it.
private def boolTextCode :
    { value : EnsTy boolTextHeader.unit boolTextMain × RumpTy boolTextHeader.unit boolTextMain ×
        ReqTy boolTextHeader.unit boolTextMain //
      lowerFnAt boolTextHeader.unit boolTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem boolText_code_eq :
    lowerFnAt boolTextHeader.unit boolTextMain = .ok boolTextCode.val := boolTextCode.property

private def boolTextFunctions : Functions boolTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := boolText_only_main f
    subst f
    rw [boolText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := boolText_only_main f
      subst f
      cbv) (by cbv)

private def boolTextArrays :
    { value : PLift (∀ item ∈ uMembers (pre108 boolTextHeader.source.prepared.elaborierbar),
        Frontend.ArrayMeaning boolTextHeader.unit boolTextHeader.source.scopes item) //
      Frontend.checkArrays boolTextHeader.unit boolTextHeader.source.scopes
        (uMembers (pre108 boolTextHeader.source.prepared.elaborierbar)) = .ok value } := by
  refine ⟨?value, ?checked⟩
  case checked => cbv <;> exact Eq.refl _

private def boolTextProgram :
    { value : Programm (declOf boolTextHeader.unit) //
      OldSource.restore (pre108 boolTextHeader.source.prepared.elaborierbar)
        boolTextHeader.unit boolTextFunctions.program = .ok value } := by
  refine ⟨?value, ?restored⟩
  case restored => cbv <;> exact Eq.refl _

private theorem boolText_accepted :
    OldSource.accepts boolTextHeader.unit boolTextProgram.val = .ok true := by cbv

private def boolTextBody : Body boolTextHeader where
  functions := boolTextFunctions
  main := boolTextMain
  entry := by cbv
  initializers := by cbv
  arrays := boolTextArrays.val
  arrayEq := boolTextArrays.property
  program := boolTextProgram.val
  restored := boolTextProgram.property
  accepted := boolText_accepted

private theorem boolText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.boolText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨boolTextHeader, boolText_count, ⟨boolTextBody⟩⟩

theorem boolText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.boolText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.boolText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := boolText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end boolCompilation

-- Retain the canonical Header before any dependent function projection.
private def optionTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.optionText := by
  refine {
    source := sourceFrom optionTextInput optionTextTail
    sourceEq := sourceFrom_eq optionTextInput optionTextTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by cbv
    metadata := optionTextTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants optionTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact optionTextTail.metadata
    · rfl
  case elaborated =>
    cbv <;> exact Eq.refl _

private theorem optionText_count : optionTextHeader.unit.fns.length = 1 := by cbv

private def optionTextMain : Fin optionTextHeader.unit.fns.length :=
  ⟨0, by have count := optionText_count; omega⟩

private theorem optionText_only_main (f : Fin optionTextHeader.unit.fns.length) :
    f = optionTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [optionText_count] using f.isLt
  change f.val = 0
  omega

-- The actual complete lowering result is fixed before of_success selects it.
private def optionTextCode :
    { value : EnsTy optionTextHeader.unit optionTextMain × RumpTy optionTextHeader.unit optionTextMain ×
        ReqTy optionTextHeader.unit optionTextMain //
      lowerFnAt optionTextHeader.unit optionTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem optionText_code_eq :
    lowerFnAt optionTextHeader.unit optionTextMain = .ok optionTextCode.val := optionTextCode.property

private def optionTextFunctions : Functions optionTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := optionText_only_main f
    subst f
    rw [optionText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := optionText_only_main f
      subst f
      cbv) (by cbv)

private def optionTextArrays :
    { value : PLift (∀ item ∈ uMembers (pre108 optionTextHeader.source.prepared.elaborierbar),
        Frontend.ArrayMeaning optionTextHeader.unit optionTextHeader.source.scopes item) //
      Frontend.checkArrays optionTextHeader.unit optionTextHeader.source.scopes
        (uMembers (pre108 optionTextHeader.source.prepared.elaborierbar)) = .ok value } := by
  refine ⟨?value, ?checked⟩
  case checked => cbv <;> exact Eq.refl _

private def optionTextProgram :
    { value : Programm (declOf optionTextHeader.unit) //
      OldSource.restore (pre108 optionTextHeader.source.prepared.elaborierbar)
        optionTextHeader.unit optionTextFunctions.program = .ok value } := by
  refine ⟨?value, ?restored⟩
  case restored => cbv <;> exact Eq.refl _

private theorem optionText_accepted :
    OldSource.accepts optionTextHeader.unit optionTextProgram.val = .ok true := by cbv

private def optionTextBody : Body optionTextHeader where
  functions := optionTextFunctions
  main := optionTextMain
  entry := by cbv
  initializers := by cbv
  arrays := optionTextArrays.val
  arrayEq := optionTextArrays.property
  program := optionTextProgram.val
  restored := optionTextProgram.property
  accepted := optionText_accepted

private theorem optionText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.optionText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨optionTextHeader, optionText_count, ⟨optionTextBody⟩⟩

theorem optionText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.optionText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.optionText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := optionText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

-- Retain the canonical Header before any dependent function projection.
private def noneTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.noneText := by
  refine {
    source := sourceFrom noneTextInput noneTextTail
    sourceEq := sourceFrom_eq noneTextInput noneTextTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by cbv
    metadata := noneTextTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants noneTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact noneTextTail.metadata
    · rfl
  case elaborated =>
    cbv <;> exact Eq.refl _

private theorem noneText_count : noneTextHeader.unit.fns.length = 1 := by cbv

private def noneTextMain : Fin noneTextHeader.unit.fns.length :=
  ⟨0, by have count := noneText_count; omega⟩

private theorem noneText_only_main (f : Fin noneTextHeader.unit.fns.length) :
    f = noneTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [noneText_count] using f.isLt
  change f.val = 0
  omega

-- The actual complete lowering result is fixed before of_success selects it.
private def noneTextCode :
    { value : EnsTy noneTextHeader.unit noneTextMain × RumpTy noneTextHeader.unit noneTextMain ×
        ReqTy noneTextHeader.unit noneTextMain //
      lowerFnAt noneTextHeader.unit noneTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem noneText_code_eq :
    lowerFnAt noneTextHeader.unit noneTextMain = .ok noneTextCode.val := noneTextCode.property

private def noneTextFunctions : Functions noneTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := noneText_only_main f
    subst f
    rw [noneText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := noneText_only_main f
      subst f
      cbv) (by cbv)

private def noneTextArrays :
    { value : PLift (∀ item ∈ uMembers (pre108 noneTextHeader.source.prepared.elaborierbar),
        Frontend.ArrayMeaning noneTextHeader.unit noneTextHeader.source.scopes item) //
      Frontend.checkArrays noneTextHeader.unit noneTextHeader.source.scopes
        (uMembers (pre108 noneTextHeader.source.prepared.elaborierbar)) = .ok value } := by
  refine ⟨?value, ?checked⟩
  case checked => cbv <;> exact Eq.refl _

private def noneTextProgram :
    { value : Programm (declOf noneTextHeader.unit) //
      OldSource.restore (pre108 noneTextHeader.source.prepared.elaborierbar)
        noneTextHeader.unit noneTextFunctions.program = .ok value } := by
  refine ⟨?value, ?restored⟩
  case restored => cbv <;> exact Eq.refl _

private theorem noneText_accepted :
    OldSource.accepts noneTextHeader.unit noneTextProgram.val = .ok true := by cbv

private def noneTextBody : Body noneTextHeader where
  functions := noneTextFunctions
  main := noneTextMain
  entry := by cbv
  initializers := by cbv
  arrays := noneTextArrays.val
  arrayEq := noneTextArrays.property
  program := noneTextProgram.val
  restored := noneTextProgram.property
  accepted := noneText_accepted

private theorem noneText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.noneText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨noneTextHeader, noneText_count, ⟨noneTextBody⟩⟩

theorem noneText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.noneText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.noneText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := noneText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
