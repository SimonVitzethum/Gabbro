module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.NamedSources
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

/-- Retain the actual elaborated constructor and all body facts inside one opaque theorem. -/
private theorem tagText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.tagText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) := by
  let header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.tagText := by
    refine {
      source := sourceFrom tagTextInput tagTextTail
      sourceEq := by exact sourceFrom_eq tagTextInput tagTextTail
      expanded := ?expanded
      requirements := ?requirements
      expansion := ?expansion
      constants := ?constants
      ordinary := by cbv
      metadata := by exact tagTextTail.metadata
      candidate := ?candidate
      elaborated := ?elaborated }
    case expansion => cbv <;> exact Eq.refl _
    case constants =>
      change Konst.checkSourceConstants tagTextInput.original = .ok ()
      unfold Konst.checkSourceConstants
      split
      · exact tagTextTail.metadata
      · rfl
    case elaborated => cbv <;> exact Eq.refl _
  have count : header.unit.fns.length = 1 := by cbv
  have produced : ∀ f : Fin header.unit.fns.length,
      (lowerFnAt header.unit f).toOption.isSome = true := by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv
  let functions : Functions header.unit := Functions.of_success produced (by cbv) (by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv) (by cbv)
  refine ⟨header, count, ?body⟩
  case body =>
    refine ⟨{
      functions := functions
      main := ⟨0, by omega⟩
      entry := by cbv
      initializers := by cbv
      arrays := ?arrays
      arrayEq := ?arrayEq
      program := ?program
      restored := ?restored
      accepted := ?accepted }⟩
    case arrayEq => cbv <;> exact Eq.refl _
    case restored => cbv <;> exact Eq.refl _
    case accepted => cbv

theorem tagText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.tagText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.tagText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := tagText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

/-- Retain the actual elaborated constructor and all body facts inside one opaque theorem. -/
private theorem stringText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.stringText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) := by
  let header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.stringText := by
    refine {
      source := sourceFrom stringTextInput stringTextTail
      sourceEq := by exact sourceFrom_eq stringTextInput stringTextTail
      expanded := ?expanded
      requirements := ?requirements
      expansion := ?expansion
      constants := ?constants
      ordinary := by cbv
      metadata := by exact stringTextTail.metadata
      candidate := ?candidate
      elaborated := ?elaborated }
    case expansion => cbv <;> exact Eq.refl _
    case constants =>
      change Konst.checkSourceConstants stringTextInput.original = .ok ()
      unfold Konst.checkSourceConstants
      split
      · exact stringTextTail.metadata
      · rfl
    case elaborated => cbv <;> exact Eq.refl _
  have count : header.unit.fns.length = 1 := by cbv
  have produced : ∀ f : Fin header.unit.fns.length,
      (lowerFnAt header.unit f).toOption.isSome = true := by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv
  let functions : Functions header.unit := Functions.of_success produced (by cbv) (by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv) (by cbv)
  refine ⟨header, count, ?body⟩
  case body =>
    refine ⟨{
      functions := functions
      main := ⟨0, by omega⟩
      entry := by cbv
      initializers := by cbv
      arrays := ?arrays
      arrayEq := ?arrayEq
      program := ?program
      restored := ?restored
      accepted := ?accepted }⟩
    case arrayEq => cbv <;> exact Eq.refl _
    case restored => cbv <;> exact Eq.refl _
    case accepted => cbv

theorem stringText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.stringText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.stringText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := stringText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
