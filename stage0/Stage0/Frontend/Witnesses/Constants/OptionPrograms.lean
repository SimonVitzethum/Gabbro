module
public import Stage0.Frontend.Witnesses.Constants.Compilation
public import Stage0.Frontend.Witnesses.Constants.Lexical
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
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

/-- Parse this already certified token stream once. -/
private theorem boolText_parsed :
    (parseTopTief (boolTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

/-- Construct the complete source and elaborator packet before projecting its dependent unit. -/
def boolTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.boolText := by
  have parsed := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := List SItemTief) (x := parseTopTief (boolTextScan.tokens ++ [.ende])) boolText_parsed
  refine {
    source := ?source
    sourceEq := ?sourceEq
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := ?ordinary
    metadata := ?metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case sourceEq =>
    unfold Frontend.source
    rw [boolText_lexed]
    dsimp only
    rw [parsed]
    dsimp only
    cbv <;> exact Eq.refl _
  case expansion => cbv <;> exact Eq.refl _
  case constants => cbv <;> exact Eq.refl _
  case ordinary => cbv
  case metadata => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _

/-- Keep all three actual function results together through canonical assembly and admission. -/
def boolTextBody : Body boolTextHeader := by
  refine {
    functions := {
      values := Fin.cases ?functionValue (fun impossible => Fin.elim0 impossible)
      equations := ?functionEq
      noInvariants := by cbv
      noMeasures := ?noMeasures
      contracts := by cbv }
    main := ⟨0, by cbv⟩
    entry := by cbv
    initializers := by cbv
    arrays := ?arrays
    arrayEq := ?arrayEq
    program := ?program
    restored := ?restored
    accepted := ?accepted }
  case functionEq =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv <;> exact Eq.refl _
  case noMeasures =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

theorem boolText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.boolText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.boolText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨result, origin, unitEq⟩ := compiled boolTextHeader boolTextBody
  refine ⟨result, origin, ?_⟩
  rw [unitEq]
  cbv

/-- Parse this already certified token stream once. -/
private theorem optionText_parsed :
    (parseTopTief (optionTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

/-- Construct the complete source and elaborator packet before projecting its dependent unit. -/
def optionTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.optionText := by
  have parsed := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := List SItemTief) (x := parseTopTief (optionTextScan.tokens ++ [.ende])) optionText_parsed
  refine {
    source := ?source
    sourceEq := ?sourceEq
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := ?ordinary
    metadata := ?metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case sourceEq =>
    unfold Frontend.source
    rw [optionText_lexed]
    dsimp only
    rw [parsed]
    dsimp only
    cbv <;> exact Eq.refl _
  case expansion => cbv <;> exact Eq.refl _
  case constants => cbv <;> exact Eq.refl _
  case ordinary => cbv
  case metadata => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _

/-- Keep all three actual function results together through canonical assembly and admission. -/
def optionTextBody : Body optionTextHeader := by
  refine {
    functions := {
      values := Fin.cases ?functionValue (fun impossible => Fin.elim0 impossible)
      equations := ?functionEq
      noInvariants := by cbv
      noMeasures := ?noMeasures
      contracts := by cbv }
    main := ⟨0, by cbv⟩
    entry := by cbv
    initializers := by cbv
    arrays := ?arrays
    arrayEq := ?arrayEq
    program := ?program
    restored := ?restored
    accepted := ?accepted }
  case functionEq =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv <;> exact Eq.refl _
  case noMeasures =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

theorem optionText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.optionText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.optionText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨result, origin, unitEq⟩ := compiled optionTextHeader optionTextBody
  refine ⟨result, origin, ?_⟩
  rw [unitEq]
  cbv

/-- Parse this already certified token stream once. -/
private theorem noneText_parsed :
    (parseTopTief (noneTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

/-- Construct the complete source and elaborator packet before projecting its dependent unit. -/
def noneTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.noneText := by
  have parsed := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := List SItemTief) (x := parseTopTief (noneTextScan.tokens ++ [.ende])) noneText_parsed
  refine {
    source := ?source
    sourceEq := ?sourceEq
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := ?ordinary
    metadata := ?metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case sourceEq =>
    unfold Frontend.source
    rw [noneText_lexed]
    dsimp only
    rw [parsed]
    dsimp only
    cbv <;> exact Eq.refl _
  case expansion => cbv <;> exact Eq.refl _
  case constants => cbv <;> exact Eq.refl _
  case ordinary => cbv
  case metadata => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _

/-- Keep all three actual function results together through canonical assembly and admission. -/
def noneTextBody : Body noneTextHeader := by
  refine {
    functions := {
      values := Fin.cases ?functionValue (fun impossible => Fin.elim0 impossible)
      equations := ?functionEq
      noInvariants := by cbv
      noMeasures := ?noMeasures
      contracts := by cbv }
    main := ⟨0, by cbv⟩
    entry := by cbv
    initializers := by cbv
    arrays := ?arrays
    arrayEq := ?arrayEq
    program := ?program
    restored := ?restored
    accepted := ?accepted }
  case functionEq =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv <;> exact Eq.refl _
  case noMeasures =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    cbv
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

theorem noneText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.noneText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.noneText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨result, origin, unitEq⟩ := compiled noneTextHeader noneTextBody
  refine ⟨result, origin, ?_⟩
  rw [unitEq]
  cbv

end Gabbro.Stage0.Frontend.ConstPhases
