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
theorem globalText_parsed :
    (parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

/-- Construct the complete source and elaborator packet before projecting its dependent unit. -/
def globalTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.globalText := by
  have parsing : (parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.isSome = true := by
    exact globalText_parsed
  have parsed : parseTopTief (globalTextScan.tokens ++ [.ende]) =
      .ok ((parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.get parsing) := by
    exact Gabbro.Grammatik.except_ok_get (ε := String)
      (α := List SItemTief) (x := parseTopTief (globalTextScan.tokens ++ [.ende])) parsing
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
    split
    · rename_i error rejected
      cases rejected.symm.trans globalText_lexed
    · rename_i tokens selected
      have same : tokens = globalTextScan.tokens ++ [.ende] :=
        Except.ok.inj (selected.symm.trans globalText_lexed)
      subst tokens
      split
      · rename_i error rejected
        cases rejected.symm.trans parsed
      · rename_i items selected
        have same : items =
            (parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.get parsing :=
          Except.ok.inj (selected.symm.trans parsed)
        subst items
        cbv <;> exact Eq.refl _
  case expansion => cbv <;> exact Eq.refl _
  case constants => cbv <;> exact Eq.refl _
  case ordinary => cbv
  case metadata => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _

/-- Keep all three actual function results together through canonical assembly and admission. -/
def globalTextBody : Body globalTextHeader := by
  refine {
    functions := {
      values := fun f => Fin.cases (n := 0)
        (motive := fun f : Fin globalTextHeader.unit.fns.length =>
          EnsTy globalTextHeader.unit f × RumpTy globalTextHeader.unit f × ReqTy globalTextHeader.unit f)
        ?functionValue (fun impossible => Fin.elim0 impossible) f
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
    have count : globalTextHeader.unit.fns.length = 1 := by cbv
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv <;> exact Eq.refl _
  case noMeasures =>
    intro f
    rcases f with ⟨index, bound⟩
    have count : globalTextHeader.unit.fns.length = 1 := by cbv
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

theorem globalText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.globalText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.globalText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨result, origin, unitEq⟩ := compiled globalTextHeader globalTextBody
  refine ⟨result, origin, ?_⟩
  rw [unitEq]
  cbv

/-- Parse this already certified token stream once. -/
theorem qualifiedText_parsed :
    (parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

/-- Construct the complete source and elaborator packet before projecting its dependent unit. -/
def qualifiedTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText := by
  have parsing : (parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.isSome = true := by
    exact qualifiedText_parsed
  have parsed : parseTopTief (qualifiedTextScan.tokens ++ [.ende]) =
      .ok ((parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.get parsing) := by
    exact Gabbro.Grammatik.except_ok_get (ε := String)
      (α := List SItemTief) (x := parseTopTief (qualifiedTextScan.tokens ++ [.ende])) parsing
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
    split
    · rename_i error rejected
      cases rejected.symm.trans qualifiedText_lexed
    · rename_i tokens selected
      have same : tokens = qualifiedTextScan.tokens ++ [.ende] :=
        Except.ok.inj (selected.symm.trans qualifiedText_lexed)
      subst tokens
      split
      · rename_i error rejected
        cases rejected.symm.trans parsed
      · rename_i items selected
        have same : items =
            (parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.get parsing :=
          Except.ok.inj (selected.symm.trans parsed)
        subst items
        cbv <;> exact Eq.refl _
  case expansion => cbv <;> exact Eq.refl _
  case constants => cbv <;> exact Eq.refl _
  case ordinary => cbv
  case metadata => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _

/-- Keep all three actual function results together through canonical assembly and admission. -/
def qualifiedTextBody : Body qualifiedTextHeader := by
  refine {
    functions := {
      values := fun f => Fin.cases (n := 0)
        (motive := fun f : Fin qualifiedTextHeader.unit.fns.length =>
          EnsTy qualifiedTextHeader.unit f × RumpTy qualifiedTextHeader.unit f × ReqTy qualifiedTextHeader.unit f)
        ?functionValue (fun impossible => Fin.elim0 impossible) f
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
    have count : qualifiedTextHeader.unit.fns.length = 1 := by cbv
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv <;> exact Eq.refl _
  case noMeasures =>
    intro f
    rcases f with ⟨index, bound⟩
    have count : qualifiedTextHeader.unit.fns.length = 1 := by cbv
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

theorem qualifiedText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText, compile Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨result, origin, unitEq⟩ := compiled qualifiedTextHeader qualifiedTextBody
  refine ⟨result, origin, ?_⟩
  rw [unitEq]
  cbv

end Gabbro.Stage0.Frontend.ConstPhases
