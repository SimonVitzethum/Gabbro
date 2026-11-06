module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.GlobalSources
import all Stage0.Frontend.Witnesses.Constants.GlobalSources
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import Init.Data.String.Lemmas.Intercalate
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

-- Use the source owner's successful metadata and closed qualified-name equation.
attribute [local cbv_eval] globalText_metadata qualifiedText_metadata String.intercalate_singleton

-- Eliminate the source-list reindexing while all phase values are still abstract.
private theorem original_scope_data {text : String} (input : SourceInput text)
    (items : List SItemTief) (origin : input.original = items)
    (metadata : Konst.checkSourceMetadata items = .ok ())
    (order : Frontend.AliasOrder items) (ordered : Frontend.orderAliases items = .ok order)
    (derived : Frontend.DerivedScopes items)
    (elaborated : Frontend.elaborateConstantScopes items = .ok derived)
    (aliases : items.all (Frontend.checkAliasMeaning derived.scope.types) = true)
    (constants : items.all (Frontend.checkConstantMeaning derived.scope.types
      derived.scope.functions derived.scope.values) = true) :
    let tail := SourceTail.ofOriginal input items origin metadata order ordered
      derived elaborated aliases constants
    (tail.derived.scope.types, tail.derived.scope.functions, tail.derived.scope.values) =
      (derived.scope.types, derived.scope.functions, derived.scope.values) := by
  cases origin
  rfl

private theorem qualified_scope_data :
    (qualifiedTextTail.derived.scope.types, qualifiedTextTail.derived.scope.functions,
      qualifiedTextTail.derived.scope.values) =
    (qualifiedScopesPacket.val.scope.types, qualifiedScopesPacket.val.scope.functions,
      qualifiedScopesPacket.val.scope.values) :=
  original_scope_data qualifiedTextInput qualifiedOriginalPacket.val qualifiedOriginalPacket.property
    qualified_metadata qualifiedOrderPacket.val qualifiedOrderPacket.property
    qualifiedScopesPacket.val qualifiedScopesPacket.property qualified_aliases qualified_constants

@[local cbv_eval] private theorem qualified_scope_types :
    qualifiedTextTail.derived.scope.types = qualifiedScopesPacket.val.scope.types :=
  congrArg Prod.fst qualified_scope_data
@[local cbv_eval] private theorem qualified_scope_functions :
    qualifiedTextTail.derived.scope.functions = qualifiedScopesPacket.val.scope.functions :=
  congrArg (fun data => data.2.1) qualified_scope_data
@[local cbv_eval] private theorem qualified_scope_values :
    qualifiedTextTail.derived.scope.values = qualifiedScopesPacket.val.scope.values :=
  congrArg (fun data => data.2.2) qualified_scope_data

-- Select the real constant checker with its original meaning, type, value and literal gates.
private theorem checked_u8_five {original : List SItemTief}
    (u : UProg) (scope : Frontend.Scopes original) (name : String)
    (meaning : Frontend.checkConstantMeaning scope.types scope.functions scope.values
      (.constT name (.atom "u8") (.one (.lit 5))) = true)
    (typed : uTypIn scope.types [] (uRecordConstantTypes u.records) [] []
      (.atom "u8") = .ok (.int 0 255)) :
    (Frontend.checkArrayItem u scope
      (.constT name (.atom "u8") (.one (.lit 5)))).toOption.isSome = true := by
  have evaluated : uKonstZeile scope.types scope.functions scope.values (.int 0 255)
      (.one (.lit 5)) (uRecordConstant u.records scope.types scope.functions scope.values) =
      some (.lit 5) := by
    rw [uKonstZeile_int]
    rfl
  have lower : (0 : Int) ≤ 5 := by decide
  have upper : (5 : Int) ≤ 255 := by decide
  have lowered : lowLit (u := u) (Γ := []) (Λ := []) (.int 0 255) (.lit 5) =
      .ok (.widen lower upper (.lit 5)) := by
    simp only [lowLit, dite_eq_left lower, dite_eq_left upper]
  unfold Frontend.checkArrayItem
  dsimp only [Frontend.arrayInput]
  split
  · split
    · rename_i error rejected
      cases rejected.symm.trans typed
    · rename_i actual selected
      have same : actual = .int 0 255 := Except.ok.inj (selected.symm.trans typed)
      subst actual
      split
      · rename_i rejected
        cases rejected.symm.trans evaluated
      · rename_i actual selected
        have same : actual = .lit 5 := Option.some.inj (selected.symm.trans evaluated)
        subst actual
        split
        · rename_i error rejected
          cases rejected.symm.trans lowered
        · rfl
  · rename_i rejected
    exact False.elim (rejected meaning)

-- Name the complete canonical header before any dependent code projection.
private def globalTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.globalText := by
  refine {
    source := sourceFrom globalTextInput globalTextTail
    sourceEq := sourceFrom_eq globalTextInput globalTextTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by cbv
    metadata := globalTextTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants globalTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact globalTextTail.metadata
    · rfl
  case elaborated => cbv <;> exact Eq.refl _

private theorem globalText_count : globalTextHeader.unit.fns.length = 1 := by cbv
private def globalTextMain : Fin globalTextHeader.unit.fns.length :=
  ⟨0, by have count := globalText_count; omega⟩
private theorem globalText_only_main (f : Fin globalTextHeader.unit.fns.length) :
    f = globalTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [globalText_count] using f.isLt
  change f.val = 0
  omega

private def globalTextCode :
    { value : EnsTy globalTextHeader.unit globalTextMain ×
        RumpTy globalTextHeader.unit globalTextMain × ReqTy globalTextHeader.unit globalTextMain //
      lowerFnAt globalTextHeader.unit globalTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem globalText_code_eq :
    lowerFnAt globalTextHeader.unit globalTextMain = .ok globalTextCode.val := globalTextCode.property

private def globalTextFunctions : Functions globalTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := globalText_only_main f
    subst f
    rw [globalText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := globalText_only_main f
      subst f
      cbv) (by cbv)

-- Obtain the original item spine from the producer; only its scalar leaf is fixed here.
private theorem globalText_arrays_ready :
    (Frontend.checkArrays globalTextHeader.unit globalTextHeader.source.scopes
      globalTextInput.original).toOption.isSome = true := by
  have typed : uTypIn globalTextHeader.source.scopes.types []
      (uRecordConstantTypes globalTextHeader.unit.records) [] [] (.atom "u8") =
      .ok (.int 0 255) := by cbv
  have itemSpine : ∃ name firstSig firstBody lastSig lastBody,
      globalTextInput.original = [.constT name (.atom "u8") (.one (.lit 5)),
        .fnT firstSig firstBody, .fnT lastSig lastBody] := by
    refine ⟨?name, ?firstSig, ?firstBody, ?lastSig, ?lastBody, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  obtain ⟨name, firstSig, firstBody, lastSig, lastBody, origin⟩ := itemSpine
  have meanings : globalTextInput.original.all
      (Frontend.checkConstantMeaning globalTextHeader.source.scopes.types
        globalTextHeader.source.scopes.functions globalTextHeader.source.scopes.values) = true :=
    globalTextTail.constants
  apply checked_array_items
  intro item member
  have meaning := List.all_eq_true.mp meanings item member
  rw [origin] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact checked_u8_five globalTextHeader.unit globalTextHeader.source.scopes name meaning typed
  · rfl
  · rfl

private theorem globalText_entry_free (f : Fin globalTextHeader.unit.fns.length) :
    (OldSource.clauses globalTextHeader.expanded (fnAt globalTextHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := globalText_only_main f
  subst f
  cbv

private theorem globalText_restored :
    OldSource.restore (pre108 globalTextHeader.source.prepared.elaborierbar)
      globalTextHeader.unit globalTextFunctions.program = .ok globalTextFunctions.program :=
  restore_entry_free _ globalTextHeader.expanded globalTextHeader.requirements
    globalTextHeader.unit globalTextFunctions.program globalTextHeader.expansion globalText_entry_free

private theorem globalText_accepted :
    OldSource.accepts globalTextHeader.unit globalTextFunctions.program = .ok true := by
  apply accepts_function_results globalTextFunctions
  intro invariants pointers foreigns
  cbv

private def globalTextBody : Body globalTextHeader where
  functions := globalTextFunctions
  main := globalTextMain
  entry := by cbv
  initializers := by cbv
  arrays := (Frontend.checkArrays globalTextHeader.unit globalTextHeader.source.scopes
    globalTextInput.original).toOption.get globalText_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get globalText_arrays_ready
  program := globalTextFunctions.program
  restored := globalText_restored
  accepted := globalText_accepted

private theorem globalText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.globalText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨globalTextHeader, globalText_count, ⟨globalTextBody⟩⟩

theorem globalText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.globalText,
      compile Gabbro.Stage0.Frontend.ConstValuesWitness.globalText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := globalText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

-- Name the complete canonical header before any dependent code projection.
private def qualifiedTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText := by
  refine {
    source := sourceFrom qualifiedTextInput qualifiedTextTail
    sourceEq := sourceFrom_eq qualifiedTextInput qualifiedTextTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by
      change qualifiedTextInput.original.any Frontend.expansionHeader = false
      rw [qualifiedOriginalPacket.property]
      cbv
    metadata := qualifiedTextTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants qualifiedTextInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact qualifiedTextTail.metadata
    · rfl
  case elaborated =>
    change ((Frontend.elabWithScopes (pre108 qualifiedTextInput.prepared.elaborierbar)
      qualifiedTextTail.derived.scope.values qualifiedTextTail.derived.scope.types
      qualifiedTextTail.derived.scope.functions (Frontend.tableWithEmpty
        qualifiedTextTail.derived.scope.values qualifiedTextTail.derived.scope.types)).bind
          (Profil.selectUnit {})) = .ok _
    rw [qualified_scope_values, qualified_scope_types, qualified_scope_functions]
    cbv <;> exact Eq.refl _

private theorem qualifiedText_count : qualifiedTextHeader.unit.fns.length = 1 := by cbv
private def qualifiedTextMain : Fin qualifiedTextHeader.unit.fns.length :=
  ⟨0, by have count := qualifiedText_count; omega⟩
private theorem qualifiedText_only_main (f : Fin qualifiedTextHeader.unit.fns.length) :
    f = qualifiedTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [qualifiedText_count] using f.isLt
  change f.val = 0
  omega

private def qualifiedTextCode :
    { value : EnsTy qualifiedTextHeader.unit qualifiedTextMain ×
        RumpTy qualifiedTextHeader.unit qualifiedTextMain × ReqTy qualifiedTextHeader.unit qualifiedTextMain //
      lowerFnAt qualifiedTextHeader.unit qualifiedTextMain = .ok value } := by
  refine ⟨?value, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

@[local cbv_eval] private theorem qualifiedText_code_eq :
    lowerFnAt qualifiedTextHeader.unit qualifiedTextMain = .ok qualifiedTextCode.val := qualifiedTextCode.property

private def qualifiedTextFunctions : Functions qualifiedTextHeader.unit :=
  Functions.of_success (fun f => by
    have same := qualifiedText_only_main f
    subst f
    rw [qualifiedText_code_eq]
    rfl) (by cbv) (fun f => by
      have same := qualifiedText_only_main f
      subst f
      cbv) (by cbv)

-- Obtain the original item spine from the producer; only its scalar leaf is fixed here.
private theorem qualifiedText_arrays_ready :
    (Frontend.checkArrays qualifiedTextHeader.unit qualifiedTextHeader.source.scopes
      qualifiedTextInput.original).toOption.isSome = true := by
  have typed : uTypIn qualifiedTextHeader.source.scopes.types []
      (uRecordConstantTypes qualifiedTextHeader.unit.records) [] [] (.atom "u8") =
      .ok (.int 0 255) := by
    change uTypIn qualifiedTextTail.derived.scope.types []
      (uRecordConstantTypes qualifiedTextHeader.unit.records) [] [] (.atom "u8") = .ok (.int 0 255)
    rw [qualified_scope_types]
    cbv
  have itemSpine : ∃ name firstSig firstBody lastSig lastBody,
      qualifiedTextInput.original = [.constT name (.atom "u8") (.one (.lit 5)),
        .fnT firstSig firstBody, .fnT lastSig lastBody] := by
    rw [qualifiedOriginalPacket.property]
    refine ⟨?name, ?firstSig, ?firstBody, ?lastSig, ?lastBody, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  obtain ⟨name, firstSig, firstBody, lastSig, lastBody, origin⟩ := itemSpine
  have meanings : qualifiedTextInput.original.all
      (Frontend.checkConstantMeaning qualifiedTextHeader.source.scopes.types
        qualifiedTextHeader.source.scopes.functions qualifiedTextHeader.source.scopes.values) = true :=
    qualifiedTextTail.constants
  apply checked_array_items
  intro item member
  have meaning := List.all_eq_true.mp meanings item member
  rw [origin] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact checked_u8_five qualifiedTextHeader.unit qualifiedTextHeader.source.scopes name meaning typed
  · rfl
  · rfl

private theorem qualifiedText_entry_free (f : Fin qualifiedTextHeader.unit.fns.length) :
    (OldSource.clauses qualifiedTextHeader.expanded (fnAt qualifiedTextHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := qualifiedText_only_main f
  subst f
  cbv

private theorem qualifiedText_restored :
    OldSource.restore (pre108 qualifiedTextHeader.source.prepared.elaborierbar)
      qualifiedTextHeader.unit qualifiedTextFunctions.program = .ok qualifiedTextFunctions.program :=
  restore_entry_free _ qualifiedTextHeader.expanded qualifiedTextHeader.requirements
    qualifiedTextHeader.unit qualifiedTextFunctions.program qualifiedTextHeader.expansion qualifiedText_entry_free

private theorem qualifiedText_accepted :
    OldSource.accepts qualifiedTextHeader.unit qualifiedTextFunctions.program = .ok true := by
  apply accepts_function_results qualifiedTextFunctions
  intro invariants pointers foreigns
  cbv

private def qualifiedTextBody : Body qualifiedTextHeader where
  functions := qualifiedTextFunctions
  main := qualifiedTextMain
  entry := by cbv
  initializers := by cbv
  arrays := (Frontend.checkArrays qualifiedTextHeader.unit qualifiedTextHeader.source.scopes
    qualifiedTextInput.original).toOption.get qualifiedText_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get qualifiedText_arrays_ready
  program := qualifiedTextFunctions.program
  restored := qualifiedText_restored
  accepted := qualifiedText_accepted

private theorem qualifiedText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨qualifiedTextHeader, qualifiedText_count, ⟨qualifiedTextBody⟩⟩

theorem qualifiedText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText,
      compile Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := qualifiedText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
