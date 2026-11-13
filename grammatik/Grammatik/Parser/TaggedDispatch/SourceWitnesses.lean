module

public import Grammatik.Parser.TaggedDispatch.SourcePhases
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
public import Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Spec.Zeugen
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Modules.Frontend
import all Grammatik.Parser.Elab.Modules.Expansion
import all Grammatik.Parser.Elab.Generic.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
import all Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
import all Grammatik.Parser.TaggedDispatch.SourcePhases

public import Grammatik.Parser.TaggedDispatch.Frontend
public import Grammatik.Parser.Expr.Ausdruck.Teil3
public import Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Spec.Walk
import all Grammatik.Parser.Spec.Items
import all Grammatik.Parser.Spec.Expand
import all Grammatik.Parser.SourceFolds.Range
import all Grammatik.Parser.SourceFolds.Hoist
import all Grammatik.Parser.Dyn.Frontend
import all Grammatik.Parser.TaggedDispatch.Frontend
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Spec.Parse
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Typ
import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Dyn.WitnessPhases
import all Grammatik.Parser.Dyn.Collect
import all Grammatik.Parser.Dyn.Rewrite
import all Grammatik.Parser.Spec.Contract
import all Grammatik.Parser.Spec.Resolve
import all Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
import all Init.Data.Int.Repr
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
import all Grammatik.Parser.Elab.Proben.RightsConstants.Scanning
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
import Grammatik.Kern.Taktik.KernelRfl

namespace Gabbro.Grammatik.Parser
open Uebersetze UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

attribute [local cbv_opaque]
  Spec.Walk.expr Spec.Walk.type Spec.Walk.statement Spec.Walk.statements
  Spec.Walk.item Spec.Walk.constant Spec.resolveKnownBodies Spec.resolveKnownWith Spec.inferType Spec.inferTypeMit
  Spec.canonicalType Spec.expandEffects Uebersetze.sErsetze Uebersetze.uKonstEval
  SourceFolds.hasRangeFold SourceFolds.hasRangeFoldList SourceFolds.hasRangeFoldAnw SourceFolds.hasRangeFoldAnwList
  SourceFolds.tagFoldNodes SourceFolds.tagFoldNodesList SourceFolds.expandNested Dyn.statementProducers
  Dyn.statementsProducers Dyn.statementUses Dyn.statementsUses Dyn.itemUses
  Dyn.itemsUses Dyn.lookup Dyn.containsDynamic
attribute [local cbv_eval]
  Spec.Walk.expr.eq_def Spec.Walk.type.eq_def Spec.Walk.statement.eq_def
  Spec.Walk.statements.eq_def Spec.Walk.item.eq_def Spec.Walk.constant.eq_def
  Spec.resolveKnownBodies.eq_def Spec.resolveKnownWith.eq_def Spec.inferType.eq_def Spec.inferTypeMit.eq_def Spec.canonicalType.eq_def
  Spec.expandEffects.eq_def Uebersetze.sErsetze.eq_def Uebersetze.uKonstEval.eq_def
  SourceFolds.hasRangeFold.eq_def SourceFolds.hasRangeFoldList.eq_def SourceFolds.hasRangeFoldAnw.eq_def
  SourceFolds.hasRangeFoldAnwList.eq_def SourceFolds.tagFoldNodes.eq_def SourceFolds.tagFoldNodesList.eq_def
  SourceFolds.expandNested.eq_def Dyn.statementProducers.eq_def Dyn.statementsProducers.eq_def
  Dyn.statementUses.eq_def Dyn.statementsUses.eq_def Dyn.itemUses.eq_def
  Dyn.itemsUses.eq_def Dyn.lookup.eq_def Dyn.containsDynamic.eq_def
attribute [local cbv_eval] Spec.Walk.expr_literal Spec.Walk.type_atom

attribute [local cbv_opaque] Uebersetze.uFloatLimit
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def

private def sourceSpec : {actual : List SItemTief //
    Spec.prepare (Dyn.finish sourceClose.val.1 sourceTagged.val.1) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sourceChecked : {actual : List SItemTief //
    Dyn.checkedOutput sourceTagged.val.1 sourceSpec.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sourceLibrary : {actual : List SItemTief //
    exportLibraryUnit sourceChecked.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem source_exported :
    exportDeclarationUnit (uMembers (pre108 sourceItems.val)) = .ok sourceLibrary.val :=
  Dyn.export_from_phases (source := uMembers (pre108 sourceItems.val))
    (folded := sourceFold.val) (closed := sourceClose.val.1) (rewritten := sourceClose.val.2)
    (tagged := sourceTagged.val.1) (names := sourceTagged.val.2)
    (ordinary := sourceSpec.val) (validated := sourceChecked.val) (output := sourceLibrary.val)
    sourceFold.property sourceClose.property sourceTagged.property sourceSpec.property
    sourceChecked.property sourceLibrary.property

private theorem expanded_from_items (word : String) (items : List SItemTief)
    (result : Except String (List SItemTief))
    (parsed : taggedSourceItems word = .ok items)
    (exported : exportDeclarationUnit (uMembers (pre108 items)) = result) :
    taggedSourceExpanded word = result := by
  simpa only [taggedSourceExpanded, parsed, bind, Except.bind] using exported

private theorem source_expanded : taggedSourceExpanded "bool" = .ok sourceLibrary.val :=
  expanded_from_items "bool" sourceItems.val (.ok sourceLibrary.val)
    sourceItems.property source_exported

private def wrongFold : {actual : List SItemTief //
    SourceFolds.prepare (uMembers (pre108 wrongItems.val)) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem wrong_signature : Dyn.prepare wrongFold.val = .error "spec.signature" := by cbv

private theorem source_refused : taggedSourceExpanded "u8" = .error "spec.signature" := by
  apply expanded_from_items "u8" wrongItems.val _ wrongItems.property
  simp only [exportDeclarationUnit,
    exportDeclarationUnitDetailed, wrongFold.property,
    wrong_signature, bind, Except.bind, Except.map]

attribute [local cbv_opaque] taggedSourceExpanded
attribute [local cbv_eval] source_expanded

/-- Source text → lexer → group/by parser → pre108 → checked declaration
    expansion → the exact generated match, with both case implementations. -/
public theorem tagged_source_match_zeuge :
    taggedSourceBody "#tagged-AnyShape::Shape::area" = .ok taggedExpectedMatch := by cbv

/-- The source call is connected to that generated function in the same pass. -/
public theorem tagged_source_call_zeuge :
    taggedSourceBody "sample" =
      .ok (.block [.bind false "answer" none
        (.call "#tagged-AnyShape::Shape::area" [.fls, .variable "s", .tru])]
        (some (.ret (some (.variable "answer"))))) := by cbv

attribute [local cbv_opaque] elabFn uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen uSondenFns uTorHuellen uSpecEin
attribute [local cbv_eval] Spec.function_block row_nil row_cons core_bind
  bound_names_select pointer_source_select start_source_select sonden_nil wrappers_nil
  Spec.spec_expression_select Spec.substitution_select
  clauses_nil clauses_effect clauses_cost clauses_effect_cost
  return_none return_empty return_variable fold_end_none fold_end_empty fold_end_variable

-- Select the actual predecessor before passing the recursive reader to uCases.
-- No arm, continuation, end reader or body context is evaluated by this equation.
private theorem source_cases (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (scrutinee : SExpr) (arms rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.cases scrutinee arms :: rest) =
      match fuel with
      | 0 => .error "nesting without G form"
      | next + 1 => uCases (uAnwReihe tabs heads next) ctx scrutinee arms rest := by
  cases fuel <;> simp only [uAnwReiheCore]

attribute [local cbv_eval] source_cases

-- Keep the existing declaration packets at the real Modules boundary. In
-- particular the elaboration proof below never repeats fold/closure/tag/spec
-- expansion while normalizing a function's body context.
private def sourceDeclarationNames : {names : List String //
    exportDeclarationUnitDetailed (uMembers (pre108 sourceItems.val)) =
      .ok (sourceLibrary.val, names)} := by
  refine ⟨?_, by
    simp only [exportDeclarationUnitDetailed, sourceFold.property,
      sourceClose.property, sourceTagged.property, sourceSpec.property,
      sourceChecked.property, sourceLibrary.property, bind, Except.bind]
    cbv <;> exact Eq.refl _⟩

private theorem modules_from_phases (items : List SItemTief)
    (output : List SItemTief) (names : List String)
    (ordinary : Modules.syntaxList items = false)
    (modules : Modules.expandWithRequirements items = .ok { items := items })
    (generic : Generic.expandDetailed (uMembers items) [] =
      .ok { items := uMembers items })
    (adapters : entzuckere (uMembers items) = .ok (uMembers items))
    (numbers : MatchNumber.erweitere (uMembers items) = .ok (uMembers items))
    (wildcards : MatchWildcard.erweitere (uMembers items) = uMembers items)
    (hoisted : CallHoist.hebe (uMembers items) = uMembers items)
    (declarations : exportDeclarationUnitDetailed (uMembers items) = .ok (output, names))
    (accepted : Modules.validOutput items
      { items := output, requirements := [],
        generatedNames := names.filter ((Modules.outputNames output).contains) } = true) :
    expandU items = .ok (output, []) := by
  simp only [expandU, Modules.prepare, Modules.prepareDetailedRaw, modules,
    ordinary, Bool.false_eq_true, ite_false, generic, adapters, numbers, wildcards, hoisted, declarations,
    bind, Except.bind, List.nil_append, accepted, ite_true, pure, Except.pure]

private theorem source_no_modules : Modules.syntaxList (pre108 sourceItems.val) = false := by cbv

private theorem source_module_expansion :
    Modules.expandWithRequirements (pre108 sourceItems.val) =
      .ok { items := pre108 sourceItems.val } := by cbv

private theorem source_generic_expansion :
    Generic.expandDetailed (uMembers (pre108 sourceItems.val)) [] =
      .ok { items := uMembers (pre108 sourceItems.val) } := by cbv

private theorem source_adapters :
    entzuckere (uMembers (pre108 sourceItems.val)) =
      .ok (uMembers (pre108 sourceItems.val)) := by cbv

/-- The dispatching source expands and elaborates: the call `Shape::area(false, s, true)` passes
    the tagged value `s : AnyShape` as an argument of its own declaration. -/
public theorem tagged_source_elaboration_zeuge :
    ((taggedSourceItems "bool").bind (fun items => elabU (pre108 items))).toOption.isSome = true := by
  rw [sourceItems.property]
  change (elabU (pre108 sourceItems.val)).toOption.isSome = true
  kernel_rfl

/-- A parsed implementation with the wrong result type is refused by name
    before any dispatcher is admitted. -/
public theorem tagged_source_signature_refused_zeuge :
    beqTopTief (taggedSourceExpanded "u8")
      (.error "spec.signature") = true := by
  rw [source_refused]
  cbv

end Gabbro.Grammatik.Parser
