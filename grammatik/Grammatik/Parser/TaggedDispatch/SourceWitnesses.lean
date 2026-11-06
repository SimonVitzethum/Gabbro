module

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
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.TakeDrop
import all Init.Data.String.ToSlice
import all Grammatik.Parser.Elab.Proben.RightsConstants.Scanning
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

namespace Gabbro.Grammatik.Parser
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Two distinct payload types, a receiver between ordinary arguments, and a
    static member with complete conforming implementations in the same group. -/
@[expose] public def taggedSource (rectResult : String) : String :=
  "spec Shape[T] { " ++
  "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; " ++
  "fn copy(s: T) -> T effects {} costs <= 50 ops; } " ++
  "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool " ++
  "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } " ++
  "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> " ++ rectResult ++
  " effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } " ++
  "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; " ++
  "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { " ++
  "let answer = Shape::area(false, s, true); return answer; }"

@[expose] public def taggedSourceItems (rectResult : String) : Except String (List SItemTief) := do
  match lex (taggedSource rectResult) with
  | .error _ => .error "lex"
  | .ok tokens => parseTopTief tokens

@[expose] public def taggedSourceExpanded (rectResult : String) : Except String (List SItemTief) := do
  exportDeclarationUnit (uMembers (pre108 (← taggedSourceItems rectResult)))

@[expose] public def taggedSourceBody (name : String) : Except String SAnw := do
  let items ← taggedSourceExpanded "bool"
  let bodies := items.filterMap fun
    | .fnT sig body => if strEq sig.name name then some body else none
    | _ => none
  match bodies with
  | [body] => pure body
  | _ => throw "witness: generated function not unique"

@[expose] public def taggedExpectedMatch : SAnw :=
  .block [.cases (.variable "s")
    [.arm "Circle" (some "#dispatch")
      (.block [.bind false "#dispatch-result" none
        (.call "$spec$0$area"
          [.variable "prefix", .variable "#dispatch", .variable "suffix"])]
        (some (.ret (some (.variable "#dispatch-result"))))),
     .arm "Rect" (some "#dispatch")
      (.block [.bind false "#dispatch-result" none
        (.call "$spec$1$area"
          [.variable "prefix", .variable "#dispatch", .variable "suffix"])]
        (some (.ret (some (.variable "#dispatch-result")))))]] none


attribute [local cbv_opaque]
  Spec.Walk.expr Spec.Walk.type Spec.Walk.statement Spec.Walk.statements
  Spec.Walk.item Spec.Walk.constant Spec.resolveKnownBodies Spec.inferType
  Spec.canonicalType Spec.expandEffects Uebersetze.sErsetze Uebersetze.uKonstEval
  SourceFolds.hasRangeFold SourceFolds.hasRangeFoldList SourceFolds.hasRangeFoldAnw SourceFolds.hasRangeFoldAnwList
  SourceFolds.tagFoldNodes SourceFolds.tagFoldNodesList SourceFolds.expandNested Dyn.statementProducers
  Dyn.statementsProducers Dyn.statementUses Dyn.statementsUses Dyn.itemUses
  Dyn.itemsUses Dyn.lookup Dyn.containsDynamic
attribute [local cbv_eval]
  Spec.Walk.expr.eq_def Spec.Walk.type.eq_def Spec.Walk.statement.eq_def
  Spec.Walk.statements.eq_def Spec.Walk.item.eq_def Spec.Walk.constant.eq_def
  Spec.resolveKnownBodies.eq_def Spec.inferType.eq_def Spec.canonicalType.eq_def
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

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
open Gabbro.Grammatik.Parser.UebersetzeProben11.Phases (Input)
namespace TaggedSourceCuts
rights_cut piece0 as "spec Shape[T] { "
bound_fragment piece0 as "spec Shape[T] { "
rights_cut piece1 as "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; "
bound_fragment piece1 as "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; "
rights_cut piece2 as "fn copy(s: T) -> T effects {} costs <= 50 ops; } "
bound_fragment piece2 as "fn copy(s: T) -> T effects {} costs <= 50 ops; } "
rights_cut piece3 as "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool "
bound_fragment piece3 as "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool "
rights_cut piece4 as "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } "
bound_fragment piece4 as "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } "
rights_cut piece5 as "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> "
bound_fragment piece5 as "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> "
rights_cut piece7 as "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; "
bound_fragment piece7 as "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; "
rights_cut piece8 as "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { "
bound_fragment piece8 as "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { "
rights_cut piece9 as "let answer = Shape::area(false, s, true); return answer; }"
bound_fragment piece9 as "let answer = Shape::area(false, s, true); return answer; }"
rights_cut resultbool as "bool effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } "
bound_fragment resultbool as "bool effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } "
rights_cut resultu8 as "u8 effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } "
bound_fragment resultu8 as "u8 effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } "
rights_input inputbool : (taggedSource "bool")
  with_cuts [piece0, piece1, piece2, piece3, piece4, piece5, resultbool, piece7, piece8, piece9]
  with_text ["spec Shape[T] { ", "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; ", "fn copy(s: T) -> T effects {} costs <= 50 ops; } ", "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool ", "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } ", "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> ", "bool effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } ", "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; ", "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { ", "let answer = Shape::area(false, s, true); return answer; }"]
rights_input inputu8 : (taggedSource "u8")
  with_cuts [piece0, piece1, piece2, piece3, piece4, piece5, resultu8, piece7, piece8, piece9]
  with_text ["spec Shape[T] { ", "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; ", "fn copy(s: T) -> T effects {} costs <= 50 ops; } ", "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool ", "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } ", "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> ", "u8 effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } ", "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; ", "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { ", "let answer = Shape::area(false, s, true); return answer; }"]
end TaggedSourceCuts

private def sourceItems : {actual : List SItemTief // taggedSourceItems "bool" = .ok actual} := by
  refine ⟨?_, by
    rw [taggedSourceItems, TaggedSourceCuts.inputbool.text, lex_ofList, TaggedSourceCuts.inputbool.lexed]
    cbv <;> exact Eq.refl _⟩

private def wrongItems : {actual : List SItemTief // taggedSourceItems "u8" = .ok actual} := by
  refine ⟨?_, by
    rw [taggedSourceItems, TaggedSourceCuts.inputu8.text, lex_ofList, TaggedSourceCuts.inputu8.lexed]
    cbv <;> exact Eq.refl _⟩

private def sourceFold : {actual : List SItemTief //
    SourceFolds.prepare (uMembers (pre108 sourceItems.val)) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sourceClose : {actual : List Dyn.Closed × List SItemTief //
    Dyn.prepare sourceFold.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sourceTagged : {actual : List SItemTief × List String //
    exportTaggedUnitDetailed sourceClose.val.2 = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
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

private theorem source_expanded : taggedSourceExpanded "bool" = .ok sourceLibrary.val := by
  rw [taggedSourceExpanded, sourceItems.property]
  exact source_exported

private def wrongFold : {actual : List SItemTief //
    SourceFolds.prepare (uMembers (pre108 wrongItems.val)) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def wrongClose : {actual : List Dyn.Closed × List SItemTief //
    Dyn.prepare wrongFold.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem wrong_signature :
    exportTaggedUnitDetailed wrongClose.val.2 = .error "spec.signature" := by cbv

private theorem source_refused : taggedSourceExpanded "u8" = .error "spec.signature" := by
  simp only [taggedSourceExpanded, wrongItems.property, exportDeclarationUnit,
    exportDeclarationUnitDetailed, wrongFold.property, wrongClose.property,
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

/-- This also runs through the actual elaborator, beyond the expansion witness. -/
public theorem tagged_source_elaborated_zeuge :
    ((taggedSourceItems "bool").bind (fun items => elabU (pre108 items))).toOption.isSome = true := by
  rw [sourceItems.property]
  cbv

/-- A parsed implementation with the wrong result type is refused by name
    before any dispatcher is admitted. -/
public theorem tagged_source_signature_refused_zeuge :
    beqTopTief (taggedSourceExpanded "u8")
      (.error "spec.signature") = true := by
  rw [source_refused]
  cbv

end Gabbro.Grammatik.Parser
