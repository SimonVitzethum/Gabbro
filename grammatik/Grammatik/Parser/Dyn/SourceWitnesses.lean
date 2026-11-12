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

@[expose] public section

namespace Gabbro.Grammatik.Parser.Dyn
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- The shared phase theorem leaves concrete pass proofs to this consumer.
-- Activate the same local canonical operation equations here.
-- Keep partial large-fuel callbacks as functions. Only the canonical unfolding
-- equation of a fully applied operation may evaluate its selected AST node.
-- This covers the same visitor, collectors, inference and constant-cost reader
-- in every pass; no constructor, callback context or refusal is bypassed.
attribute [local cbv_opaque]
  Spec.Walk.expr Spec.Walk.type Spec.Walk.statement Spec.Walk.statements
  Spec.Walk.item Spec.Walk.constant Spec.resolveKnownBodies Spec.resolveKnownWith Spec.inferType Spec.inferTypeMit
  Spec.canonicalType Spec.expandEffects Uebersetze.sErsetze Uebersetze.uKonstEval
  SourceFolds.hasRangeFold SourceFolds.hasRangeFoldList SourceFolds.hasRangeFoldAnw SourceFolds.hasRangeFoldAnwList
  SourceFolds.tagFoldNodes SourceFolds.tagFoldNodesList SourceFolds.expandNested statementProducers
  statementsProducers statementUses statementsUses itemUses
  itemsUses lookup containsDynamic
attribute [local cbv_eval]
  Spec.Walk.expr.eq_def Spec.Walk.type.eq_def Spec.Walk.statement.eq_def
  Spec.Walk.statements.eq_def Spec.Walk.item.eq_def Spec.Walk.constant.eq_def
  Spec.resolveKnownBodies.eq_def Spec.resolveKnownWith.eq_def Spec.inferType.eq_def Spec.inferTypeMit.eq_def Spec.canonicalType.eq_def
  Spec.expandEffects.eq_def Uebersetze.sErsetze.eq_def Uebersetze.uKonstEval.eq_def
  SourceFolds.hasRangeFold.eq_def SourceFolds.hasRangeFoldList.eq_def SourceFolds.hasRangeFoldAnw.eq_def
  SourceFolds.hasRangeFoldAnwList.eq_def SourceFolds.tagFoldNodes.eq_def SourceFolds.tagFoldNodesList.eq_def
  SourceFolds.expandNested.eq_def statementProducers.eq_def statementsProducers.eq_def
  statementUses.eq_def statementsUses.eq_def itemUses.eq_def
  itemsUses.eq_def lookup.eq_def containsDynamic.eq_def
attribute [local cbv_eval] Spec.Walk.expr_literal Spec.Walk.type_atom

-- Source fixtures have their own namespace, distinct from the AST witnesses.
namespace SourceWitnessData

def source : String :=
  "table Circles count 4 { slot { r: u64, } } " ++
  "table Rects count 4 { slot { r: u64, } } " ++
  "spec Shape[T; effects E] { fn area(s: T) -> u64 " ++
  "ensures result >= 1 effects { E } costs <= 50 ops; } " ++
  "impl Shape[index into Circles; effects { reads Circles }] { " ++
  "fn area(s: index into Circles) -> u64 ensures result >= 1 " ++
  "effects { reads Circles } costs <= 20 ops { return 1; } } " ++
  "impl Shape[index into Rects; effects { reads Rects }] { " ++
  "fn area(s: index into Rects) -> u64 ensures result >= 1 " ++
  "effects { reads Rects } costs <= 20 ops { return 1; } } " ++
  "table Scene count 256 { slot { s: dyn Shape effects { reads Circles, reads Rects }, } } " ++
  "impl fn draw(c: index into Circles, i: index into Scene, j: index into Scene) -> u64 " ++
  "effects { reads Circles, reads Rects, reads Scene, writes Scene } costs <= 100 ops { " ++
  "Scene[i].s = dyn Shape(c); let a = Shape::area(Scene[j].s); return a; }"

-- Use the same lexer-error channel as the canonical source pipeline.
def parsed : Except String (List SItemTief) :=
  match lex source with
  | .error _ => .error "lex"
  | .ok tokens => parseTopTief tokens

def expanded : Except String (List SItemTief) := do
  exportDeclarationUnit (← parsed)

end SourceWitnessData

open SourceWitnessData

open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

private def characters0 : List Char :=
  ['t', 'a', 'b', 'l', 'e', ' ', 'C', 'i', 'r', 'c', 'l', 'e', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ',
   's', 'l', 'o', 't', ' ', '{', ' ', 'r', ':', ' ', 'u', '6', '4', ',', ' ', '}', ' ', '}', ' ']

private theorem lexed0 : (lexL characters0).toOption.isSome = true := by cbv

private def chunk0 : Chunk where
  characters := characters0
  tokens := ((lexL characters0).toOption.get lexed0).dropLast
  steps := ((lexL characters0).toOption.get lexed0).length - 1 +
    (characters0.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters1 : List Char :=
  ['t', 'a', 'b', 'l', 'e', ' ', 'R', 'e', 'c', 't', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ', 's', 'l',
   'o', 't', ' ', '{', ' ', 'r', ':', ' ', 'u', '6', '4', ',', ' ', '}', ' ', '}', ' ']

private theorem lexed1 : (lexL characters1).toOption.isSome = true := by cbv

private def chunk1 : Chunk where
  characters := characters1
  tokens := ((lexL characters1).toOption.get lexed1).dropLast
  steps := ((lexL characters1).toOption.get lexed1).length - 1 +
    (characters1.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters2 : List Char :=
  ['s', 'p', 'e', 'c', ' ', 'S', 'h', 'a', 'p', 'e', '[', 'T', ';', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', 'E', ']',
   ' ', '{', ' ', 'f', 'n', ' ', 'a', 'r', 'e', 'a', '(', 's', ':', ' ', 'T', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ']

private theorem lexed2 : (lexL characters2).toOption.isSome = true := by cbv

private def chunk2 : Chunk where
  characters := characters2
  tokens := ((lexL characters2).toOption.get lexed2).dropLast
  steps := ((lexL characters2).toOption.get lexed2).length - 1 +
    (characters2.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters3 : List Char :=
  ['e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '>', '=', ' ', '1', ' ', 'e', 'f', 'f', 'e',
   'c', 't', 's', ' ', '{', ' ', 'E', ' ', '}', ' ', 'c', 'o', 's', 't', 's', ' ', '<', '=', ' ', '5', '0', ' ', 'o', 'p',
   's', ';', ' ', '}', ' ']

private theorem lexed3 : (lexL characters3).toOption.isSome = true := by cbv

private def chunk3 : Chunk where
  characters := characters3
  tokens := ((lexL characters3).toOption.get lexed3).dropLast
  steps := ((lexL characters3).toOption.get lexed3).length - 1 +
    (characters3.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters4 : List Char :=
  ['i', 'm', 'p', 'l', ' ', 'S', 'h', 'a', 'p', 'e', '[', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'C', 'i',
   'r', 'c', 'l', 'e', 's', ';', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'C',
   'i', 'r', 'c', 'l', 'e', 's', ' ', '}', ']', ' ', '{', ' ']

private theorem lexed4 : (lexL characters4).toOption.isSome = true := by cbv

private def chunk4 : Chunk where
  characters := characters4
  tokens := ((lexL characters4).toOption.get lexed4).dropLast
  steps := ((lexL characters4).toOption.get lexed4).length - 1 +
    (characters4.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters5 : List Char :=
  ['f', 'n', ' ', 'a', 'r', 'e', 'a', '(', 's', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'C', 'i',
   'r', 'c', 'l', 'e', 's', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e',
   's', 'u', 'l', 't', ' ', '>', '=', ' ', '1', ' ']

private theorem lexed5 : (lexL characters5).toOption.isSome = true := by cbv

private def chunk5 : Chunk where
  characters := characters5
  tokens := ((lexL characters5).toOption.get lexed5).dropLast
  steps := ((lexL characters5).toOption.get lexed5).length - 1 +
    (characters5.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters6 : List Char :=
  ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'C', 'i', 'r', 'c', 'l', 'e', 's', ' ',
   '}', ' ', 'c', 'o', 's', 't', 's', ' ', '<', '=', ' ', '2', '0', ' ', 'o', 'p', 's', ' ', '{', ' ', 'r', 'e', 't', 'u',
   'r', 'n', ' ', '1', ';', ' ', '}', ' ', '}', ' ']

private theorem lexed6 : (lexL characters6).toOption.isSome = true := by cbv

private def chunk6 : Chunk where
  characters := characters6
  tokens := ((lexL characters6).toOption.get lexed6).dropLast
  steps := ((lexL characters6).toOption.get lexed6).length - 1 +
    (characters6.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters7 : List Char :=
  ['i', 'm', 'p', 'l', ' ', 'S', 'h', 'a', 'p', 'e', '[', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'R', 'e',
   'c', 't', 's', ';', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'R', 'e', 'c',
   't', 's', ' ', '}', ']', ' ', '{', ' ']

private theorem lexed7 : (lexL characters7).toOption.isSome = true := by cbv

private def chunk7 : Chunk where
  characters := characters7
  tokens := ((lexL characters7).toOption.get lexed7).dropLast
  steps := ((lexL characters7).toOption.get lexed7).length - 1 +
    (characters7.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters8 : List Char :=
  ['f', 'n', ' ', 'a', 'r', 'e', 'a', '(', 's', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'R', 'e',
   'c', 't', 's', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u',
   'l', 't', ' ', '>', '=', ' ', '1', ' ']

private theorem lexed8 : (lexL characters8).toOption.isSome = true := by cbv

private def chunk8 : Chunk where
  characters := characters8
  tokens := ((lexL characters8).toOption.get lexed8).dropLast
  steps := ((lexL characters8).toOption.get lexed8).length - 1 +
    (characters8.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters9 : List Char :=
  ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'R', 'e', 'c', 't', 's', ' ', '}', ' ',
   'c', 'o', 's', 't', 's', ' ', '<', '=', ' ', '2', '0', ' ', 'o', 'p', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n',
   ' ', '1', ';', ' ', '}', ' ', '}', ' ']

private theorem lexed9 : (lexL characters9).toOption.isSome = true := by cbv

private def chunk9 : Chunk where
  characters := characters9
  tokens := ((lexL characters9).toOption.get lexed9).dropLast
  steps := ((lexL characters9).toOption.get lexed9).length - 1 +
    (characters9.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters10 : List Char :=
  ['t', 'a', 'b', 'l', 'e', ' ', 'S', 'c', 'e', 'n', 'e', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', '5', '6', ' ', '{', ' ',
   's', 'l', 'o', 't', ' ', '{', ' ', 's', ':', ' ', 'd', 'y', 'n', ' ', 'S', 'h', 'a', 'p', 'e', ' ', 'e', 'f', 'f', 'e',
   'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'C', 'i', 'r', 'c', 'l', 'e', 's', ',', ' ', 'r', 'e', 'a',
   'd', 's', ' ', 'R', 'e', 'c', 't', 's', ' ', '}', ',', ' ', '}', ' ', '}', ' ']

private theorem lexed10 : (lexL characters10).toOption.isSome = true := by cbv

private def chunk10 : Chunk where
  characters := characters10
  tokens := ((lexL characters10).toOption.get lexed10).dropLast
  steps := ((lexL characters10).toOption.get lexed10).length - 1 +
    (characters10.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters11 : List Char :=
  ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'd', 'r', 'a', 'w', '(', 'c', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n',
   't', 'o', ' ', 'C', 'i', 'r', 'c', 'l', 'e', 's', ',', ' ', 'i', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't',
   'o', ' ', 'S', 'c', 'e', 'n', 'e', ',', ' ', 'j', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S',
   'c', 'e', 'n', 'e', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ']

private theorem lexed11 : (lexL characters11).toOption.isSome = true := by cbv

private def chunk11 : Chunk where
  characters := characters11
  tokens := ((lexL characters11).toOption.get lexed11).dropLast
  steps := ((lexL characters11).toOption.get lexed11).length - 1 +
    (characters11.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters12 : List Char :=
  ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'C', 'i', 'r', 'c', 'l', 'e', 's', ',',
   ' ', 'r', 'e', 'a', 'd', 's', ' ', 'R', 'e', 'c', 't', 's', ',', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'S', 'c', 'e', 'n',
   'e', ',', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'S', 'c', 'e', 'n', 'e', ' ', '}', ' ', 'c', 'o', 's', 't', 's', ' ',
   '<', '=', ' ', '1', '0', '0', ' ', 'o', 'p', 's', ' ', '{', ' ']

private theorem lexed12 : (lexL characters12).toOption.isSome = true := by cbv

private def chunk12 : Chunk where
  characters := characters12
  tokens := ((lexL characters12).toOption.get lexed12).dropLast
  steps := ((lexL characters12).toOption.get lexed12).length - 1 +
    (characters12.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def characters13 : List Char :=
  ['S', 'c', 'e', 'n', 'e', '[', 'i', ']', '.', 's', ' ', '=', ' ', 'd', 'y', 'n', ' ', 'S', 'h', 'a', 'p', 'e', '(', 'c',
   ')', ';', ' ', 'l', 'e', 't', ' ', 'a', ' ', '=', ' ', 'S', 'h', 'a', 'p', 'e', ':', ':', 'a', 'r', 'e', 'a', '(', 'S',
   'c', 'e', 'n', 'e', '[', 'j', ']', '.', 's', ')', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', ';', ' ', '}']

private theorem lexed13 : (lexL characters13).toOption.isSome = true := by cbv

private def chunk13 : Chunk where
  characters := characters13
  tokens := ((lexL characters13).toOption.get lexed13).dropLast
  steps := ((lexL characters13).toOption.get lexed13).length - 1 +
    (characters13.filter istLeer).length
  scanned := by intro rest remaining; cbv

private def chunks : List Chunk :=
  [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7, chunk8, chunk9, chunk10, chunk11, chunk12, chunk13]

-- The text is unchanged. Only this bridge handles its complete String value;
-- every scanner equation above retains an arbitrary suffix and remaining fuel.
private theorem source_text : source = String.ofList (characters chunks) := by cbv

private theorem lex_from_characters (text : String) (cs : List Char) (ts : List Token)
    (textEq : text = String.ofList cs) (scanned : lexL cs = .ok ts) :
    lex text = .ok ts := by
  rw [textEq, lex_ofList]
  exact scanned

private theorem source_lexed : lex source = .ok (tokens chunks) :=
  lex_from_characters source (characters chunks) (tokens chunks) source_text
    (lex_chunks chunks (by cbv))

private theorem parsed_from_phases {ts : List Token} {items : List SItemTief}
    (scanned : lex source = .ok ts) (read : parseTopTief ts = .ok items) :
    parsed = .ok items := by
  unfold parsed
  rw [scanned]
  exact read

-- Retain normalized data from each real phase, including the parsed input.
-- No later value contains a get that re-runs its producer chain.
private def source_items_result : { actual : List SItemTief // parseTopTief (tokens chunks) = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_items : List SItemTief := source_items_result.val
private theorem source_items_success :
    parseTopTief (tokens chunks) = .ok source_items := source_items_result.property

private theorem source_items_read : parsed = .ok source_items :=
  parsed_from_phases source_lexed source_items_success

private def source_fold_result : { actual : List SItemTief // SourceFolds.prepare source_items = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_fold_value : List SItemTief := source_fold_result.val
private theorem source_fold_success :
    SourceFolds.prepare source_items = .ok source_fold_value := source_fold_result.property

private def source_close_result : { actual : List Closed × List SItemTief // prepare source_fold_value = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_close_value : List Closed × List SItemTief := source_close_result.val
private theorem source_close_success :
    prepare source_fold_value = .ok source_close_value := source_close_result.property

private def source_tagged_result : { actual : List SItemTief × List String // exportTaggedUnitDetailed source_close_value.2 = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_tagged_value : List SItemTief × List String := source_tagged_result.val
private theorem source_tagged_success :
    exportTaggedUnitDetailed source_close_value.2 = .ok source_tagged_value := source_tagged_result.property

private def source_spec_result : { actual : List SItemTief // Spec.prepare (finish source_close_value.1 source_tagged_value.1) = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_spec_value : List SItemTief := source_spec_result.val
private theorem source_spec_success :
    Spec.prepare (finish source_close_value.1 source_tagged_value.1) = .ok source_spec_value := source_spec_result.property

private def source_checked_result : { actual : List SItemTief // checkedOutput source_tagged_value.1 source_spec_value = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_checked_value : List SItemTief := source_checked_result.val
private theorem source_checked_success :
    checkedOutput source_tagged_value.1 source_spec_value = .ok source_checked_value := source_checked_result.property

private def source_library_result : { actual : List SItemTief // exportLibraryUnit source_checked_value = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _
private def source_library_value : List SItemTief := source_library_result.val
private theorem source_library_success :
    exportLibraryUnit source_checked_value = .ok source_library_value := source_library_result.property

private theorem source_exported : exportDeclarationUnit source_items = .ok source_library_value := by
  exact export_from_phases (source := source_items) (folded := source_fold_value)
    (closed := source_close_value.1) (rewritten := source_close_value.2)
    (tagged := source_tagged_value.1) (names := source_tagged_value.2)
    (ordinary := source_spec_value) (validated := source_checked_value) (output := source_library_value)
    source_fold_success source_close_success source_tagged_success
    source_spec_success source_checked_success source_library_success

private theorem source_phases : ∃ items output,
    parsed = .ok items ∧ exportDeclarationUnit items = .ok output ∧
    (output.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) =
      [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] := by
  refine ⟨source_items, source_library_value, source_items_read, source_exported, ?sum⟩
  case sum => cbv

/-- Source text, lexer, parser and the actual front-end expansion agree on the closed cases. -/
public theorem dyn_source_scene_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) =
    .ok [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] := by
  rcases source_phases with ⟨items, output, read, emitted, sum⟩
  unfold expanded
  rw [read]
  dsimp only [bind, Except.bind]
  rw [emitted]
  exact congrArg Except.ok sum

public theorem dyn_producer_parser_zeuge :
    (parseTop [ .wort "dyn", .ident "Shape", .zeichen "(", .ident "c", .zeichen ")", .ende]) =
    .ok (.ext .dyn ["Shape"] [.variable "c"]) := by cbv

public theorem dyn_type_parser_zeuge :
    (parseTyp 100 [.wort "dyn", .ident "Shape", .wort "effects", .zeichen "{",
      .wort "reads", .ident "Circles", .zeichen "}", .ende]) =
    .ok (.dyn "Shape" (some "reads Circles } "), [.ende]) := by cbv

end Gabbro.Grammatik.Parser.Dyn
