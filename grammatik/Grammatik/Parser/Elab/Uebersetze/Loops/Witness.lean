module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import Lean.Elab.Tactic.Cbv
public import Grammatik.Parser.Stmt.Anweisung.BoundedWitness
import all Grammatik.Parser.Elab.Uebersetze.Loops.Bounded
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Kontext.Bindings

import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
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

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze.BoundedWitness
attribute [local cbv_eval] strEq_apply_eq_decide

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def context : UCtx :=
  { names := []
    kinds := []
    types := []
    tabs := []
    locks := []
    held := []
    res := none
    fname := "sample"
    alias := []
    lits := [("LIMIT", 3)] }

def overflowHead : UFnKopf :=
  { name := "overrun"
    names := []
    kinds := []
    types := []
    res := none
    held := []
    ext := true }

/-- The real recursive source exporter, projected to its small decidable code list. -/
def exportLoop (ctx : UCtx) (raw : String) (body : SAnw := .block [] none) :
    Except String (List UStmt) :=
  (uAnwReihe [] [overflowHead] 20 ctx [.boundedLoop raw body]).map (·.1)

theorem while_export_zeuge :
    exportLoop context "while true bounded LIMIT ops on_exceeded overrun" =
      .ok [.retryBeg 3 (.not .tru), .ifElse, .axCall "overrun" [], .blkEnd] := by
  cbv

theorem nonstatic_bound_refused_zeuge :
    exportLoop { context with
      names := ["LIMIT"]
      kinds := [.int]
      types := [.int 3 3]
      bits := [64] } "while true bounded LIMIT ops on_exceeded overrun" =
      .error "while.bound.static-natural-required" := by
  cbv

theorem negative_bound_refused_zeuge :
    exportLoop context "while true bounded -1 ops on_exceeded overrun" =
      .error "while.bound.static-natural-required" := by
  cbv

theorem noninteger_range_refused_zeuge :
    exportLoop context "for i in 0 ..< 1.5" = .error "for.range.static-integer-required" ∧
    exportLoop context "for i in false ..< 3" = .error "for.range.static-integer-required" := by
  cbv

def increment : List UStmt :=
  [.bind "#for-next" none (.add (.param "i") (.lit 1)),
   .narrowReqBeg "#for-next" 1 4, .setVar "i" (.param "#for-next")]

theorem for_export_zeuge :
    exportLoop context "for i in 1 ..< 4" =
      .ok ([.ifBeg .tru, .bindMut "i" 1 4 (.lit 1),
        .retryBeg 3 (.not (.cmp "<" (.param "i") (.lit 4)))] ++ increment ++
        [.ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

theorem for_next_zeuge :
    exportLoop context "for i in 1 ..< 4" (.block [] (some (.next "i"))) =
      .ok ([.ifBeg .tru, .bindMut "i" 1 4 (.lit 1),
        .retryBeg 3 (.not (.cmp "<" (.param "i") (.lit 4)))] ++ increment ++ [.next "i"] ++
        increment ++ [.ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

theorem index_write_needs_handler_zeuge :
    exportLoop context "for i in 1 ..< 4" (.block [.set (.variable "i") "=" (.lit 1)] none) =
      .error "for.on_exceeded.required-for-index-write" := by
  cbv

theorem index_shadowing_refused_zeuge :
    exportLoop context "for i in 1 ..< 4 on_exceeded overrun"
      (.block [.bind false "i" none (.lit 1)] none) = .error "for.index.shadowed" := by
  cbv

/-- An indexed store reads i; a foreign-call failure body can actually write it. -/
theorem index_effects_zeuge :
    uForIndexEffects 10 "i" (.set (.index (.variable "T") (.variable "i")) "=" (.lit 0)) =
      (false, false) ∧
    uForIndexEffects 10 "i" (.bindAxiomOptElse "x" none (.call "f" []) "reason"
      (.block [.set (.variable "i") "=" (.lit 0)] none)) = (false, true) := by
  cbv

/-- The range binder ends before the subsequent statements are elaborated. -/
theorem for_scope_zeuge :
    (uAnwReihe [] [overflowHead] 20 context [.boundedLoop "for i in 1 ..< 4" (.block [] none)]).map
      (fun pair => pair.2.names) = .ok [] := by
  cbv

end Gabbro.Grammatik.Parser.Uebersetze.BoundedWitness
