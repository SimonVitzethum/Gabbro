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
import all Init.Data.String.Intercalate
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

namespace Gabbro.Grammatik.Parser.Uebersetze.ForWitness
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

def increment14 : List UStmt :=
  [.bind "#for-next" none (.add (.param "i") (.lit 1)),
   .narrowReqBeg "#for-next" 1 4, .setVar "i" (.param "#for-next")]

/-- A trailing `return` inside `while` ends the pass before the overflow block. -/
theorem while_early_exit_zeuge :
    exportLoop context "while true bounded LIMIT ops on_exceeded overrun"
      (.block [] (some (.ret none))) =
      .ok [.retryBeg 3 (.not .tru), .ret .empty, .ifElse, .axCall "overrun" [], .blkEnd] := by
  cbv

/-- A `while` with bound zero runs no pass and reaches the handler while the test holds. -/
theorem while_zero_bound_zeuge :
    exportLoop context "while true bounded 0 ops on_exceeded overrun" =
      .ok [.retryBeg 0 (.not .tru), .ifElse, .axCall "overrun" [], .blkEnd] := by
  cbv

/-- A `for` with `lo > hi` runs no pass: the binder keeps the swapped range, no handler. -/
theorem for_zero_trip_zeuge :
    exportLoop context "for i in 5 ..< 2" =
      .ok ([.ifBeg .tru, .bindMut "i" 2 5 (.lit 5),
        .retryBeg 0 (.not (.cmp "<" (.param "i") (.lit 2)))] ++
        [.bind "#for-next" none (.add (.param "i") (.lit 1)),
         .narrowReqBeg "#for-next" 2 5, .setVar "i" (.param "#for-next")] ++
        [.ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

/-- A `next i` ender completes the index increment before starting the next pass. -/
theorem for_next_call_zeuge :
    exportLoop context "for i in 1 ..< 4" (.block [.call "overrun" []] (some (.next "i"))) =
      .ok ([.ifBeg .tru, .bindMut "i" 1 4 (.lit 1),
        .retryBeg 3 (.not (.cmp "<" (.param "i") (.lit 4))), .axCall "overrun" []] ++
        increment14 ++ [.next "i"] ++ increment14 ++
        [.ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

/-- A `leave i` ender exits the loop without running the index increment. -/
theorem for_leave_zeuge :
    exportLoop context "for i in 1 ..< 4" (.block [] (some (.leave "i"))) =
      .ok ([.ifBeg .tru, .bindMut "i" 1 4 (.lit 1),
        .retryBeg 3 (.not (.cmp "<" (.param "i") (.lit 4))), .leave "i"] ++
        increment14 ++ [.ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

/-- A `for` inside a `for` elaborates both headers with their own binder and increment. -/
theorem for_nested_zeuge :
    exportLoop context "for i in 0 ..< 2"
      (.block [.boundedLoop "for j in 0 ..< 3" (.block [] none)] none) =
      .ok ([.ifBeg .tru, .bindMut "i" 0 2 (.lit 0),
        .retryBeg 2 (.not (.cmp "<" (.param "i") (.lit 2))),
        .ifBeg .tru, .bindMut "j" 0 3 (.lit 0),
        .retryBeg 3 (.not (.cmp "<" (.param "j") (.lit 3))),
        .bind "#for-next" none (.add (.param "j") (.lit 1)),
        .narrowReqBeg "#for-next" 0 3, .setVar "j" (.param "#for-next"),
        .ifElse, .blkEnd, .ifElse, .blkEnd,
        .bind "#for-next" none (.add (.param "i") (.lit 1)),
        .narrowReqBeg "#for-next" 0 2, .setVar "i" (.param "#for-next"),
        .ifElse, .blkEnd, .ifElse, .blkEnd]) := by
  cbv

/-- A body that writes the index elaborates once the named overflow handler is present. -/
theorem for_write_handler_zeuge :
    exportLoop context "for i in 0 ..< 2 on_exceeded overrun"
      (.block [.set (.variable "i") "=" (.lit 1)] none) =
      .ok ([.ifBeg .tru, .bindMut "i" 0 2 (.lit 0),
        .retryBeg 2 (.not (.cmp "<" (.param "i") (.lit 2))),
        .setVar "i" (.lit 1),
        .bind "#for-next" none (.add (.param "i") (.lit 1)),
        .narrowReqBeg "#for-next" 0 2, .setVar "i" (.param "#for-next"),
        .ifElse, .axCall "overrun" [], .blkEnd, .ifElse, .blkEnd]) := by
  cbv

/-- A body that writes the index without `on_exceeded` is refused by name. -/
theorem for_write_refused_zeuge :
    exportLoop context "for i in 0 ..< 2"
      (.block [.set (.variable "i") "=" (.lit 1)] none) =
      .error "for.on_exceeded.required-for-index-write" := by
  cbv

/-- A nested `for` over the same binder is refused as shadowing before elaboration. -/
theorem for_shadow_refused_zeuge :
    exportLoop context "for i in 0 ..< 2"
      (.block [.boundedLoop "for i in 0 ..< 1" (.block [] none)] none) =
      .error "for.index.shadowed" := by
  cbv

end Gabbro.Grammatik.Parser.Uebersetze.ForWitness
