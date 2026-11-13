module

public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardMutable
public import Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
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
import all Grammatik.Parser.Elab.Uebersetze.Kontext.GuardNarrowing
import all Grammatik.Parser.Elab.Uebersetze.Kontext.GuardRelation
import all Grammatik.Parser.Elab.Uebersetze.Kontext.GuardMutable
import all Grammatik.Parser.Elab.Uebersetze.Narrowing

/-! Witnesses of block-local mutable snapshots. The callback reads bindings and assignment values as
ordinary body values; a nested conditional is recorded without recursing into it. The block-walk witnesses
also compare the surface trees, so a barrier cannot pass merely because the callback ignores a form. -/

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze.GuardMutableWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- One mutable number `b : u32 in 0 .. 20`, narrowing on. -/
def context : UCtx :=
  {names := ["b"], kinds := [.int], types := [.int 0 20], tabs := [], locks := [], held := [],
   res := some (0, 100), fname := "sample", alias := [], lits := [], bits := [32], muts := ["b"],
   narrow := true}

def b : SExpr := .variable "b"
def lt20 : SExpr := .bin "<" b (.lit 20)
def increment : SAnw := .set b "=" (.bin "+" b (.lit 1))
def readB : SAnw := .bind false "seen" none b
def nested : SAnw := .cond (.bin "<" b (.lit 10)) (.block [.set b "=" (.lit 0)] none) [] none

/-- Record the values of the straight-line fixture; a nested if is an opaque marker. -/
def reader (ctx : UCtx) (ss : List SAnw) : Except String (List UStmt × UCtx) :=
  (uSeq (ss.map (fun (s : SAnw) => (match s with
    | .bind _ x _ v => (uWertBody ctx v).map (UStmt.bind x none)
    | .set (.variable x) "=" v => (uWertBody ctx v).map (UStmt.setVar x)
    | .cond .. => .ok (UStmt.bind "nested" none (.lit 0))
    | _ => .error "not a fixture statement" : Except String UStmt)))).map (fun xs => (xs, ctx))

def stmts (r : Except String (List UStmt × UCtx)) : Except String (List UStmt) := r.map (·.1)

/-- The counter: the original target `b` receives `#mut:b + 1`, whose range is `1 .. 20`.
    The binding precedes the assignment; `b` is never rebound at a smaller declared range. -/
public theorem mutable_counter_zeuge :
    stmts (uCond reader context lt20 [increment] none [] none []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)),
        UStmt.bind "#mut:b" (some (0, 19)) (.eng (.param "b") 0 19),
        UStmt.setVar "b" (.add (.param "#mut:b") (.lit 1)),
        UStmt.ifElse, UStmt.blkEnd] := by cbv

/-- The first assignment's value is replaced; a later read, assignment and block ending keep `b`. -/
public theorem mutable_after_assignment_zeuge :
    uMutErsetzeL "b" "#mut:b" [readB, increment, readB, increment] =
      ([.bind false "seen" none (.variable "#mut:b"),
        .set b "=" (.bin "+" (.variable "#mut:b") (.lit 1)), readB, increment], false) ∧
      stmts (uCond reader context lt20 [increment, readB] (some (.ret (some b))) [] none []) =
        .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)),
          UStmt.bind "#mut:b" (some (0, 19)) (.eng (.param "b") 0 19),
          UStmt.setVar "b" (.add (.param "#mut:b") (.lit 1)),
          UStmt.bind "seen" none (.param "b"),
          UStmt.ret (.val (.param "b")), UStmt.ifElse, UStmt.blkEnd] := by
  constructor <;> cbv

/-- A nested if as the first statement is a barrier: no snapshot, no rewrite inside it or after it. -/
public theorem mutable_nested_first_zeuge :
    uMutBlock context [("b", 0, 19)] [nested, readB] (some (.ret (some b))) =
      ([], context, [nested, readB], some (.ret (some b))) := by cbv

/-- A plain else block gets the negated fact: `b >= 1` makes `b - 1` fit `0 .. 20`. -/
public theorem mutable_else_zeuge :
    stmts (uCond reader context (.bin "<" b (.lit 1)) [] none []
        (some (.block [.set b "=" (.bin "-" b (.lit 1))] none)) []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 1)), UStmt.ifElse,
        UStmt.bind "#mut:b" (some (1, 20)) (.eng (.param "b") 1 20),
        UStmt.setVar "b" (.sub (.param "#mut:b") (.lit 1)), UStmt.blkEnd] := by cbv

/-- An else-if chain receives no snapshot from the outer guard, including its final else block.
    The callback records the nested conditional without processing its own independent guard. -/
public theorem mutable_else_if_zeuge :
    stmts (uCond reader context lt20 [] none [.elsif (.bin "<" b (.lit 10)) (.block [readB] none)]
        (some (.block [readB] none)) []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)), UStmt.ifElse,
        UStmt.bind "nested" none (.lit 0), UStmt.blkEnd] := by cbv

/-- Even an always-returning then block gives no mutable fact to the continuation. The else assignment
    witnesses why: the guard's false-path singleton `20 .. 20` no longer describes `b` after that block. -/
public theorem mutable_continuation_zeuge :
    stmts (uCond reader context lt20 [] (some (.ret (some (.lit 0)))) []
        (some (.block [.set b "=" (.lit 0)] none)) [readB]) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)), UStmt.ret (.val (.lit 0)),
        UStmt.ifElse, UStmt.setVar "b" (.lit 0), UStmt.blkEnd,
        UStmt.bind "seen" none (.param "b")] := by cbv

/-- The continuation gets no mutable fact even without an else block that could assign the local. -/
public theorem mutable_continuation_without_else_zeuge :
    stmts (uCond reader context lt20 [] (some (.ret (some (.lit 0)))) [] none [readB]) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)), UStmt.ret (.val (.lit 0)),
        UStmt.ifElse, UStmt.blkEnd, UStmt.bind "seen" none (.param "b")] := by cbv

/-- A return value alone is a pre-assignment read and gets a snapshot. -/
public theorem mutable_return_snapshot_zeuge :
    stmts (uCond reader context lt20 [] (some (.ret (some b))) [] none []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)),
        UStmt.bind "#mut:b" (some (0, 19)) (.eng (.param "b") 0 19),
        UStmt.ret (.val (.param "#mut:b")), UStmt.ifElse, UStmt.blkEnd] := by cbv

/-- Without narrowing, both assignment values keep their original local reads. -/
public theorem mutable_switch_off_zeuge :
    stmts (uCond reader {context with narrow := false} lt20 [increment] none []
        (some (.block [increment] none)) [readB]) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)),
        UStmt.setVar "b" (.add (.param "b") (.lit 1)), UStmt.ifElse,
        UStmt.setVar "b" (.add (.param "b") (.lit 1)), UStmt.blkEnd,
        UStmt.bind "seen" none (.param "b")] := by cbv

/-- An immutable local still uses the original rebinding and early-return continuation rule. -/
public theorem immutable_unchanged_zeuge :
    stmts (uCond reader {context with muts := []} lt20 [readB] (some (.ret (some (.lit 0)))) []
        (some (.block [readB] none)) [readB]) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "b") (.lit 20)),
        UStmt.bind "b" (some (0, 19)) (.eng (.param "b") 0 19),
        UStmt.bind "seen" none (.param "b"), UStmt.ret (.val (.lit 0)), UStmt.ifElse,
        UStmt.bind "b" (some (20, 20)) (.eng (.param "b") 20 20),
        UStmt.bind "seen" none (.param "b"), UStmt.blkEnd,
        UStmt.bind "b" (some (20, 20)) (.eng (.param "b") 20 20),
        UStmt.bind "seen" none (.param "b")] := by cbv

/-- No read before the first assignment: no fresh binding, even though a later statement reads `b`. -/
public theorem mutable_unread_before_assignment_zeuge :
    uMutBlock context [("b", 0, 19)] [.set b "=" (.lit 0), readB] none =
      ([], context, [.set b "=" (.lit 0), readB], none) := by cbv

/-- Rebinding, compound assignment, a raw statement and a loop each stop before the statement itself. -/
public theorem mutable_barriers_zeuge :
    uMutErsetzeL "b" "#mut:b" [.bind false "b" none b, readB] =
        ([.bind false "b" none b, readB], false) ∧
      uMutErsetzeL "b" "#mut:b" [.set b "+=" b, readB] = ([.set b "+=" b, readB], false) ∧
      uMutErsetzeL "b" "#mut:b" [.other "raw", readB] = ([.other "raw", readB], false) ∧
      uMutErsetzeL "b" "#mut:b" [.loop "again" (.block [readB, increment] none), readB] =
        ([.loop "again" (.block [readB, increment] none), readB], false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

/-- Mutable fact extraction reuses unary guard facts, excluding deferred ranges and relational facts. -/
public theorem mutable_facts_zeuge :
    uMutFakten context (.cmp "<" (.param "b") (.lit 20)) true = [("b", 0, 19)] ∧
      uMutFakten context (.cmp "<" (.param "b") (.lit 20)) false = [("b", 20, 20)] ∧
      uMutFakten {context with unknownRanges := ["b"]} (.cmp "<" (.param "b") (.lit 20)) true = [] ∧
      uWaechterFakten context (.cmp "<" (.param "b") (.lit 20)) true = [] ∧
      uRelFakten context (.cmp "<" (.param "b") (.param "b")) true = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cbv

/-- The snapshot retains 32 bits; the original local is still mutable at its declared range. -/
public theorem mutable_context_zeuge :
    (uMutBindung context "b" 0 19).2.bits = [32, 32] ∧
      (uMutBindung context "b" 0 19).2.muts = ["b"] ∧
      (uMutBindung context "b" 0 19).2.names = ["#mut:b", "b"] ∧
      (uMutBindung context "b" 0 19).2.types = [.int 0 19, .int 0 20] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

end Gabbro.Grammatik.Parser.Uebersetze.GuardMutableWitness
