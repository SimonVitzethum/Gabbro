module

public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardNarrowing
public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardRelation
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
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
import all Grammatik.Parser.Elab.Uebersetze.Narrowing

/-
  Witnesses of the narrowing by the guarding condition (`uCond`, `uCondGuard`, `uWaechterFakten`): the
  reader of a block is a probe that reports the range its context gives the local `i`, so each witness shows
  the range a branch reads `i` at, in the statements the condition produces. The narrowing is on in `context`
  (`UCtx.narrow`, as the Stage-0 compiler sets it) and off by default; a block narrows only the locals it reads,
  so the blocks below read `i` (`useI`) or only another name (`useK`).
-/
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze.GuardWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- One parameter `i : u32 in 0 .. 100`, narrowing on. -/
def context : UCtx :=
  {names := ["i"], kinds := [.int], types := [.int 0 100], tabs := [], locks := [], held := [],
   res := none, fname := "sample", alias := [], lits := [], bits := [32], narrow := true}

/-- Two parameters, `i : u32 in 0 .. 100` and `j : u32 in 0 .. 50`. -/
def context2 : UCtx :=
  {context with names := ["i", "j"], kinds := [.int, .int], types := [.int 0 100, .int 0 50],
                bits := [32, 32]}

/-- The reader of a block: the statement `seen` records the range the block's context gives `i`. -/
def seen (ctx : UCtx) (_ : List SAnw) : Except String (List UStmt × UCtx) :=
  match uParamNr ctx "i" with
  | .error e => .error e
  | .ok j =>
    match ctx.types[j]? with
    | some (.int lo hi) => .ok ([UStmt.bind "seen" (some (lo, hi)) (.param "i")], ctx)
    | _ => .error "not a number"

/-- The statements of a result, without the context. -/
def stmts (r : Except String (List UStmt × UCtx)) : Except String (List UStmt) := r.map (·.1)

def lt10 : SExpr := .bin "<" (.variable "i") (.lit 10)
def ge10 : SExpr := .bin ">=" (.variable "i") (.lit 10)
def lt200 : SExpr := .bin "<" (.variable "i") (.lit 200)
def between : SExpr :=
  .bin "&&" (.bin ">=" (.variable "i") (.lit 5)) (.bin "<" (.variable "i") (.lit 10))
/-- A block that reads `i`, and one that reads only `k`. -/
def useI : List SAnw := [.call "use" [.variable "i"]]
def useK : List SAnw := [.call "use" [.variable "k"]]
def elseI : Option SAnw := some (.block useI .none)
def elseK : Option SAnw := some (.block useK .none)

/-- `if i < 10 { .. } else { .. }`: the then block reads `i` at `0 .. 9`, the `else` block at `10 .. 100`,
    the continuation (the then block does not end) at the declared range. Each branch starts with the value
    form `eng`, no `else`, no new return path. -/
public theorem guard_then_else_zeuge :
    stmts (uCond seen context lt10 useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "i") (.lit 10)),
        UStmt.bind "i" (some (0, 9)) (.eng (.param "i") 0 9),
        UStmt.bind "seen" (some (0, 9)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "i" (some (10, 100)) (.eng (.param "i") 10 100),
        UStmt.bind "seen" (some (10, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- The same source with the narrowing off (the default: the canonical exporter and the read-back): no
    rebinding, every block reads `i` at the declared range. The switch alone decides. -/
public theorem guard_switch_off_zeuge :
    stmts (uCond seen {context with narrow := false} lt10 useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "i") (.lit 10)),
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- The switch matters: on, the source `if i < 10 { use(i) } else { use(i) } use(i)` starts each branch with the
    rebinding of `i`; off, it does not. -/
public theorem guard_switch_zeuge :
    stmts (uCond seen context lt10 useI none [] elseI useI) ≠
      stmts (uCond seen {context with narrow := false} lt10 useI none [] elseI useI) := by
  rw [guard_then_else_zeuge, guard_switch_off_zeuge]
  intro h
  injection h with h
  exact absurd (congrArg List.length h) (by decide)

/-- A `let mut` local gets no fact: the result is the plain reading of the branches. -/
public theorem guard_mutable_no_fact_zeuge :
    stmts (uCond seen {context with muts := ["i"]} lt10 useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "i") (.lit 10)),
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- An untyped local whose range is deferred (`unknownRanges`) gets no fact either. -/
public theorem guard_unknown_range_no_fact_zeuge :
    stmts (uCond seen {context with unknownRanges := ["i"]} lt10 useI none [] elseI useI) =
      stmts (uCondPlain seen {context with unknownRanges := ["i"]} lt10 useI none [] elseI useI) := by cbv

/-- A condition that bounds nothing (`i < 200` holds for every `i`, its negation for none): the result is
    exactly the old reading. -/
public theorem guard_bounds_nothing_zeuge :
    stmts (uCond seen context lt200 useI none [] elseI useI) =
      stmts (uCondPlain seen context lt200 useI none [] elseI useI) := by cbv

/-- A condition whose facts concern a local that no block reads (each block reads only `k`): the result is
    exactly the old reading, no range test is added. -/
public theorem guard_unread_plain_zeuge :
    stmts (uCond seen context lt10 useK none [] elseK useK) =
      stmts (uCondPlain seen context lt10 useK none [] elseK useK) := by cbv

/-- Only the block that reads `i` narrows it: the then block reads `i`, the `else` block and the
    continuation read only `k`, so only the then block starts with the rebinding. -/
public theorem guard_read_then_only_zeuge :
    stmts (uCond seen context lt10 useI none [] elseK useK) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "i") (.lit 10)),
        UStmt.bind "i" (some (0, 9)) (.eng (.param "i") 0 9),
        UStmt.bind "seen" (some (0, 9)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- A conjunction narrows the then block to the intersection (`5 .. 9`); its negation says nothing, so the
    `else` block keeps the declared range. -/
public theorem guard_conjunction_zeuge :
    stmts (uCond seen context between useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.and (.cmp ">=" (.param "i") (.lit 5)) (.cmp "<" (.param "i") (.lit 10))),
        UStmt.bind "i" (some (5, 9)) (.eng (.param "i") 5 9),
        UStmt.bind "seen" (some (5, 9)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- `if i >= 10 { use(i); return; } use(i);`: the then block reads `i` at `10 .. 100`, and because it always
    ends, the continuation reads `i` at `0 .. 9`. -/
public theorem guard_after_return_zeuge :
    stmts (uCond seen context ge10 useI (some (.ret none)) [] none useI) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "i") (.lit 10)),
        UStmt.bind "i" (some (10, 100)) (.eng (.param "i") 10 100),
        UStmt.bind "seen" (some (10, 100)) (.param "i"),
        UStmt.ret .empty,
        UStmt.ifElse,
        UStmt.blkEnd,
        UStmt.bind "i" (some (0, 9)) (.eng (.param "i") 0 9),
        UStmt.bind "seen" (some (0, 9)) (.param "i")] := by cbv

/-- Without an early end the continuation keeps the declared range. -/
public theorem guard_no_early_end_zeuge :
    stmts (uCond seen context ge10 useI none [] none useI) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "i") (.lit 10)),
        UStmt.bind "i" (some (10, 100)) (.eng (.param "i") 10 100),
        UStmt.bind "seen" (some (10, 100)) (.param "i"),
        UStmt.ifElse,
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- The other side may be another immutable number local, read at its declared range: `i < j` bounds `i` by
    `j`'s top and `j` by `i`'s bottom. -/
public theorem guard_side_local_zeuge :
    uWaechterFakten context2 (.cmp "<" (.param "i") (.param "j")) true =
      [("i", 0, 49), ("j", 1, 50)] := by cbv

/-- The read walk: a statement mentions the names it reads, nested blocks and endings included; a raw
    statement stands for every name. -/
public theorem guard_reads_zeuge :
    uLiestL [.cond (.bin "<" (.variable "a") (.lit 1)) (.block [.set (.variable "b") "=" (.variable "c")]
        (some (.ret (some (.variable "d"))))) [] none] = ["a", "b", "c", "d"] ∧
      uGelesen (uLiestL [.other "raw"]) "x" = true := by
  constructor <;> cbv

/-! ### Relational facts between two locals (`uRelFakten`, `uRelBlock`)

The reader of a block elaborates each `let x = e;` as a body value (`uWertBody`) in the block's context, so each
witness shows the value a block reads: a difference the facts bound is read as the fresh local `#rel:p:q`, bound
once at the start of the block to the difference narrowed to the bound (`USide.eng`, no `else`). -/

/-- Two parameters `a, b : u32 in 0 .. 100` and a result `0 .. 100`, narrowing on. -/
def relContext : UCtx :=
  {names := ["a", "b"], kinds := [.int, .int], types := [.int 0 100, .int 0 100], tabs := [], locks := [],
   held := [], res := some (0, 100), fname := "sample", alias := [], lits := [], bits := [32, 32],
   narrow := true}

/-- The reader of a block: each `let x = e;` as `UStmt.bind x none <e as a body value>`. -/
def relReader (ctx : UCtx) (ss : List SAnw) : Except String (List UStmt × UCtx) :=
  (uSeq (ss.map (fun (s : SAnw) => (match s with
    | .bind _ x _ v => (uWertBody ctx v).map (UStmt.bind x none)
    | _ => .error "not a binding" : Except String UStmt)))).map (fun xs => (xs, ctx))

def relA : SExpr := .variable "a"
def relB : SExpr := .variable "b"
def relAminusB : SExpr := .bin "-" relA relB

/-- The facts of `a > b`, of its negation, and of a conjunction with a literal comparison (which relates
    nothing). -/
public theorem relation_facts_zeuge :
    uRelFakten relContext (.cmp ">" (.param "a") (.param "b")) true = [("a", "b", 1)] ∧
      uRelFakten relContext (.cmp ">" (.param "a") (.param "b")) false = [("b", "a", 0)] ∧
      uRelFakten relContext (.and (.cmp "<" (.param "a") (.param "b")) (.cmp "==" (.param "a") (.lit 3))) true =
        [("b", "a", 1)] := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- `if a >= b { return a - b; }`: the then block returns `#rel:a:b`, bound to `a - b` narrowed to `0 .. 100`
    (the declared ranges alone give `-100 .. 100`); the then block always ends, so the continuation reads `a` at
    `0 .. 99` and `b` at `1 .. 100`. -/
public theorem relation_return_zeuge :
    stmts (uCond relReader relContext (.bin ">=" relA relB) [] (some (.ret (some relAminusB))) [] none []) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "a") (.param "b")),
        UStmt.bind "#rel:a:b" (some (0, 100)) (.eng (.sub (.param "a") (.param "b")) 0 100),
        UStmt.ret (.val (.param "#rel:a:b")),
        UStmt.ifElse,
        UStmt.blkEnd,
        UStmt.bind "a" (some (0, 99)) (.eng (.param "a") 0 99),
        UStmt.bind "b" (some (1, 100)) (.eng (.param "b") 1 100)] := by cbv

/-- `if a > b { let d = a - b - 1; }`: after the unary rebindings (`a` at `1 .. 100`, `b` at `0 .. 99`) the
    difference is bound at `1 .. 100` (the ranges alone give `-98 .. 100`), so `d` is `#rel:a:b - 1`, at least 0. -/
public theorem relation_offset_zeuge :
    stmts (uCond relReader relContext (.bin ">" relA relB)
        [.bind false "d" none (.bin "-" relAminusB (.lit 1))] none [] none []) =
      .ok [UStmt.ifBeg (.cmp ">" (.param "a") (.param "b")),
        UStmt.bind "a" (some (1, 100)) (.eng (.param "a") 1 100),
        UStmt.bind "b" (some (0, 99)) (.eng (.param "b") 0 99),
        UStmt.bind "#rel:a:b" (some (1, 100)) (.eng (.sub (.param "a") (.param "b")) 1 100),
        UStmt.bind "d" none (.sub (.param "#rel:a:b") (.lit 1)),
        UStmt.ifElse,
        UStmt.blkEnd] := by cbv

/-- `if a < b { let r = b - a; }` (the shape `if i < n { let rest = n - i; }`): `b - a` is bound at `1 .. 100`. -/
public theorem relation_rest_zeuge :
    stmts (uCond relReader relContext (.bin "<" relA relB) [.bind false "r" none (.bin "-" relB relA)]
        none [] none []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "a") (.param "b")),
        UStmt.bind "a" (some (0, 99)) (.eng (.param "a") 0 99),
        UStmt.bind "b" (some (1, 100)) (.eng (.param "b") 1 100),
        UStmt.bind "#rel:b:a" (some (1, 100)) (.eng (.sub (.param "b") (.param "a")) 1 100),
        UStmt.bind "r" none (.param "#rel:b:a"),
        UStmt.ifElse,
        UStmt.blkEnd] := by cbv

/-- The `else` block gets the facts of the negation: `if a < b { } else { let r = a - b; }` binds `a - b` at
    `0 .. 100` at the start of the `else` block. -/
public theorem relation_else_zeuge :
    stmts (uCond relReader relContext (.bin "<" relA relB) [] none []
        (some (.block [.bind false "r" none relAminusB] none)) []) =
      .ok [UStmt.ifBeg (.cmp "<" (.param "a") (.param "b")),
        UStmt.ifElse,
        UStmt.bind "#rel:a:b" (some (0, 100)) (.eng (.sub (.param "a") (.param "b")) 0 100),
        UStmt.bind "r" none (.param "#rel:a:b"),
        UStmt.blkEnd] := by cbv

/-- A rebinding drops the fact: in `if a >= b { let c = a - b; let a = 5; let d = a - b; }` only the
    difference before `let a` is read as `#rel:a:b`; from the rebinding on the block keeps its text. -/
public theorem relation_rebound_zeuge :
    stmts (uCond relReader relContext (.bin ">=" relA relB)
        [.bind false "c" none relAminusB, .bind false "a" none (.lit 5), .bind false "d" none relAminusB]
        none [] none []) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "a") (.param "b")),
        UStmt.bind "#rel:a:b" (some (0, 100)) (.eng (.sub (.param "a") (.param "b")) 0 100),
        UStmt.bind "c" none (.param "#rel:a:b"),
        UStmt.bind "a" none (.lit 5),
        UStmt.bind "d" none (.sub (.param "a") (.param "b")),
        UStmt.ifElse,
        UStmt.blkEnd] := by cbv

/-- A `let mut` operand gives no fact: `if a >= b { return a - b; }` with `a` mutable is the plain reading, the
    difference keeps its declared range `-100 .. 100` (and lowering refuses it against the result). -/
public theorem relation_mutable_no_fact_zeuge :
    stmts (uCond relReader {relContext with muts := ["a"]} (.bin ">=" relA relB) []
        (some (.ret (some relAminusB))) [] none []) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "a") (.param "b")),
        UStmt.ret (.val (.sub (.param "a") (.param "b"))),
        UStmt.ifElse,
        UStmt.blkEnd] := by cbv

/-- With the switch off the same source is the old reading: no fresh local, no rebinding. -/
public theorem relation_switch_off_zeuge :
    stmts (uCond relReader {relContext with narrow := false} (.bin ">=" relA relB) []
        (some (.ret (some relAminusB))) [] none []) =
      .ok [UStmt.ifBeg (.cmp ">=" (.param "a") (.param "b")),
        UStmt.ret (.val (.sub (.param "a") (.param "b"))),
        UStmt.ifElse,
        UStmt.blkEnd] := by cbv

/-! ### Equality guards and inclusive range endpoints -/

/-- `if i == 0 { use(i); return; } use(i);`: equality fixes the then value, and its failure excludes
    the lower endpoint in the continuation, which can only be reached after the condition failed. -/
public theorem guard_equality_after_return_zeuge :
    stmts (uCond seen context (.bin "==" (.variable "i") (.lit 0)) useI (some (.ret none)) [] none useI) =
      .ok [UStmt.ifBeg (.cmp "==" (.param "i") (.lit 0)),
        UStmt.bind "i" (some (0, 0)) (.eng (.param "i") 0 0),
        UStmt.bind "seen" (some (0, 0)) (.param "i"),
        UStmt.ret .empty,
        UStmt.ifElse,
        UStmt.blkEnd,
        UStmt.bind "i" (some (1, 100)) (.eng (.param "i") 1 100),
        UStmt.bind "seen" (some (1, 100)) (.param "i")] := by cbv

/-- `i != 100` excludes the upper endpoint in the then block; its failure fixes the else value. -/
public theorem guard_inequality_upper_zeuge :
    stmts (uCond seen context (.bin "!=" (.variable "i") (.lit 100)) useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.cmp "!=" (.param "i") (.lit 100)),
        UStmt.bind "i" (some (0, 99)) (.eng (.param "i") 0 99),
        UStmt.bind "seen" (some (0, 99)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "i" (some (100, 100)) (.eng (.param "i") 100 100),
        UStmt.bind "seen" (some (100, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- Equality to an interior value gives a singleton in the then block and no fact in the else block:
    an interval cannot express the hole at 50. The continuation has no early-end fact either. -/
public theorem guard_equality_middle_zeuge :
    stmts (uCond seen context (.bin "==" (.variable "i") (.lit 50)) useI none [] elseI useI) =
      .ok [UStmt.ifBeg (.cmp "==" (.param "i") (.lit 50)),
        UStmt.bind "i" (some (50, 50)) (.eng (.param "i") 50 50),
        UStmt.bind "seen" (some (50, 50)) (.param "i"),
        UStmt.ifElse,
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- The equality source with the switch off keeps the plain reading, including after an early return. -/
public theorem guard_equality_switch_off_zeuge :
    stmts (uCond seen {context with narrow := false} (.bin "==" (.variable "i") (.lit 0))
        useI (some (.ret none)) [] none useI) =
      .ok [UStmt.ifBeg (.cmp "==" (.param "i") (.lit 0)),
        UStmt.bind "seen" (some (0, 100)) (.param "i"),
        UStmt.ret .empty,
        UStmt.ifElse,
        UStmt.blkEnd,
        UStmt.bind "seen" (some (0, 100)) (.param "i")] := by cbv

/-- All four polarities at the lower and upper endpoints, interior exclusion, an impossible equality,
    reversed operands and negation. The order is the order of the guard's local names. -/
public theorem guard_equality_facts_zeuge :
    ([ (.cmp "==" (.param "i") (.lit 0), true),
       (.cmp "==" (.param "i") (.lit 0), false),
       (.cmp "!=" (.param "i") (.lit 0), true),
       (.cmp "!=" (.param "i") (.lit 0), false),
       (.cmp "==" (.param "i") (.lit 100), true),
       (.cmp "==" (.param "i") (.lit 100), false),
       (.cmp "!=" (.param "i") (.lit 100), true),
       (.cmp "!=" (.param "i") (.lit 100), false),
       (.cmp "==" (.param "i") (.lit 50), false),
       (.cmp "!=" (.param "i") (.lit 50), true),
       (.cmp "==" (.param "i") (.lit 101), true),
       (.cmp "==" (.lit 0) (.param "i"), false),
       (.not (.cmp "==" (.param "i") (.lit 100)), true) ] : List (UEns × Bool)).map
        (fun g => uWaechterFakten context g.1 g.2) =
      [[("i", 0, 0)], [("i", 1, 100)], [("i", 1, 100)], [("i", 0, 0)],
       [("i", 100, 100)], [("i", 0, 99)], [("i", 0, 99)], [("i", 100, 100)],
       [], [], [], [("i", 1, 100)], [("i", 0, 99)]] := by cbv

/-- True conjunctions and false disjunctions intersect the endpoint bounds; their opposite polarities
    give nothing. False inequality already gives the singleton, also under negation or disjunction. -/
public theorem guard_equality_composite_zeuge :
    ([ (.and (.cmp "!=" (.param "i") (.lit 0)) (.cmp "!=" (.param "i") (.lit 100)), true),
       (.and (.cmp "!=" (.param "i") (.lit 0)) (.cmp "!=" (.param "i") (.lit 100)), false),
       (.or (.cmp "==" (.param "i") (.lit 0)) (.cmp "==" (.param "i") (.lit 100)), false),
       (.or (.cmp "==" (.param "i") (.lit 0)) (.cmp "==" (.param "i") (.lit 100)), true),
       (.not (.cmp "!=" (.param "i") (.lit 5)), true),
       (.or (.cmp "!=" (.param "i") (.lit 5)) (.cmp "<" (.param "i") (.lit 5)), false) ] :
        List (UEns × Bool)).map (fun g => uWaechterFakten context g.1 g.2) =
      [[("i", 1, 99)], [], [("i", 1, 99)], [], [("i", 5, 5)], [("i", 5, 5)]] := by cbv

/-- Named constants are literals before fact extraction, including with the operands reversed. -/
public theorem guard_equality_constant_zeuge :
    (uBool {context with lits := [("TOP", 100)]} (.bin "!=" (.variable "TOP") (.variable "i"))).map
        (fun cv => uWaechterFakten context cv true) = .ok [("i", 0, 99)] := by cbv

/-- Endpoint exclusion uses the current range; empty or unchanged results, mutable and unknown ranges
    still give no fact. No shared `update`-arm boundary rule was added. -/
public theorem guard_equality_limits_zeuge :
    uWaechterFakten {context with types := [.int 10 90]} (.cmp "!=" (.param "i") (.lit 10)) true =
        [("i", 11, 90)] ∧
      uWaechterFakten {context with types := [.int 0 0]} (.cmp "!=" (.param "i") (.lit 0)) true = [] ∧
      uWaechterFakten {context with types := [.int 0 0]} (.cmp "==" (.param "i") (.lit 0)) true = [] ∧
      uWaechterFakten {context with muts := ["i"]} (.cmp "!=" (.param "i") (.lit 0)) true = [] ∧
      uWaechterFakten {context with unknownRanges := ["i"]} (.cmp "!=" (.param "i") (.lit 0)) true = [] ∧
      uGrenzen context "i" false (.cmp "==" (.param "i") (.lit 0)) = (none, none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

end Gabbro.Grammatik.Parser.Uebersetze.GuardWitness
