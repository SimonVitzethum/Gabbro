/-
  File:      Grammatik/Parser/Print/Proben.lean
  Subject:   Track P: decided witnesses of the printers (`Print/Stmt`, `Print/Item`, the `ext` spelling of
             `druckToks`). One witness per form, each with a negative twin: a tampered token list does not
             read back as the same tree, and a kind without a printer answers `none`.
-/
module
public import Grammatik.Parser.Print.Item
import Lean.Elab.Tactic.Cbv
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
@[expose] public section


namespace Gabbro.Grammatik.Parser

-- Compare spellings through literal equality during proof-producing evaluation.
attribute [local cbv_eval] strEq_apply_eq_decide

set_option maxRecDepth 100000

/-! ## The `ext` forms: print, read back through `parsePred` -/

/-- Print a predicate, read it back as a predicate, compare by shape. -/
def rundlaufPred (e : SExpr) : Bool :=
  match parsePred 400 (druckToks e ++ [.ende]) with
  | .ok (e', [.ende]) => beqSExpr e e'
  | _ => false

def pc : SExpr := .variable "c"
def pBody : SExpr := .bin "==" (.variable "x") (.lit 0)

theorem rt_all : rundlaufPred (.ext .all ["x", "slots"] [pc, pBody]) = true := by cbv
theorem rt_any : rundlaufPred (.ext .any ["x", "descendants"] [pc, pBody]) = true := by cbv
theorem rt_count : rundlaufPred (.ext .count ["x", "queue"] [pc, pBody]) = true := by cbv
theorem rt_threads : rundlaufPred (.ext .all ["t", "threads"] [pBody]) = true := by cbv
theorem rt_fields : rundlaufPred (.ext .all ["f", "fields", "A", "B"] [pBody]) = true := by cbv
theorem rt_chain : rundlaufPred (.ext .all ["x", "chain", "a", "b"] [pc, pBody]) = true := by cbv
theorem rt_mem : rundlaufPred (.ext .mem ["slots"] [.variable "e", pc]) = true := by cbv
theorem rt_reach :
    rundlaufPred (.ext .reach ["elter"] [.index (.field pc "slots") (.variable "s"), .variable "W"]) = true := by
  cbv
theorem rt_imp : rundlaufPred (.ext .imp [] [pBody, .bin "!=" (.variable "y") (.lit 1)]) = true := by
  cbv
theorem rt_text : rundlaufPred (.ext .text ["abc"] []) = true := by cbv
theorem rt_call : rundlaufPred (.ext .call [] [.arrow (.variable "v") "f", .lit 1]) = true := by
  cbv
/-- A quantifier inside a conjunction: the parentheses keep the body from swallowing the rest. -/
theorem rt_nested :
    rundlaufPred (.bin "&&" (.ext .all ["x", "slots"] [pc, pBody]) (.ext .imp [] [pBody, pBody])) = true := by
  cbv

/-- NEGATIVE: the quantifier read back with its `in` replaced is not the same tree. -/
theorem rt_all_twin :
    (match parsePred 400 ((druckToks (.ext .all ["x", "slots"] [pc, pBody])).map
        (fun t => match t with | .wort "in" => .wort "of" | t => t) ++ [.ende]) with
      | .ok (e', [.ende]) => beqSExpr (.ext .all ["x", "slots"] [pc, pBody]) e'
      | _ => false) = false := by
  cbv

/-! ## Statements -/

def rbs (ss : List SAnw) (e : Option SEnde := none) : Bool := rundlaufBlock (.block ss e)

theorem rt_let : rbs [.bind false "x" (some (.atom "u32")) (.lit 1), .bind true "y" none (.variable "x")] = true := by
  cbv
theorem rt_letelse :
    rbs [.bindElse "v" none (.call "g" [.lit 1]) "r" (.block [] (some (.ret none)))] = true := by cbv
theorem rt_set : rbs [.set (.variable "x") "+=" (.lit 1), .call "f" [.variable "x", .lit 2]] = true := by
  cbv
theorem rt_if :
    rbs [.cond (.variable "c") (.block [.call "f" []] none)
      [.elsif (.variable "d") (.block [] (some (.leave "i")))] (some (.block [.call "g" []] none))] = true := by
  cbv
theorem rt_traverse :
    rbs [.each "i" none "slots" (.variable "t") "unvisited" "touches writes t . slots " (some pBody)
      (.block [.call "f" [.variable "i"]] (some (.next "i")))] = true := by
  cbv
theorem rt_locks :
    rbs [.locks false (.variable "L") (.block [.set (.variable "x") "=" (.lit 1)] none),
         .locks true (.variable "M") (.block [] none)] (some (.ret (some (.variable "x")))) = true := by
  cbv
theorem rt_match :
    rbs [.cases (.variable "v") [.arm "A" none (.block [] none), .arm "B" (some "k") (.block [] (some (.ret none)))]]
      = true := by
  cbv
theorem rt_misc :
    rbs [.emit (.variable "A") (.lit 1) "nothing", .await "v" none (.variable "A") "p , q ",
         .swap "w" none (.variable "A") "update ( v ) { v } ", .step "a" "b", .free (.index (.variable "A") (.lit 0)),
         .reset "A" none, .reset "A" (some (.lit 0, .lit 2)), .start ["main", "m::f"], .child (.block [] none)] = true := by
  cbv
/-- The whole statement forms of the reader that carry a raw header or an alloc, grow and shift: one block. -/
theorem rt_rest :
    rbs [.alloc false "n" none "A" (.lit 1) (some (.block [] none)), .grow "A" (.lit 2) (.block [] none),
         .shift (.variable "x") "a" "b", .waive ["I", "J"] (.block [] none),
         .trim (.variable "x") "u8 " (.block [] none), .watch "R" (.block [] none),
         .retry "until ok bounded 8 ops on_exceeded h " (.block [] none)] = true := by
  cbv

/-- NEGATIVE: the printed block with one `;` dropped does not read back (the reader refuses it). -/
theorem rt_set_twin :
    beqTopBlock (parseTopBlock ((druckAnw (.block [.call "f" []] none)).filter
      (fun t => match t with | .zeichen ";" => false | _ => true) ++ [.ende])) (.ok (.block [.call "f" []] none))
      = false := by
  cbv

/-! ## Items -/

theorem rt_item_fn :
    rundlaufItem (.fnT { art := "impl", name := "f", params := [("a", .atom "u32")], res := some (.atom "u32"),
                         fehler := none, klauseln := [.needs (.bin "<" (.variable "a") (.lit 9)),
                           .gives (.bin "==" .res (.variable "a")), .effs [.reads (.variable "T"), .pure],
                           .cost (.lit 4)] }
      (.block [] (some (.ret (some (.variable "a")))))) = true := by
  cbv
theorem rt_item_data :
    rundlaufItem (.tableT "T" none (some (.lit 4)) none none false
      [.tSlot [{ fname := "v", ftyp := .atom "u32", pos := none, bezug := none, wo := none,
                 reserviert := false, byOps := true }]]) = true := by
  cbv

/-! ## Reason propagation `?` and adapters `from` (§4.1, §4.3) -/

theorem rt_letquery :
    rbs [.bindQ false "x" (some (.atom "u32")) (.call "g" [.lit 1]),
         .bindQ true "y" none (.call "h" [.variable "x"])] = true := by
  cbv

theorem rt_callquery :
    rbs [.callQ "f" [.variable "x", .lit 2]] = true := by
  cbv

/-- NEGATIVE: `?` behind a non-call is refused. -/
theorem rt_query_twin :
    (match parseTopBlock (druckAnw (.block [.bindQ false "x" none (.lit 1)] none) ++ [.ende]) with
      | .ok _ => true
      | .error _ => false) = false := by
  cbv

theorem rt_item_adapt :
    rundlaufItem (.adaptT { art := "", name := "g", params := [], res := some (.atom "u32"),
                            fehler := none, klauseln := [.cost (.lit 4)] }
      [.alle, .ohne "s", .neu "k" (.atom "u32")]
      { quelle := "f", gebunden := some "a", sonst := none,
        vorspiel := [.bind false "s" none (.lit 2)] }
      (some (.block [] (some (.ret (some (.variable "a"))))))) = true := by
  cbv

theorem rt_item_adaptkurz :
    rundlaufItem (.adaptT { art := "", name := "g", params := [], res := none,
                            fehler := none, klauseln := [] }
      [.alle, .ohne "s"]
      { quelle := "f", gebunden := none, sonst := none,
        vorspiel := [.bind false "s" none (.lit 2)] }
      none) = true := by
  cbv

/-- A minus in an ordinary parameter's type is not an adapter removal parameter. -/
theorem rt_item_type_minus :
    (match lex "fn f(p: string max -x);" with
      | .ok ts => beqTopTief (parseTopTief ts) (.ok [.protoT
          { art := "", name := "f", params := [("p", .str (.un "-" (.variable "x")))],
            res := none, fehler := none, klauseln := [] }])
      | .error _ => false) = true := by
  cbv

/-- A real adapter marker still counts after a new parameter with an ordinary type expression. -/
theorem rt_item_adapt_after_type_minus :
    rundlaufItem (.adaptT { art := "", name := "g", params := [], res := none,
                            fehler := none, klauseln := [] }
      [.neu "p" (.str (.un "-" (.variable "x"))), .alle, .ohne "s"]
      { quelle := "f", gebunden := none, sonst := none, vorspiel := [] }
      none) = true := by
  cbv

end Gabbro.Grammatik.Parser
