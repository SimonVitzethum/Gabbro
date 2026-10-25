/-
  File:      Grammatik/Parser/Print/Proben.lean
  Subject:   Track P: decided witnesses of the printers (`Print/Stmt`, `Print/Item`, the `ext` spelling of
             `druckToks`). One witness per form, each with a negative twin: a tampered token list does not
             read back as the same tree, and a kind without a printer answers `none`.
-/
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ## The `ext` forms: print, read back through `parsePred` -/

/-- Print a predicate, read it back as a predicate, compare by shape. -/
def rundlaufPred (e : SExpr) : Bool :=
  match parsePred 400 (druckToks e ++ [.ende]) with
  | .ok (e', [.ende]) => beqSExpr e e'
  | _ => false

def pc : SExpr := .variable "c"
def pBody : SExpr := .bin "==" (.variable "x") (.lit 0)

theorem rt_all : rundlaufPred (.ext .all ["x", "slots"] [pc, pBody]) = true := by decide +kernel
theorem rt_any : rundlaufPred (.ext .any ["x", "descendants"] [pc, pBody]) = true := by decide +kernel
theorem rt_count : rundlaufPred (.ext .count ["x", "queue"] [pc, pBody]) = true := by decide +kernel
theorem rt_threads : rundlaufPred (.ext .all ["t", "threads"] [pBody]) = true := by decide +kernel
theorem rt_fields : rundlaufPred (.ext .all ["f", "fields", "A", "B"] [pBody]) = true := by decide +kernel
theorem rt_chain : rundlaufPred (.ext .all ["x", "chain", "a", "b"] [pc, pBody]) = true := by decide +kernel
theorem rt_mem : rundlaufPred (.ext .mem ["slots"] [.variable "e", pc]) = true := by decide +kernel
theorem rt_reach :
    rundlaufPred (.ext .reach ["elter"] [.index (.field pc "slots") (.variable "s"), .variable "W"]) = true := by
  decide +kernel
theorem rt_imp : rundlaufPred (.ext .imp [] [pBody, .bin "!=" (.variable "y") (.lit 1)]) = true := by
  decide +kernel
theorem rt_text : rundlaufPred (.ext .text ["abc"] []) = true := by decide +kernel
theorem rt_call : rundlaufPred (.ext .call [] [.arrow (.variable "v") "f", .lit 1]) = true := by
  decide +kernel
/-- A quantifier inside a conjunction: the parentheses keep the body from swallowing the rest. -/
theorem rt_nested :
    rundlaufPred (.bin "&&" (.ext .all ["x", "slots"] [pc, pBody]) (.ext .imp [] [pBody, pBody])) = true := by
  decide +kernel

/-- NEGATIVE: the quantifier read back with its `in` replaced is not the same tree. -/
theorem rt_all_twin :
    (match parsePred 400 ((druckToks (.ext .all ["x", "slots"] [pc, pBody])).map
        (fun t => match t with | .wort "in" => .wort "of" | t => t) ++ [.ende]) with
      | .ok (e', [.ende]) => beqSExpr (.ext .all ["x", "slots"] [pc, pBody]) e'
      | _ => false) = false := by
  decide +kernel

/-! ## Statements -/

def rbs (ss : List SAnw) (e : Option SEnde := none) : Bool := rundlaufBlock (.block ss e)

theorem rt_let : rbs [.bind false "x" (some (.atom "u32")) (.lit 1), .bind true "y" none (.variable "x")] = true := by
  decide +kernel
theorem rt_letelse :
    rbs [.bindElse "v" none (.call "g" [.lit 1]) "r" (.block [] (some (.ret none)))] = true := by decide +kernel
theorem rt_set : rbs [.set (.variable "x") "+=" (.lit 1), .call "f" [.variable "x", .lit 2]] = true := by
  decide +kernel
theorem rt_if :
    rbs [.cond (.variable "c") (.block [.call "f" []] none)
      [.elsif (.variable "d") (.block [] (some (.leave "i")))] (some (.block [.call "g" []] none))] = true := by
  decide +kernel
theorem rt_traverse :
    rbs [.each "i" none "slots" (.variable "t") "unvisited" "touches writes t . slots " (some pBody)
      (.block [.call "f" [.variable "i"]] (some (.next "i")))] = true := by
  decide +kernel
theorem rt_locks :
    rbs [.locks false (.variable "L") (.block [.set (.variable "x") "=" (.lit 1)] none),
         .locks true (.variable "M") (.block [] none)] (some (.ret (some (.variable "x")))) = true := by
  decide +kernel
theorem rt_match :
    rbs [.cases (.variable "v") [.arm "A" none (.block [] none), .arm "B" (some "k") (.block [] (some (.ret none)))]]
      = true := by
  decide +kernel
theorem rt_misc :
    rbs [.emit (.variable "A") (.lit 1) "nothing", .await "v" (.variable "A") "p , q ",
         .swap "w" (.variable "A") "update ( v ) { v } ", .step "a" "b", .free (.index (.variable "A") (.lit 0)),
         .reset "A" none, .reset "A" (some (.lit 0, .lit 2)), .start ["main", "m::f"], .child (.block [] none)] = true := by
  decide +kernel
/-- The whole statement forms of the reader that carry a raw header or an alloc, grow and shift: one block. -/
theorem rt_rest :
    rbs [.alloc false "n" none "A" (.lit 1) (some (.block [] none)), .grow "A" (.lit 2) (.block [] none),
         .shift (.variable "x") "a" "b", .waive ["I", "J"] (.block [] none),
         .trim (.variable "x") "u8 " (.block [] none), .watch "R" (.block [] none),
         .retry "until ok bounded 8 ops on_exceeded h " (.block [] none)] = true := by
  decide +kernel

/-- NEGATIVE: the printed block with one `;` dropped does not read back (the reader refuses it). -/
theorem rt_set_twin :
    beqTopBlock (parseTopBlock ((druckAnw (.block [.call "f" []] none)).filter
      (fun t => match t with | .zeichen ";" => false | _ => true) ++ [.ende])) (.ok (.block [.call "f" []] none))
      = false := by
  decide +kernel

/-! ## Items -/

theorem rt_item_fn :
    rundlaufItem (.fnT { art := "impl", name := "f", params := [("a", .atom "u32")], res := some (.atom "u32"),
                         fehler := none, klauseln := [.needs (.bin "<" (.variable "a") (.lit 9)),
                           .gives (.bin "==" .res (.variable "a")), .effs [.reads (.variable "T"), .pure],
                           .cost (.lit 4)] }
      (.block [] (some (.ret (some (.variable "a")))))) = true := by
  decide +kernel
theorem rt_item_data :
    rundlaufItem (.tableT "T" none (some (.lit 4)) none none false
      [.tSlot [{ fname := "v", ftyp := .atom "u32", pos := none, bezug := none, wo := none,
                 reserviert := false, byOps := true }]]) = true := by
  decide +kernel

end Gabbro.Grammatik.Parser
