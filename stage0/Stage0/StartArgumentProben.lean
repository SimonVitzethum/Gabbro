import Stage0.StartArgument
import Grammatik.Parser.Elab.UebersetzeAllg3

namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Exercise the actual canonical parser/elaborator with repeated functions and distinct
    source arguments; this adapter does not enable the still parameterless image startup. -/
def sourceArguments (text : String) : Except String (List (List SExpr)) := do
  let tokens ← (lex text).mapError (fun _ => "lex")
  let parsed ← parseTopTief tokens
  let items := uMembers (pre108 parsed)
  let unit ← elabU items
  let starts ← fromItems unit items
  pure (starts.map (·.sourceArgs))

def argumentSource : String :=
  "module m { impl fn worker(i : u32 in 0 .. 9, b : bool) { } concurrent { worker(7, true), worker(2, false) }; }"

#eval do
  match sourceArguments argumentSource with
  | .error e => throw (IO.userError e)
  | .ok starts =>
    unless starts.length == 2 && beqSExprList (starts[0]?.getD []) [.lit 7, .tru] &&
        beqSExprList (starts[1]?.getD []) [.lit 2, .fls] do
      throw (IO.userError "source start arguments or multiplicity changed")
  if (sourceArguments
      "module m { impl fn worker(i : u32 in 0 .. 9) { } concurrent { worker(10) }; }").isOk then
    throw (IO.userError "out-of-range source start argument accepted")

/-- A small nondegenerate canonical unit for the generic identity theorem witness. -/
def witnessUnit : UProg := {
  tabs := []
  locks := []
  fns := [{
    name := "worker"
    params := [("i", .int 0 9), ("b", .bool)]
    kinds := [.int, .bool]
    res := none
    held := []
    puts := []
    gives := []
    body := []
    ret := .empty }] }

def witnessGroup : List (List String × List SExpr) :=
  [(["worker"], [.lit 7, .tru]), (["worker"], [.lit 2, .fls])]

theorem fromItems_identity_zeuge :
    ∃ starts, fromItems witnessUnit [.concT witnessGroup] = .ok starts ∧
      starts.map (fun start => (start.path, start.sourceArgs)) = witnessGroup := by
  have accepted : (fromItems witnessUnit [.concT witnessGroup]).isOk = true := by rfl
  cases hr : fromItems witnessUnit [.concT witnessGroup] with
  | error e => rw [hr] at accepted; cases accepted
  | ok starts => exact ⟨starts, rfl, fromItems_identity hr⟩

theorem fromGroup_identity_zeuge :
    ∃ starts, fromGroup witnessUnit [.concT witnessGroup] witnessGroup (by simp) = .ok starts ∧
      starts.map (fun start => (start.path, start.sourceArgs)) = witnessGroup := by
  have accepted : (fromGroup witnessUnit [.concT witnessGroup] witnessGroup (by simp)).isOk = true := by rfl
  cases hr : fromGroup witnessUnit [.concT witnessGroup] witnessGroup (by simp) with
  | error e => rw [hr] at accepted; cases accepted
  | ok starts => exact ⟨starts, rfl, fromGroup_identity _ hr⟩

theorem expression_pure_zeuge (before world before' world' : World (declOf witnessUnit)) :
    eval before (expression witnessUnit (.int (-9) 12) (.un "-" (.lit 7)) (by rfl)) world .nil =
      eval before' (expression witnessUnit (.int (-9) 12) (.un "-" (.lit 7)) (by rfl)) world' .nil :=
  expression_pure witnessUnit _ _ _ before world before' world'

theorem arguments_pure_zeuge (before world before' world' : World (declOf witnessUnit)) :
    evalArgs before (arguments witnessUnit [.int 0 9, .bool] [.lit 7, .tru]
      (by constructor <;> rfl)) world .nil =
    evalArgs before' (arguments witnessUnit [.int 0 9, .bool] [.lit 7, .tru]
      (by constructor <;> rfl)) world' .nil :=
  arguments_pure witnessUnit _ _ _ before world before' world'

#print axioms expression_pure
#print axioms arguments_pure
#print axioms expression_pure_zeuge
#print axioms arguments_pure_zeuge
#print axioms fromItems_identity
#print axioms fromGroup_identity
#print axioms fromItems_identity_zeuge
#print axioms fromGroup_identity_zeuge
#print axioms expression_literal
#print axioms expression_negative
#print axioms expression_literal_zeuge
#print axioms expression_negative_zeuge
end Gabbro.Stage0.StartArgument
