module
public import Grammatik.Parser.Elab.Modules.MatchNumber
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Round.RundlaufLex.Teil1a
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Grammatik.Parser.MatchNumber

attribute [local cbv_eval] strEq_apply_eq_decide

def answer (n : Nat) : SAnw := .block [] (some (.ret (some (.lit n))))

def arms : List SAnw :=
  [.arm "1" none (answer 11), .arm "2" none (answer 13), .arm "_" none (answer 17)]

def expected (e : SExpr) : SAnw :=
  .cond (.bin "==" e (.lit 1)) (answer 11)
    [.elsif (.bin "==" e (.lit 2)) (answer 13)] (some (answer 17))

/-- Check the shared text reader before exercising any body traversal or code generation. -/
theorem pattern_zeuge :
    muster {} "1" = some 1 ∧ muster {} "2" = some 2 ∧ muster {} "_" = none :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- Unwinding the recursion keeps both numeric arms in source order and separates the fallback. -/
theorem arms_zeuge :
    arme {} arms [] = .ok ([(1, answer 11), (2, answer 13)], answer 17) := by kernel_rfl

/-- A three-arm match is exactly the existing `if`/`else if`/`else` shape. -/
theorem three_arm_zeuge :
    erweitereMatch {} ["k"] 0 (.variable "k") arms =
      .ok ([expected (.variable "k")], 0) := by kernel_rfl

/-- A call scrutinee occurs in one binding and nowhere in the comparison chain. -/
theorem call_once_zeuge :
    erweitereMatch {} [] 0 (.call "nextCode" []) arms =
      .ok ([.bind false "#m0" none (.call "nextCode" []), expected (.variable "#m0")], 1) := by
  kernel_rfl

/-- A known local (including a parameter) needs no generated binding. -/
theorem local_zeuge :
    erweitereS {} ["k"] 100 0 (.cases (.variable "k") arms) =
      .ok ([expected (.variable "k")], 0) := by kernel_rfl

/-- Locals introduced earlier in the same block are visible to the rewrite. -/
theorem bound_local_zeuge :
    erweitereS {} [] 100 0
      (.block [.bind false "k" none (.lit 2), .cases (.variable "k") arms] none) =
      .ok ([.block [.bind false "k" none (.lit 2), expected (.variable "k")] none], 0) := by
  kernel_rfl

def fixtureSig : FnSig :=
  { art := "impl"
    name := "classify"
    params := [("k", .atom "u32")]
    res := some (.atom "u32")
    fehler := none
    klauseln := [] }

/-- The actual unit entry supplies function parameters to the shared lexical walk. -/
theorem unit_zeuge :
    erweitere [.fnT fixtureSig (.block [.cases (.variable "k") arms] none)] =
      .ok [.fnT fixtureSig (.block [expected (.variable "k")] none)] := by kernel_rfl

/-- A global read is captured once even when it is written as a plain name. -/
theorem global_once_zeuge :
    erweitereMatch {} [] 4 (.variable "CURRENT") arms =
      .ok ([.bind false "#m4" none (.variable "CURRENT"), expected (.variable "#m4")], 5) := by
  kernel_rfl

/-- Call hoisting sees the generated binding; a nested argument call is lifted only once. -/
theorem hoisting_zeuge :
    (erweitereMatch {} [] 0 (.call "nextCode" [.call "arg" []]) arms).map
      (fun r => (CallHoist.hebeS
        { fns := Tafel.von _ ["nextCode", "arg"], statics := Tafel.von _ [] }
        100 0 (.block r.1 none)).1) =
      .ok [.block [.bind false "#r0" none (.call "arg" []),
        .bind false "#m0" none (.call "nextCode" [.variable "#r0"]),
        expected (.variable "#m0")] none] := by kernel_rfl

/-- Missing fallback, duplicate values and binders are refused in the source rewrite. -/
theorem refusal_zeuge :
    erweitereMatch {} ["k"] 0 (.variable "k") [.arm "1" none (answer 1)] =
      .error "number match: final wildcard arm is required" ∧
    erweitereMatch {} ["k"] 0 (.variable "k")
      [.arm "1" none (answer 1), .arm "1" none (answer 2), .arm "_" none (answer 3)] =
      .error "number match: duplicate pattern value" ∧
    erweitereMatch {} ["k"] 0 (.variable "k")
      [.arm "1" (some "x") (answer 1), .arm "_" none (answer 2)] =
      .error "number match: pattern binders are not allowed" :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem nonfinal_wildcard_zeuge :
    erweitereMatch {} ["k"] 0 (.variable "k")
      [.arm "_" none (answer 1), .arm "1" none (answer 2)] =
      .error "number match: wildcard must be the last arm" := by kernel_rfl

/-- Constants and literals are compared by value, independent of local name shadowing. -/
theorem constant_zeuge :
    erweitereMatch { constants := [("CODE", 65)] } ["k", "CODE"] 0 (.variable "k")
      [.arm "CODE" none (answer 1), .arm "_" none (answer 2)] =
      .ok ([.cond (.bin "==" (.variable "k") (.lit 65)) (answer 1) [] (some (answer 2))], 0) ∧
    erweitereMatch { constants := [("CODE", 65)] } ["k"] 0 (.variable "k")
      [.arm "65" none (answer 1), .arm "CODE" none (answer 2), .arm "_" none (answer 3)] =
      .error "number match: duplicate pattern value" := ⟨by kernel_rfl, by kernel_rfl⟩

/-- The unit context uses evaluated integer constants, excluding truth-valued declarations. -/
theorem context_zeuge :
    (kontext [.constT "CODE" (.atom "u32") (.one (.bin "+" (.lit 3) (.lit 4))),
      .constT "FLAG" (.atom "bool") (.one .tru)]).constants = [("CODE", 7)] := by
  cbv

theorem ambiguous_zeuge :
    erweitereMatch { constants := [("CODE", 1)], cases := ["CODE", "Other"] }
      ["k"] 0 (.variable "k") [.arm "CODE" none (answer 1), .arm "_" none (answer 2)] =
      .error "number match: pattern is both a number constant and a tagged case" := by kernel_rfl

/-- Tagged matches retain their arms for the tagged wildcard rewrite and ordinary elaborator. -/
theorem tagged_untouched_zeuge :
    erweitereS { cases := ["End", "Number"] } ["k"] 100 0
      (.cases (.variable "k") [.arm "End" none (answer 1), .arm "_" none (answer 2)]) =
      .ok ([.cases (.variable "k") [.arm "End" none (answer 1), .arm "_" none (answer 2)]], 0) := by
  kernel_rfl

/-- A nested match is expanded inside the selected outer arm, not before the outer condition. -/
theorem nested_zeuge :
    erweitereS {} ["k"] 100 0 (.cases (.variable "k")
      [.arm "1" none (.block [.cases (.call "nextCode" []) arms] none),
        .arm "_" none (answer 2)]) =
      .ok ([.cond (.bin "==" (.variable "k") (.lit 1))
        (.block [.bind false "#m0" none (.call "nextCode" []), expected (.variable "#m0")] none)
        [] (some (answer 2))], 1) := by kernel_rfl

/-- Decimal, hexadecimal, character and constant patterns all use the existing arm constructor. -/
theorem parser_zeuge :
    ((lex "match k { 1 => { return 11; } 0x2 => { return 13; } _ => { return 17; } }").toOption.bind
      (fun tokens => (parseTopStmt tokens).toOption)) = some (.cases (.variable "k") arms) ∧
    ((lex "match k { 'A' => { return 1; } CODE => { return 2; } _ => { return 3; } }").toOption.bind
      (fun tokens => (parseTopStmt tokens).toOption)) = some (.cases (.variable "k")
        [.arm "65" none (answer 1), .arm "CODE" none (answer 2), .arm "_" none (answer 3)]) :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- Literal tokens survive printing and reparsing, both at token and at source-text level. -/
theorem round_trip_zeuge :
    parseTopStmt (druckAnw (.cases (.variable "k") arms) ++ [.ende]) =
      .ok (.cases (.variable "k") arms) ∧
    ((lex (renderText (druckAnw (.cases (.variable "k") arms)))).toOption.bind
      (fun tokens => (parseTopStmt tokens).toOption)) =
      some (.cases (.variable "k") arms) := ⟨by kernel_rfl, by kernel_rfl⟩

/-- Noncanonical decimal names only arise in synthetic ASTs. Keep their exact token-level
    spelling; source `007`, `0x7` and character literals instead arrive as canonical `num` values. -/
theorem synthetic_pattern_zeuge :
    armMusterTok "7" = .num 7 ∧
    armMusterTok "007" = nameTok "007" ∧
    armMusterTok "+1" = nameTok "+1" ∧
    nimmArmMuster (armMusterTok "007" :: [.ende]) = .ok ("007", [.ende]) :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

end Gabbro.Grammatik.Parser.MatchNumber
