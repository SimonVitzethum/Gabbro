/- Witnesses of tagged wildcard expansion and the shapes left for ordinary refusal. -/
module
public import Grammatik.Parser.Elab.Modules.MatchWildcard
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

namespace Gabbro.Grammatik.Parser.MatchWildcard
attribute [local cbv_eval] strEq_apply_eq_decide

def fixtureSig : FnSig :=
  { art := "impl", name := "f", params := [("v", .atom "Token")], res := some (.atom "u8"), fehler := none, klauseln := [] }

def twoCases : SItemTief := .typeT ["tagged"] "Token" [] [] (some (.raw "{ A, B }"))

def threeCases : SItemTief :=
  .typeT ["tagged"] "Token" [] [] (some (.raw "{ B(u8), A, C }"))

def answer (n : Nat) : SAnw := .block [] (some (.ret (some (.lit n))))

def fixture (declarations : List SItemTief) (body : SAnw) : List SItemTief :=
  declarations ++ [.fnT fixtureSig body]

def wildcardMatch : SAnw :=
  .cases (.variable "v") [.arm "A" none (answer 1), .arm "_" none (answer 2)]

def explicitMatch : SAnw :=
  .cases (.variable "v") [.arm "A" none (answer 1), .arm "B" none (answer 2)]

/-- The existing parser already produces a binder-free arm named `_`. -/
theorem parser_zeuge :
    (match lex "match v { A => { return 1; } _ => { return 2; } }" with
      | .ok tokens => (parseTopStmt tokens).toOption
      | .error _ => none) = some wildcardMatch := by cbv

/-- A two-case tagged match replaces its wildcard with the missing payload-free case. -/
theorem two_cases_zeuge :
    erweitere (fixture [twoCases] wildcardMatch) =
      fixture [twoCases] explicitMatch := by cbv

/-- Missing cases follow declaration order and only the payload case gets a fresh binder. -/
theorem three_cases_zeuge :
    erweitere (fixture [threeCases] wildcardMatch) =
      fixture [threeCases] (.cases (.variable "v")
        [.arm "A" none (answer 1), .arm "B" (some "#w0") (answer 2),
          .arm "C" none (answer 2)]) := by cbv

/-- A match nested in an `if` body expands too. -/
theorem nested_if_zeuge :
    erweitere (fixture [twoCases] (.cond .tru (.block [wildcardMatch] none) [] none)) =
      fixture [twoCases] (.cond .tru (.block [explicitMatch] none) [] none) := by cbv

/-- Every statement constructor carrying a body contains the same nested match fixture. -/
def bodyForms (b : SAnw) : List SAnw :=
  [.cond .tru b [.elsif .fls b] (some b), .elsif .tru b,
    .cases (.variable "outer") [.arm "A" none b], .arm "A" none b,
    .each "i" none "slots" (.variable "T") "unvisited" "" none b,
    .boundedLoop "while true bounded 3 ops on_exceeded h " b,
    .boundedLoop "for i in 0 ..< 3 " b,
    .retry "forever" b, .loop "forever" b, .waive [] b, .trim (.variable "x") "u8" b,
    .locks false (.variable "L") b, .watch "D" b, .block [b] none,
    .bindElse "x" none (.call "f" []) "e" b, .callElse "f" [] "e" b,
    .callIndElse (.variable "p") [] "e" b,
    .bindAxiomOptElse "x" none (.call "f" []) "e" b,
    .alloc false "x" none "A" (.lit 1) (some b), .grow "A" (.lit 1) b, .child b]

/-- The traversal reaches every body form, including allocation and foreign failure bodies. -/
theorem body_forms_zeuge :
    erweitere (fixture [twoCases] (.block (bodyForms wildcardMatch) none)) =
      fixture [twoCases] (.block (bodyForms explicitMatch) none) := by cbv

/-- A wildcard without a named case cannot identify a tagged type. -/
theorem only_wildcard_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v") [.arm "_" none (answer 2)])) =
      fixture [twoCases] (.cases (.variable "v") [.arm "_" none (answer 2)]) := by cbv

/-- Two wildcards remain unchanged. -/
theorem repeated_wildcard_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v")
      [.arm "A" none (answer 1), .arm "_" none (answer 2), .arm "_" none (answer 3)])) =
      fixture [twoCases] (.cases (.variable "v")
        [.arm "A" none (answer 1), .arm "_" none (answer 2), .arm "_" none (answer 3)]) := by cbv

/-- A wildcard before a named arm remains unchanged. -/
theorem nonfinal_wildcard_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v")
      [.arm "_" none (answer 2), .arm "A" none (answer 1)])) =
      fixture [twoCases] (.cases (.variable "v")
        [.arm "_" none (answer 2), .arm "A" none (answer 1)]) := by cbv

/-- A wildcard carrying a binder remains unchanged. -/
theorem binding_wildcard_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v")
      [.arm "A" none (answer 1), .arm "_" (some "x") (answer 2)])) =
      fixture [twoCases] (.cases (.variable "v")
        [.arm "A" none (answer 1), .arm "_" (some "x") (answer 2)]) := by cbv

/-- `Some` does not identify a case of the unit's tagged type. -/
theorem option_some_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v")
      [.arm "Some" (some "x") (answer 1), .arm "_" none (answer 2)])) =
      fixture [twoCases] (.cases (.variable "v")
        [.arm "Some" (some "x") (answer 1), .arm "_" none (answer 2)]) := by cbv

/-- `None` does not identify a case of the unit's tagged type either. -/
theorem option_none_zeuge :
    erweitere (fixture [twoCases] (.cases (.variable "v")
      [.arm "None" none (answer 1), .arm "_" none (answer 2)])) =
      fixture [twoCases] (.cases (.variable "v")
        [.arm "None" none (answer 1), .arm "_" none (answer 2)]) := by cbv

def reasonCases : SItemTief := .whyT "Failure" [("Busy", .lit 1, "")] false

/-- A declared reason case is not a tagged case. -/
theorem reason_zeuge :
    erweitere (fixture [twoCases, reasonCases] (.cases (.variable "v")
      [.arm "Busy" none (answer 1), .arm "_" none (answer 2)])) =
      fixture [twoCases, reasonCases] (.cases (.variable "v")
        [.arm "Busy" none (answer 1), .arm "_" none (answer 2)]) := by cbv

def otherCases : SItemTief := .typeT ["tagged"] "Other" [] [] (some (.raw "{ A, D }"))

/-- A named case shared by two tagged types cannot select a unique schema. -/
theorem ambiguous_type_zeuge :
    erweitere (fixture [twoCases, otherCases] wildcardMatch) =
      fixture [twoCases, otherCases] wildcardMatch := by cbv

/-- Named cases belonging to different tagged types cannot select one schema. -/
theorem mixed_types_zeuge :
    erweitere (fixture [twoCases, otherCases] (.cases (.variable "v")
      [.arm "B" none (answer 1), .arm "D" none (answer 2), .arm "_" none (answer 3)])) =
      fixture [twoCases, otherCases] (.cases (.variable "v")
        [.arm "B" none (answer 1), .arm "D" none (answer 2), .arm "_" none (answer 3)]) := by cbv

/-- Fresh payload names remain distinct across ordinary and gated function bodies. -/
theorem fresh_binders_zeuge :
    erweitere [threeCases, .fnT fixtureSig wildcardMatch, .gateT (.fnT fixtureSig wildcardMatch)] =
      [threeCases, .fnT fixtureSig (.cases (.variable "v")
        [.arm "A" none (answer 1), .arm "B" (some "#w0") (answer 2), .arm "C" none (answer 2)]),
        .gateT (.fnT fixtureSig (.cases (.variable "v")
          [.arm "A" none (answer 1), .arm "B" (some "#w1") (answer 2),
            .arm "C" none (answer 2)]))] := by cbv

/-- Compile-time functions keep their source body. -/
theorem const_function_zeuge :
    erweitere [twoCases, .fnT { fixtureSig with art := "const" } wildcardMatch] =
      [twoCases, .fnT { fixtureSig with art := "const" } wildcardMatch] := by cbv

end Gabbro.Grammatik.Parser.MatchWildcard
