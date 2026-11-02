module

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
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
public import Grammatik.Kern.Syntax.Typen.ReasonProben
import all Init.Data.Repr

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

def reasonCases : List (String × SExpr × String) :=
  [("Ready", .lit 3, "ready"), ("Wide", .lit (2 ^ 100), "wide")]

def descriptorShape (r : Except String ReasonSpec) : Option (Nat × List Nat × Bool) :=
  match r with
  | .error _ => none
  | .ok r => some (r.name, r.codes.map (·.val), r.closed)

/-- The source collector retains code values, including those above one runner word. -/
theorem uReasonSpec_identity_zeuge :
    descriptorShape (uReasonSpec [] 41 reasonCases false) = some (41, [3, 2 ^ 100], false) := by
  decide

theorem uReasonSpec_closed_zeuge :
    descriptorShape (uReasonSpec [] 41 reasonCases true) = some (41, [3, 2 ^ 100], true) := by
  decide

theorem uReasonSpec_empty_open_zeuge :
    descriptorShape (uReasonSpec [] 42 [] false) = some (42, [], false) := by decide

theorem uReasonSpec_identity_preserved_zeuge :
    ∃ r, uReasonSpec [] 41 reasonCases false = .ok r ∧ r.name = 41 ∧ r.closed = false := by
  let r : ReasonSpec :=
    ⟨41, [⟨3, by decide⟩, ⟨2 ^ 100, by decide⟩], false, by decide⟩
  have h : uReasonSpec [] 41 reasonCases false = .ok r := by decide
  exact ⟨r, h, uReasonSpec_identity h⟩

theorem uReasonSpec_nominal_zeuge :
    descriptorShape (uReasonSpec [] 41 reasonCases true) ≠
      descriptorShape (uReasonSpec [] 42 reasonCases true) := by decide

theorem uReasonSpec_duplicate_code_refused :
    uReasonSpec [] 41 [("A", .lit 3, "a"), ("B", .lit 3, "b")] true =
      .error "duplicate reason code" := by decide

theorem uReasonSpec_duplicate_name_refused :
    uReasonSpec [] 41 [("A", .lit 3, "a"), ("A", .lit 4, "b")] true =
      .error "duplicate reason case name" := by decide

theorem uReasonSpec_negative_refused :
    uReasonSpec [] 41 [("A", .un "-" (.lit 1), "a")] true =
      .error "reason code outside u128" := by decide

theorem uReasonSpec_overflow_refused :
    uReasonSpec [] 41 [("A", .lit (2 ^ 128), "a")] false =
      .error "reason code outside u128" := by decide

theorem uReasonSpec_maximum_zeuge :
    descriptorShape (uReasonSpec [] 41 [("A", .lit (2 ^ 128 - 1), "a")] false) =
      some (41, [2 ^ 128 - 1], false) := by decide

/-- Resolve constant aliases through the same reader used by ranges. -/
theorem uReasonSpec_constant_zeuge :
    descriptorShape (uReasonSpec [("Code", (3, 3))] 41 [("A", .variable "Code", "a")] true) =
      some (41, [3], true) := by decide

/-- Runtime parameters cannot become declaration-time reason codes. -/
theorem uReasonSpec_nonconstant_refused :
    uReasonSpec [("Code", (3, 4))] 41 [("A", .variable "Code", "a")] true =
      .error "reason code without a constant G form" := by decide

def collectedShape (items : List SItemTief) : Option (List (Nat × List Nat × Bool)) :=
  match uWhys items with
  | .error _ => none
  | .ok ws => ws.mapM fun w => w.descriptor.map fun r => (r.name, r.codes.map (·.val), r.closed)

/-- Identical cases in separate declarations retain distinct identities. -/
theorem uWhys_descriptors_zeuge :
    collectedShape [.whyT "First" reasonCases true, .whyT "Second" reasonCases true] =
      some [(0, [3, 2 ^ 100], true), (1, [3, 2 ^ 100], true)] := by decide

theorem uWhys_duplicate_refused :
    uWhys [.whyT "R" [("A", .lit 3, "a"), ("B", .lit 3, "b")] true] =
      .error "duplicate reason code" := by decide

/-- Collection understands open descriptors, but the old execution channels remain closed. -/
theorem uWhys_open_still_refused :
    uWhys [.whyT "R" reasonCases false] =
      .error "reason that is not exhaustive without G form" := by decide

end Gabbro.Grammatik.Parser.Uebersetze
