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
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema
import all Grammatik.Parser.Elab.Uebersetze.Tagged.ProbeResults
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Init.Data.Repr

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] Nat.log2_def
attribute [local cbv_eval] Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowEns.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowCmp.eq_def
open scoped Gabbro.Grammatik.Parser.Uebersetze

namespace TypedPayload

open Gabbro.Grammatik.Parser.UebersetzeAllg2

def sums : List USum :=
  [{ name := "Message", cases := [("Empty", none), ("Flag", some .bool),
      ("Count", some (.int 0 255)), ("Bytes", some (.arr (.int 0 255) 2)),
      ("Text", some (.str 8)), ("Nested", some (.sum [none, some .bool]))] }]

def unit : UProg := { tabs := [], locks := [], fns := [], sums := sums }
def scope : UFn :=
  { name := "fixture", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

-- The indexed result type is fixed before any match elaboration.
theorem payload_index_bound : 0 < unit.sums.length := by decide

/-- The actual tagged lowering path accepts complete record-free payloads. -/
theorem lower_bool_zeuge :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 (some (.truth true))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 (some (.truth true))))

theorem lower_bool_variable_zeuge :
    (match lowSVal unit [.bool] [] { scope with params := [("flag", .bool)], kinds := [.bool] }
      0 0 payload_index_bound (.fall 1 (some (.param "flag"))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [.bool] [] { scope with params := [("flag", .bool)], kinds := [.bool] }
      0 0 payload_index_bound (.fall 1 (some (.param "flag"))))

theorem lower_scalar_zeuge :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 2 (some (.lit 37))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 2 (some (.lit 37))))

theorem lower_array_zeuge :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound
      (.fall 3 (some (.arrCons (.lit 7) (.arrCons (.lit 9) .arrNil)))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [] [] scope 0 0 payload_index_bound
      (.fall 3 (some (.arrCons (.lit 7) (.arrCons (.lit 9) .arrNil)))))

theorem lower_string_zeuge :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 4 (some (.text [65, 66]))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 4 (some (.text [65, 66]))))

theorem lower_nested_sum_zeuge :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound
      (.fall 5 (some (.taggedValue [none, some .bool] 1 (.truth false)))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (lowSVal unit [] [] scope 0 0 payload_index_bound
      (.fall 5 (some (.taggedValue [none, some .bool] 1 (.truth false)))))

theorem lower_missing_payload_refused :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 none) with
      | .ok _ => false | .error _ => true) = true := by
  tagged_error (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 none))

theorem lower_extra_payload_refused :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 0 (some (.lit 1))) with
      | .ok _ => false | .error _ => true) = true := by
  tagged_error (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 0 (some (.lit 1))))

theorem lower_wrong_payload_refused :
    (match lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 (some (.lit 1))) with
      | .ok _ => false | .error _ => true) = true := by
  tagged_error (lowSVal unit [] [] scope 0 0 payload_index_bound (.fall 1 (some (.lit 1))))

/-- Dependency resolution preserves source order even for a forward reference. -/
theorem nested_schema_export_zeuge :
    uSums [] [.typeT ["tagged"] "Outer" [] [] (some (.raw "{ Wrap(Inner) }")),
      .typeT ["tagged"] "Inner" [] [] (some (.raw "{ Flag(bool), Empty }"))] =
      .ok [{ name := "Outer", cases := [("Wrap", some (.sum [some .bool, none]))] },
        { name := "Inner", cases := [("Flag", some .bool), ("Empty", none)] }] := by cbv

theorem recursive_schema_refused :
    (match uSums [] [.typeT ["tagged"] "Recursive" [] []
        (some (.raw "{ Wrap(Recursive) }"))] with
      | .ok _ => false | .error _ => true) = true := by
  tagged_error (uSums [] [.typeT ["tagged"] "Recursive" [] []
        (some (.raw "{ Wrap(Recursive) }"))])

/-- Export and lower a source predicate as the selected complete bool payload. -/
def sourceBoolPayload (locks : List ULock) (source : SExpr) : Bool :=
  let tabs : List UTab := [{ name := "Flags", count := 2, cols := [("ready", (0, 1))], bools := ["ready"] }]
  let ctx : UCtx := { names := ["flag", "n"], kinds := [.bool, .int], types := [.bool, .int 0 255], tabs, locks, held := [], res := none, fname := "fixture", alias := [], lits := [], sums }
  let fn := { scope with params := [("flag", .bool), ("n", .int 0 255)], kinds := [.bool, .int] }
  match (generalizing := false) uSVal ctx 0 (.call "Flag" [source]) with
  | .error _ => false
  | .ok value =>
    match (generalizing := false) lowSVal { unit with tabs, locks } [.bool, .int 0 255] [] fn 0 0 payload_index_bound value with
    | .ok _ => true
    | .error _ => false

theorem source_comparison_payload_zeuge :
    sourceBoolPayload [] (.bin "<" (.variable "n") (.lit 7)) = true := by
  cbv

theorem source_boolean_payload_zeuge :
    sourceBoolPayload [] (.bin "&&" (.un "!" (.variable "flag")) (.bin "<" (.variable "n") (.lit 7))) = true := by
  cbv

def sourceFlagRead : SExpr := .field (.index (.field (.variable "Flags") "slots") (.lit 1)) "ready"

theorem source_bool_field_payload_zeuge : sourceBoolPayload [] sourceFlagRead = true := by
  cbv

theorem source_guarded_payload_refused :
    sourceBoolPayload [{ name := "Guard", rank := 1, guard := ["Flags"] }] sourceFlagRead = false := by
  cbv

theorem source_numeric_bool_payload_refused : sourceBoolPayload [] (.lit 1) = false := by
  cbv

theorem source_old_payload_refused :
    sourceBoolPayload [] (.old sourceFlagRead) = false := by
  cbv

theorem source_result_payload_refused : sourceBoolPayload [] .res = false := by
  cbv

/-- Scalar introductions are typed by the common value lowerer. -/
theorem lower_option_payload_zeuge :
    (match Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 2))) with
      | .ok _ => true | .error _ => false) = true := by
  tagged_ok (Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 2))))

theorem lower_option_payload_range_refused :
    (match Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 4))) with
      | .ok _ => false | .error _ => true) = true := by
  tagged_error (Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 4))))

end TypedPayload

end Gabbro.Grammatik.Parser.Uebersetze
