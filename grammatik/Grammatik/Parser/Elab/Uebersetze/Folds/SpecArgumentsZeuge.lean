/- Witnesses of the spec-argument check (`uSpecArgs`, `uSpecArgument`). -/
module
public import Grammatik.Parser.Elab.Uebersetze.Folds.SpecArguments
public import Grammatik.Parser.Spec.Contract
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

namespace Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] strEq_apply_eq_decide

set_option maxRecDepth 100000

def argumentContext : UCtx :=
  { names := ["value"], kinds := [.int], types := [.int 0 9], tabs := [], locks := [],
    held := [], res := none, fname := "fixture", alias := [], lits := [],
    specs := [("small", ["x"], .tru), ("outer", [], .call "small" [.lit 101])],
    specTypen := [("small", [.range (.atom "u32") (.lit 0) (.lit 100) false]),
      ("outer", [])] }

/-- Even a helper that ignores its parameter checks the caller's complete declared range. -/
theorem spec_argument_range_zeuge :
    uSpecArgs 20 argumentContext (.call "small" [.variable "value"]) = .ok () ∧
    uSpecArgs 20 {argumentContext with types := [.int 0 101]}
      (.call "small" [.variable "value"]) =
      .error "spec small: argument 1 does not fit its parameter type" ∧
    uSpecArgs 20 argumentContext (.call "outer" []) =
      .error "spec small: argument 1 does not fit its parameter type" := by
  cbv

/-- Boolean arguments use the Boolean reader; aggregates and missing arguments refuse. -/
theorem spec_argument_types_zeuge :
    uSpecArgument argumentContext "flag" 1 (.atom "bool") .tru = .ok () ∧
    uSpecArgument argumentContext "flag" 1 (.atom "bool") (.lit 1) =
      .error "spec flag: argument 1 does not fit its parameter type" ∧
    uSpecArgument argumentContext "array" 1 (.array (.atom "u32") (.lit 1)) (.lit 1) =
      .error "spec array: argument 1 does not fit its parameter type" ∧
    uSpecArgs 20 argumentContext (.call "small" []) =
      .error "spec small: argument 1 does not fit its parameter type" := by
  cbv

/-- A narrowing conversion cannot manufacture a parameter interval for an ignored argument. -/
theorem spec_argument_conversion_zeuge :
    uSpecArgument argumentContext "small" 1 (.atom "u32") (.call "u8" [.lit 1000]) =
      .error "spec small: argument 1 does not fit its parameter type" ∧
    uSpecArgument argumentContext "small" 1 (.atom "u32") (.call "u8" [.lit 7]) = .ok () := by
  cbv

/-- The count binder shadows the smaller outer `value`; all 102 indices must fit. -/
theorem spec_count_argument_refused_zeuge :
    uSpecArgs 20 {argumentContext with
      tabs := [{ name := "T", count := 102, cols := [] }]}
      (.ext .count ["value", "slots"]
        [.variable "T", .call "small" [.variable "value"]]) =
      .error "spec small: argument 1 does not fit its parameter type" := by
  cbv

/-- The same count is accepted when its largest bound index is exactly 100. -/
theorem spec_count_argument_accepted_zeuge :
    uSpecArgs 20 {argumentContext with
      tabs := [{ name := "T", count := 101, cols := [] }]}
      (.ext .count ["value", "slots"]
        [.variable "T", .call "small" [.variable "value"]]) = .ok () := by
  cbv

def samePredicate : SExpr :=
  .ext .all ["y", "slots"] [.variable "T", .bin "==" (.variable "x") (.variable "y")]

def captureContext : UCtx :=
  { argumentContext with
    names := ["y", "z"]
    kinds := [.int, .int]
    types := [.int 0 9, .int 0 9]
    tabs := [{ name := "T", count := 10, cols := [] }]
    specs := [("same", ["x"], samePredicate)]
    specTypen := [("same", [.atom "u8"])] }

/-- Capturing substitution stays a call; the original predicate is never changed to `y == y`. -/
theorem spec_capture_uninlined_zeuge :
    uSpecEin captureContext.specs 20 (.call "same" [.variable "y"]) =
      .call "same" [.variable "y"] := by
  cbv

/-- The argument gate reports the precise capture error before substituting. -/
theorem spec_capture_refused_zeuge :
    uSpecArgs 20 captureContext (.call "same" [.variable "y"]) =
      .error "spec same: argument 1 names a binder of the predicate" := by
  cbv

/-- A remaining spec call has no ordinary predicate G form, even with a declared spec. -/
theorem spec_capture_downstream_refused_zeuge :
    uSichert captureContext
      (uSpecEin captureContext.specs 20 (.call "same" [.variable "y"])) =
      .error "ensures clause without G form" := by
  cbv

/-- A non-clashing use still passes the type gate and inlines to the original quantifier. -/
theorem spec_noncapturing_inline_zeuge :
    uSpecArgs 20 captureContext (.call "same" [.variable "z"]) = .ok () ∧
    uSpecEin captureContext.specs 20 (.call "same" [.variable "z"]) =
      .ext .all ["y", "slots"]
        [.variable "T", .bin "==" (.variable "z") (.variable "y")] := by
  constructor <;> cbv

/-- The shared inliner preserves the capturing call in generic-spec contract predicates too. -/
theorem spec_contract_capture_zeuge :
    Spec.predicates captureContext.specs true []
      { art := "spec", name := "contract", params := [], res := some (.atom "bool"),
        fehler := none, klauseln := [.gives (.call "same" [.variable "y"])] } =
      [.call "same" [.variable "y"]] := by
  cbv

/-- All quantifiers and every fold kind participate, including binders below an operand. -/
theorem spec_capture_binder_kinds_zeuge :
    ([XKind.all, .any, .count, .foldAdd, .foldMin, .foldMax, .foldAnd, .foldOr].all fun kind =>
      let body := SExpr.built "wrapper" [.ext kind ["y", "slots"] [.variable "T", .tru]]
      beqSExpr (uSpecEin [("g", ["x"], body)] 20 (.call "g" [.variable "y"]))
        (.call "g" [.variable "y"])) = true := by
  cbv

/-- Reusing name collection must not hide the argument's outer-scope domain name. -/
theorem spec_capture_argument_domain_zeuge :
    specArgumentCaptures samePredicate
      (.ext .count ["y", "elems"] [.variable "y", .tru]) = true := by
  cbv

def deferredIndexContext : UCtx :=
  { argumentContext with
    names := ["i"]
    kinds := [.index 0]
    types := [.int 0 0]
    unknownRanges := ["i"]
    tabs := [{ name := "T", count := 10, cols := [("v", (0, 9))] }] }

/-- Ordinary table folds retain the field range; erased spec reads require index evidence. -/
theorem fold_deferred_table_index_zeuge :
    foldRange deferredIndexContext (.tab "T" "v" (.param "i")) = some (0, 9) ∧
    foldRangeWithIndexCheck deferredIndexContext true (.tab "T" "v" (.param "i")) = none ∧
    uSpecArgument deferredIndexContext "small" 1 (.atom "u8")
      (.field (.index (.field (.variable "T") "slots") (.variable "i")) "v") =
      .error "spec small: argument 1 does not fit its parameter type" := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

/-- Supplying real in-bounds index evidence keeps the spec argument accepted. -/
theorem fold_resolved_table_index_zeuge :
    uSpecArgument {deferredIndexContext with types := [.int 0 9], unknownRanges := []}
      "small" 1 (.atom "u8")
      (.field (.index (.field (.variable "T") "slots") (.variable "i")) "v") = .ok () := by
  cbv

/-- Array element ranges have the same split; the strict check also survives arithmetic nesting. -/
theorem fold_deferred_array_index_zeuge :
    let ctx := {deferredIndexContext with
      names := ["i", "a"], kinds := [.int, .wert], types := [.int 0 0, .arr (.int 2 7) 4]}
    foldRange ctx (.add (.idx (.param "a") (.param "i")) (.lit 1)) = some (3, 8) ∧
    foldRangeWithIndexCheck ctx true
      (.add (.idx (.param "a") (.param "i")) (.lit 1)) = none := by
  constructor <;> cbv

end Gabbro.Grammatik.Parser.Uebersetze
