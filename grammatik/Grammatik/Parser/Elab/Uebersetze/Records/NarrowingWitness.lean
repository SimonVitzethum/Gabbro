module
public import Grammatik.Parser.Elab.Uebersetze.Records.Narrowing
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.ToString.Basic
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


namespace Gabbro.Grammatik.Parser.Uebersetze.FieldNarrowing

set_option maxRecDepth 2000

def selected : SExpr := .field (.variable "entry") "pos"
def failure : SAnw := .block [] (some (.ret (some (.lit 7))))
def returning (value : SExpr) : Option SEnde := some (.ret (some value))
def snapshot : String := "#fieldNarrow:0"

/-- The original field is evaluated once; only the successful final return is rewritten. -/
theorem explicit_else_snapshot_zeuge :
    expand 20 ["entry"] 0 (.block [.trim selected "0 .. 63" failure] (returning selected)) =
      (.block [.bind false snapshot none selected,
        .trim (.variable snapshot) "0 .. 63" failure] (returning (.variable snapshot)), 1) := by
  kernel_rfl

/-- Required narrowing keeps its capacity duty, without manufacturing an else branch. -/
theorem required_snapshot_zeuge :
    expand 20 ["entry"] 0 (.block [.trimReq selected "0 .. 63"] (returning selected)) =
      (.block [.bind false snapshot none selected,
        .trimReq (.variable snapshot) "0 .. 63"] (returning (.variable snapshot)), 1) := by
  kernel_rfl

/-- An assignment is a barrier and its target is never rewritten to the immutable snapshot. -/
theorem mutation_barrier_zeuge :
    replaceRun selected "entry" snapshot [.set selected "=" (.lit 100), .ret (some selected)] =
      ([.set selected "=" (.lit 100), .ret (some selected)], false) := by
  kernel_rfl

/-- A compound field write uses the checked old value, keeps its target, and ends the fact. -/
theorem first_write_value_zeuge :
    replaceRun selected "entry" snapshot [.set selected "+=" (.lit 1), .ret (some selected)] =
      ([.set selected "=" (.bin "+" (.variable snapshot) (.lit 1)), .ret (some selected)], false) := by
  kernel_rfl

/-- Reading the narrowed field as a store index does not change its containing record. -/
theorem indexed_store_snapshot_zeuge :
    replaceRun selected "entry" snapshot
      [.set (.field (.index (.field (.variable "T") "slots") selected) "value") "=" (.lit 23)] =
      ([.set (.field (.index (.field (.variable "T") "slots") (.variable snapshot)) "value") "=" (.lit 23)],
        true) := by
  kernel_rfl

theorem assignment_root_zeuge :
    uAssignmentRoots (.field (.index (.field (.variable "T") "slots") selected) "value") = ["T"] := by
  kernel_rfl

/-- A different lexical record with the same source name cannot inherit a refinement. -/
theorem shadow_barrier_zeuge :
    replaceRun selected "entry" snapshot
      [.bind false "entry" none (.variable "other"), .ret (some selected)] =
      ([.bind false "entry" none (.variable "other"), .ret (some selected)], false) := by
  kernel_rfl

/-- Historical reads remain historical, even when the current field is narrowed. -/
theorem historical_read_zeuge : replace selected snapshot (.old selected) = .old selected := by
  kernel_rfl

/-- An unknown body is a conservative barrier. -/
theorem unknown_barrier_zeuge :
    replaceRun selected "entry" snapshot [.other "unknown", .ret (some selected)] =
      ([.other "unknown", .ret (some selected)], false) := by
  kernel_rfl

/-- A field rooted outside the local scope is never turned into a stable local snapshot. -/
theorem global_field_unchanged_zeuge :
    expand 20 [] 0 (.block [.trim selected "0 .. 63" failure] (returning selected)) =
      (.block [.trim selected "0 .. 63" failure] (returning selected), 0) := by
  kernel_rfl

end Gabbro.Grammatik.Parser.Uebersetze.FieldNarrowing
