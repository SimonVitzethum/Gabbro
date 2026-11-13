module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.LocalBindings
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import Grammatik.Kern.Taktik.KernelRfl
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
open Gabbro.Grammatik.Parser.UebersetzeAllg

def truthRecord : URecord :=
  { name := "POut", identity := 7, fields := [("pos", .int 0 63), ("ok", .bool)] }

def truthContext : UCtx :=
  { names := ["r", "flag"], kinds := [.wert, .bool], types := [truthRecord.ty, .bool],
    tabs := [], locks := [], held := [], res := none, fname := "sample", alias := [], lits := [],
    records := [truthRecord], narrow := true }

def truthFunction : UFn :=
  { name := "sample", params := [("r", truthRecord.ty), ("flag", .bool)], kinds := [.wert, .bool],
    res := none, held := [], puts := [], gives := [], body := [], ret := .empty }

def truthUnit : UProg :=
  { tabs := [], locks := [], fns := [truthFunction], records := [truthRecord] }

/-- The field's declared Boolean type selects the predicate path directly. -/
theorem bool_field_zeuge :
    uBool truthContext (.field (.variable "r") "ok") =
      .ok (.cmp "==" (.field (.param "r") "ok") (.truth true)) := by kernel_rfl

/-- An inferred binding keeps Boolean kind and type, including a mutable binding. -/
theorem bool_binding_zeuge :
    (uBindWertAllg truthContext false "b" none (.field (.variable "r") "ok")).map
      (fun (statement, ctx) => (statement, ctx.kinds.head?, ctx.types.head?)) =
      .ok (.bindB "b" (.cmp "==" (.field (.param "r") "ok") (.truth true)),
        some .bool, some .bool) ∧
    (uBindWertAllg truthContext true "b" none (.field (.variable "r") "ok")).map
      (fun (_, ctx) => ctx.muts) = .ok ["b"] := by
  constructor <;> kernel_rfl

/-- Both literals and existing Boolean locals construct the field without scalar conversion. -/
theorem bool_construction_zeuge :
    uRecordSide truthContext .tru (fun source _ => uWertBody truthContext source) = .ok (.truth true) ∧
    uRecordSide truthContext (.variable "flag") (fun source _ => uWertBody truthContext source) =
      .ok (.param "flag") ∧
    uRecordSide truthContext (.field (.variable "r") "ok") (fun source _ => uWertBody truthContext source) =
      .ok (.field (.param "r") "ok") := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

/-- The real typed field and Boolean comparison lowerers compose, on a nonempty product. -/
theorem bool_projection_lower_zeuge :
    (lowEns truthUnit [truthRecord.ty, .bool] [] truthFunction none
      (.cmp "==" (.field (.param "r") "ok") (.truth true))).toBool = true := by
  kernel_rfl

/-- The shared comparison function is exercised on unequal truth values, with its gate open. -/
theorem lowVglWert_zeuge :
    lowVglWert truthUnit (Γ := []) (Λ := []) "=="
      (.ok ⟨.bool, Expr.tru⟩) (.ok ⟨.bool, Expr.fls⟩) =
      .ok (Expr.wenn Expr.tru Expr.fls (Expr.not Expr.fls)) := by kernel_rfl

/-- Numeric fields still cannot be predicates, directly or through an inferred local. -/
theorem numeric_field_refused_zeuge :
    uBool truthContext (.field (.variable "r") "pos") =
      .error "ensures clause without G form" ∧
    (uBindWertAllg truthContext false "b" none (.field (.variable "r") "pos")).bind
      (fun (_, ctx) => uBool ctx (.variable "b")) = .error "number as a truth value" := by
  constructor <;> kernel_rfl

end Gabbro.Grammatik.Parser.Uebersetze
