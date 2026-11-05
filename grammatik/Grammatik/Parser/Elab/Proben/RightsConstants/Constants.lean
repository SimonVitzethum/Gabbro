module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Phases
import all Grammatik.Kern.Syntax.Typen.Shape
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.Konst.Ersetzung
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Konst.Scope
import all Grammatik.Parser.Elab.Konst.Replacement
import all Grammatik.Parser.Elab.Konst.Scalar.Model
import all Grammatik.Parser.Elab.Konst.Scalar.Expression
import all Grammatik.Parser.Elab.Konst.Scalar.Names
import all Grammatik.Parser.Elab.Konst.Scalar.Arguments
import all Grammatik.Parser.Elab.Konst.Scalar.KExpr
import all Grammatik.Parser.Elab.Konst.Scalar.Export
import all Grammatik.Parser.Elab.Konst.Values.Expression
import all Grammatik.Parser.Elab.Konst.Values.Quotation
import all Grammatik.Parser.Elab.Konst.Values.Export
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
namespace Gabbro.Grammatik.Parser.UebersetzeProben11
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)
open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
set_option maxRecDepth 100000

-- Preserve the original logarithm equation and select only the used canonical fuel operations.
attribute [local cbv_eval] Nat.log2_def
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

/-! ## Wall 5: compile-time constants -- expressions and `const fn` calls -/

theorem konst_ausdruck_ok : stufe konst_ausdruck = "OK" := by
  rights_ok Phases.Inputs.konst_ausdruck

theorem konst_fn_ok : stufe konst_fn = "OK" := by
  rights_ok Phases.Inputs.konst_fn

theorem konst_ueberlauf_refused : stufe konst_ueberlauf = "elab: name unknown: X" := by
  rights_elab_error Phases.Inputs.konst_ueberlauf with_reason "name unknown: X"

theorem konst_negativ_refused : stufe konst_negativ = "elab: name unknown: Y" := by
  rights_elab_error Phases.Inputs.konst_negativ with_reason "name unknown: Y"

theorem konst_argument_refused : stufe konst_argument =
    "elab: const argument failure at `doppelt`: const argument is not a compile-time value in its declared range" := by
  rights_elab_error Phases.Inputs.konst_argument with_reason
    "const argument failure at `doppelt`: const argument is not a compile-time value in its declared range"

end Gabbro.Grammatik.Parser.UebersetzeProben11
