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

/-- The parser accepts the stage marker, but one-stage exported declarations
    cannot satisfy the canonical advance constructor's successor premise. -/
theorem advances_refused_zeuge :
    stufe "module m { impl fn f() { advances setup -> live; } }" =
      "elab: advances without G form: exported marks have only stage 0" := by
  rights_elab_error Phases.Inputs.advanceBare with_reason "advances without G form: exported marks have only stage 0"

/-! ## Wall 4: `own` pointers and the complement `~p` over the declared storage width -/

theorem own1_refused : stufe own1 = "elab: pointer rights without checked data/owner form: own" := by
  rights_elab_error Phases.Inputs.own1 with_reason "pointer rights without checked data/owner form: own"

/-- Both explicit read and write rights reach the existing checked table operations. -/
theorem rights_union_ok : stufe (tableRights "w+r") = "OK" := by
  rights_ok Phases.Inputs.rightsUnion

/-- A write-only pointer can store, but its subsequent read is refused. -/
theorem write_only_refused :
    stufe (tableRights "w") = "elab: read through pointer without read right" := by
  rights_elab_error Phases.Inputs.writeOnly with_reason "read through pointer without read right"

theorem write_only_store_ok : stufe storeOnly = "OK" := by
  rights_ok Phases.Inputs.storeOnly

theorem ownAtMarke_borrow_ok : stufe ownAtMarke = "OK" := by
  rights_ok Phases.Inputs.ownAtMarke

theorem ownAtMarke_ohneLeiht_refused :
    stufe ownAtMarkeOhneLeiht = "lower: access without held guard" := by
  rights_lower_error Phases.Inputs.ownAtMarkeOhneLeiht with_reason "access without held guard" at_member 0

theorem ownAtMarke_fremdLeiht_refused :
    stufe ownAtMarkeFremdLeiht = "elab: loan without owner: Fremd" := by
  rights_elab_error Phases.Inputs.ownAtMarkeFremdLeiht with_reason "loan without owner: Fremd"

theorem ownerOhneLinear_refused : stufe ownerOhneLinear = "elab: owner without declared linear mark: Marke" := by
  rights_elab_error Phases.Inputs.ownerOhneLinear with_reason "owner without declared linear mark: Marke"

theorem bnot1_ok : stufe bnot1 = "OK" := by
  rights_ok Phases.Inputs.bnot1

theorem bnot_schmal_ok : stufe bnot_schmal = "OK" := by
  rights_ok Phases.Inputs.bnot_schmal

theorem bnot_ausdruck_refused : stufe bnot_ausdruck = "elab: value without G form" := by
  rights_elab_error Phases.Inputs.bnot_ausdruck with_reason "value without G form"

theorem bnot_vorzeichen_refused :
    stufe bnot_vorzeichen = "elab: complement of unknown width" := by
  rights_elab_error Phases.Inputs.bnot_vorzeichen with_reason "complement of unknown width"

end Gabbro.Grammatik.Parser.UebersetzeProben11
