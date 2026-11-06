module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Phases
import all Grammatik.Kern.Syntax.Typen.Shape
import all Grammatik.Parser.Elab.Uebersetze.Kontext.Eigner
import all Grammatik.Parser.Elab.Generic.SignatureData
import all Grammatik.Parser.Elab.Generic.C09Flows
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
import all Grammatik.Parser.Elab.UebersetzeAllg2.Marken
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

-- Evaluate the selected node of the canonical typed mutual before projecting
-- its result, as in the generic count-reader witnesses.
attribute [local cbv_eval] lowWertE.eq_def lowCmp.eq_def lowEns.eq_def
  lowArrayValue.eq_def lowSeiteZ.eq_def

/-! ## C09: owner mint and linear handoff -/

theorem mintAtMarke_ok : stufe mintAtMarke = "OK" := by
  rights_ok Phases.Inputs.mintAtMarke

theorem moveAtMarke_ok : stufe moveAtMarke = "OK" := by
  rights_ok Phases.Inputs.moveAtMarke

theorem moveReasonAtMarke_ok : stufe moveReasonAtMarke = "OK" := by
  rights_ok Phases.Inputs.moveReasonAtMarke

theorem mintTwice_refused : stufe mintTwice = "elab: duplicate mint: Marke" := by
  rights_elab_error Phases.Inputs.mintTwice with_reason "duplicate mint: Marke"

theorem mintFremd_refused : stufe mintFremd = "elab: mint without owner: Fremd" := by
  rights_elab_error Phases.Inputs.mintFremd with_reason "mint without owner: Fremd"

theorem moveFremd_refused : stufe moveFremd = "elab: move without owner: Fremd" := by
  rights_elab_error Phases.Inputs.moveFremd with_reason "move without owner: Fremd"

theorem moveBorrowed_refused :
    stufe moveBorrowed = "elab: mark both borrowed and moved: Marke" := by
  rights_elab_error Phases.Inputs.moveBorrowed with_reason "mark both borrowed and moved: Marke"

theorem moveDropped_refused :
    stufe moveDropped = "lower: call without held mark" := by
  rights_lower_error Phases.Inputs.moveDropped with_reason "call without held mark" at_member 1

/-! ## C09 terminal moves and C16 ordinary consumption -/

theorem terminalMoveRetires_zeuge : stufe terminalMoveRetires = "OK" := by
  rights_ok Phases.Inputs.terminalMoveRetires

/-- Omitting retire leaves an input outside `ende`; exact return inventory
    refuses the body even though the terminal call signature is valid. -/
theorem terminalMoveDropped_refused :
    stufe (terminalMoveSource "") = "lower: lower: return without produced marks" := by
  rights_lower_error Phases.Inputs.terminalMoveDropped with_reason "lower: return without produced marks" at_member 0

theorem borrowedRetire_refused :
    stufe borrowedRetire = "lower: retire of borrowed mark: Marke" := by
  rights_lower_error Phases.Inputs.borrowedRetire with_reason "retire of borrowed mark: Marke" at_member 0

theorem unheldRetire_refused :
    stufe unheldRetire = "lower: retire without held mark: Marke" := by
  rights_lower_error Phases.Inputs.unheldRetire with_reason "retire without held mark: Marke" at_member 0

theorem repeatedRetire_refused :
    stufe (terminalMoveSource "retires Marke; retires Marke;") =
      "lower: retire without held mark: Marke" := by
  rights_lower_error Phases.Inputs.repeatedRetire with_reason "retire without held mark: Marke" at_member 0

theorem ordinaryRetire_zeuge : stufe ordinaryRetire = "OK" := by
  rights_ok Phases.Inputs.ordinaryRetire

theorem handbackRetire_refused :
    stufe handbackRetire = "lower: lower: return without produced marks" := by
  rights_lower_error Phases.Inputs.handbackRetire with_reason "lower: return without produced marks" at_member 0

theorem terminalReasonRetire_ok : stufe terminalReasonRetire = "OK" := by
  rights_ok Phases.Inputs.terminalReasonRetire

end Gabbro.Grammatik.Parser.UebersetzeProben11
