module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Phases
public import Grammatik.Parser.Elab.Proben.RightsConstants.Findings
public import Grammatik.Parser.Elab.Proben.RightsConstants.Rights
public import Grammatik.Parser.Elab.Proben.RightsConstants.Constants
public import Grammatik.Parser.Elab.Proben.RightsConstants.Ownership
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
import all Init.Data.Int.Repr
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

/-! ## Declared linear stages: two checked advances and terminal discharge -/

/-- Source text reaches canonical G through both consecutive stage changes. -/
theorem staged_owner_advances_twice_zeuge : stufe stagedOwner = "OK" := by
  decide +kernel

/-- The declaration exported from that same source has three stages. -/
theorem staged_owner_declared_count_zeuge : sourceMarkStageCounts stagedOwner = some [3] := by
  rights_counts Phases.Inputs.stagedOwner

/-- Counts are per nominal mark; an undeclared order retains the one-stage default. -/
theorem staged_counts_and_default_zeuge :
    sourceMarkStageCounts
      "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }" =
      some [1, 3, 2] := by
  rights_counts Phases.Inputs.stagedCounts

theorem staged_ordinary_advances_twice_zeuge : stufe stagedOrdinary = "OK" := by
  decide +kernel

/-- The declaration bound refuses an advance from the last stage by mark name. -/
theorem staged_last_stage_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;") =
      "lower: advance from last stage: Phase: hot" := by
  rights_lower_error Phases.Inputs.stagedLast with_reason "advance from last stage: Phase: hot" at_member 0

/-- Forward skips and backward steps never manufacture a stage. -/
theorem staged_skip_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> hot;") =
      "lower: advance is not the next declared stage: cold -> hot" := by
  rights_lower_error Phases.Inputs.stagedSkip with_reason "advance is not the next declared stage: cold -> hot" at_member 0

theorem staged_backward_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances warm -> cold;") =
      "lower: advance is not the next declared stage: warm -> cold" := by
  rights_lower_error Phases.Inputs.stagedBackward with_reason "advance is not the next declared stage: warm -> cold" at_member 0

/-- A valid declared edge does not confer possession of its input stage. -/
theorem staged_wrong_input_refused_zeuge :
    stufe (stagedOwnerSource "advances warm -> hot;") =
      "lower: advance without held stage: Phase: warm" := by
  rights_lower_error Phases.Inputs.stagedWrongInput with_reason "advance without held stage: Phase: warm" at_member 0

theorem staged_repeated_step_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances cold -> warm;") =
      "lower: advance without held stage: Phase: cold" := by
  rights_lower_error Phases.Inputs.stagedRepeated with_reason "advance without held stage: Phase: cold" at_member 0

theorem staged_unknown_label_refused_zeuge :
    stufe (stagedOwnerSource "advances missing -> warm;") =
      "lower: advance of unknown stage: missing" := by
  rights_lower_error Phases.Inputs.stagedUnknown with_reason "advance of unknown stage: missing" at_member 0

theorem staged_borrowed_refused_zeuge :
    stufe stagedBorrowed = "lower: advance of borrowed mark: Phase" := by
  rights_lower_error Phases.Inputs.stagedBorrowed with_reason "advance of borrowed mark: Phase" at_member 0

theorem staged_ambiguous_refused_zeuge :
    stufe stagedAmbiguous = "lower: advance of ambiguous stage: cold" := by
  rights_lower_error Phases.Inputs.stagedAmbiguous with_reason "advance of ambiguous stage: cold" at_member 0

theorem staged_duplicate_label_refused_zeuge :
    stufe stagedDuplicate = "elab: duplicate stage in linear mark: Phase" := by
  rights_elab_error Phases.Inputs.stagedDuplicate with_reason "duplicate stage in linear mark: Phase"

end Gabbro.Grammatik.Parser.UebersetzeProben11
