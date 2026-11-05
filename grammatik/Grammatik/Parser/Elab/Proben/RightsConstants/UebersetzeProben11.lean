/-
  File:      Grammatik/Parser/Elab/UebersetzeProben11.lean
  Subject:   Walls 4 and 5: `own`/`~p` and constants (split from `UebersetzeProben`: the kernel probes of one file share one memory budget).
-/
module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Data
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

set_option maxRecDepth 100000

/-- The parser accepts the stage marker, but one-stage exported declarations
    cannot satisfy the canonical advance constructor's successor premise. -/
theorem advances_refused_zeuge :
    stufe "module m { impl fn f() { advances setup -> live; } }" =
      "elab: advances without G form: exported marks have only stage 0" := by
  decide +kernel

/-! ## Wall 4: `own` pointers and the complement `~p` over the declared storage width -/

theorem own1_refused : stufe own1 = "elab: pointer rights without checked data/owner form: own" := by
  decide +kernel

/-- Both explicit read and write rights reach the existing checked table operations. -/
theorem rights_union_ok : stufe (tableRights "w+r") = "OK" := by decide +kernel

/-- A write-only pointer can store, but its subsequent read is refused. -/
theorem write_only_refused :
    stufe (tableRights "w") = "elab: read through pointer without read right" := by
  decide +kernel

theorem write_only_store_ok : stufe storeOnly = "OK" := by decide +kernel

theorem ownAtMarke_borrow_ok : stufe ownAtMarke = "OK" := by
  decide +kernel

theorem ownAtMarke_ohneLeiht_refused :
    stufe ownAtMarkeOhneLeiht = "lower: access without held guard" := by
  decide +kernel

theorem ownAtMarke_fremdLeiht_refused :
    stufe ownAtMarkeFremdLeiht = "elab: loan without owner: Fremd" := by
  decide +kernel

theorem ownerOhneLinear_refused : stufe ownerOhneLinear = "elab: owner without declared linear mark: Marke" := by
  decide +kernel

theorem bnot1_ok : stufe bnot1 = "OK" := by decide +kernel

theorem bnot_schmal_ok : stufe bnot_schmal = "OK" := by decide +kernel

theorem bnot_ausdruck_refused : stufe bnot_ausdruck = "elab: value without G form" := by decide +kernel

theorem bnot_vorzeichen_refused :
    stufe bnot_vorzeichen = "elab: complement of unknown width" := by decide +kernel

/-! ## Wall 5: compile-time constants -- expressions and `const fn` calls -/

theorem konst_ausdruck_ok : stufe konst_ausdruck = "OK" := by decide +kernel

theorem konst_fn_ok : stufe konst_fn = "OK" := by decide +kernel

theorem konst_ueberlauf_refused : stufe konst_ueberlauf = "elab: name unknown: X" := by decide +kernel

theorem konst_negativ_refused : stufe konst_negativ = "elab: name unknown: Y" := by decide +kernel

theorem konst_argument_refused : stufe konst_argument = "elab: name unknown: C" := by decide +kernel

/-! ## C09: owner mint and linear handoff -/

theorem mintAtMarke_ok : stufe mintAtMarke = "OK" := by
  decide +kernel

theorem moveAtMarke_ok : stufe moveAtMarke = "OK" := by
  decide +kernel

theorem moveReasonAtMarke_ok : stufe moveReasonAtMarke = "OK" := by
  decide +kernel

theorem mintTwice_refused : stufe mintTwice = "elab: duplicate mint: Marke" := by
  decide +kernel

theorem mintFremd_refused : stufe mintFremd = "elab: mint without owner: Fremd" := by
  decide +kernel

theorem moveFremd_refused : stufe moveFremd = "elab: move without owner: Fremd" := by
  decide +kernel

theorem moveBorrowed_refused :
    stufe moveBorrowed = "elab: mark both borrowed and moved: Marke" := by
  decide +kernel

theorem moveDropped_refused :
    stufe moveDropped = "lower: call without held mark" := by
  decide +kernel

/-! ## C09 terminal moves and C16 ordinary consumption -/

theorem terminalMoveRetires_zeuge : stufe terminalMoveRetires = "OK" := by
  decide +kernel

/-- Omitting retire leaves an input outside `ende`; exact return inventory
    refuses the body even though the terminal call signature is valid. -/
theorem terminalMoveDropped_refused :
    stufe (terminalMoveSource "") = "lower: lower: return without produced marks" := by
  decide +kernel

theorem borrowedRetire_refused :
    stufe borrowedRetire = "lower: retire of borrowed mark: Marke" := by
  decide +kernel

theorem unheldRetire_refused :
    stufe unheldRetire = "lower: retire without held mark: Marke" := by
  decide +kernel

theorem repeatedRetire_refused :
    stufe (terminalMoveSource "retires Marke; retires Marke;") =
      "lower: retire without held mark: Marke" := by
  decide +kernel

theorem ordinaryRetire_zeuge : stufe ordinaryRetire = "OK" := by
  decide +kernel

theorem handbackRetire_refused :
    stufe handbackRetire = "lower: lower: return without produced marks" := by
  decide +kernel

theorem terminalReasonRetire_ok : stufe terminalReasonRetire = "OK" := by
  decide +kernel

/-! ## Declared linear stages: two checked advances and terminal discharge -/

/-- Source text reaches canonical G through both consecutive stage changes. -/
theorem staged_owner_advances_twice_zeuge : stufe stagedOwner = "OK" := by
  decide +kernel

/-- The declaration exported from that same source has three stages. -/
theorem staged_owner_declared_count_zeuge : sourceMarkStageCounts stagedOwner = some [3] := by
  decide +kernel

/-- Counts are per nominal mark; an undeclared order retains the one-stage default. -/
theorem staged_counts_and_default_zeuge :
    sourceMarkStageCounts
      "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }" =
      some [1, 3, 2] := by
  decide +kernel

theorem staged_ordinary_advances_twice_zeuge : stufe stagedOrdinary = "OK" := by
  decide +kernel

/-- The declaration bound refuses an advance from the last stage by mark name. -/
theorem staged_last_stage_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;") =
      "lower: advance from last stage: Phase: hot" := by
  decide +kernel

/-- Forward skips and backward steps never manufacture a stage. -/
theorem staged_skip_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> hot;") =
      "lower: advance is not the next declared stage: cold -> hot" := by
  decide +kernel

theorem staged_backward_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances warm -> cold;") =
      "lower: advance is not the next declared stage: warm -> cold" := by
  decide +kernel

/-- A valid declared edge does not confer possession of its input stage. -/
theorem staged_wrong_input_refused_zeuge :
    stufe (stagedOwnerSource "advances warm -> hot;") =
      "lower: advance without held stage: Phase: warm" := by
  decide +kernel

theorem staged_repeated_step_refused_zeuge :
    stufe (stagedOwnerSource "advances cold -> warm; advances cold -> warm;") =
      "lower: advance without held stage: Phase: cold" := by
  decide +kernel

theorem staged_unknown_label_refused_zeuge :
    stufe (stagedOwnerSource "advances missing -> warm;") =
      "lower: advance of unknown stage: missing" := by
  decide +kernel

theorem staged_borrowed_refused_zeuge :
    stufe stagedBorrowed = "lower: advance of borrowed mark: Phase" := by
  decide +kernel

theorem staged_ambiguous_refused_zeuge :
    stufe stagedAmbiguous = "lower: advance of ambiguous stage: cold" := by
  decide +kernel

theorem staged_duplicate_label_refused_zeuge :
    stufe stagedDuplicate = "elab: duplicate stage in linear mark: Phase" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben11
