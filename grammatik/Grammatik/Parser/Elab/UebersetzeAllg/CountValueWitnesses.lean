module

public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Elab.UebersetzeAllg.ZaehleZeuge
public import Grammatik.Parser.Elab.UebersetzeAllg.EingebautLesen
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
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

namespace Gabbro.Grammatik.Parser.UebersetzeAllg.CountValueWitnesses
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

attribute [local cbv_eval] uRechne.eq_def uSichert.eq_def uZSeite.eq_def
  seiteAltErg.eq_def ensAltErg.eq_def

attribute [local cbv_eval] lowWertE.eq_def lowEns.eq_def lowCmp.eq_def lowArrayValue.eq_def
  lowCountE.eq_def lowSeiteZ.eq_def

/-- A body count binds a number, which is then an arithmetic operand and the return value.
    On the zero-initialised fixture both slots match, so the hand-computed exit is 3. -/
def characters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'c', '1', '3', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T',
  ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ',
  ':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a',
  'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{',
  ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', ' ', 'l',
  'e', 't', ' ', 'n', ' ', '=', ' ', 'c', 'o', 'u', 'n', 't', ' ', 'i', ' ', 'i', 'n', ' ', 's', 'l',
  'o', 't', 's', ' ', 'o', 'f', ' ', 'T', ' ', ':', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', 'i',
  ']', '.', 'v', ' ', '=', '=', ' ', '0', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'n', ' ', '+',
  ' ', '1', ';', ' ', '}', ' ', '}']

def sourceText : String := String.ofList characters

theorem lexed : (lexL characters).toOption.isSome = true := by decide +kernel
def tokens := (lexL characters).toOption.get lexed

theorem parsed : (parseTopTief tokens).toOption.isSome = true := by decide +kernel
def items := (parseTopTief tokens).toOption.get parsed

theorem elaborated : (elabU (pre108 items)).toOption.isSome = true := by decide +kernel
def unit := (elabU (pre108 items)).toOption.get elaborated

theorem lowered : (UebersetzeAllg2.lowerAllg unit).toOption.isSome = true := by decide +kernel

/-- The complete text-to-G pipeline, with cached kernel reductions for each finite stage. -/
theorem count_value_source_zeuge : (uebersetzeAllg sourceText).toOption.isSome = true := by
  have l := except_ok_get lexed
  have p := except_ok_get parsed
  have e := except_ok_get elaborated
  have g := except_ok_get lowered
  have pipeline := uebersetzeAllg_von_zeichen l p e g
  rw [show sourceText = String.ofList characters from rfl, pipeline]
  rfl

/-- Value and predicate callers use the very same checked count term and exact range. -/
theorem count_value_range_zeuge :
    (lowWertE ZaehleZeuge.zU [] [] ZaehleZeuge.zF none
      (.zaehle "T" "x" ZaehleZeuge.zBody)).toOption.map (·.ty) = some (.int 0 4) := by cbv

/-- The body path still checks every predicate index, including on a refused count value. -/
theorem count_value_bounds_refused_zeuge :
    (lowWertE ZaehleZeuge.zU [] [] ZaehleZeuge.zF none
      (.zaehle "T" "x" (.cmp ">" (.tab "T" "v" (.lit 4)) (.lit 10)))) =
        .error "index outside count" := by cbv

/-- The existing open-domain refusal reaches the value path unchanged. -/
theorem count_value_open_refused_zeuge :
    lowWertE {ZaehleZeuge.zU with tabs := [
        { name := "T"
          count := 0
          cols := [("v", (0, 255))]
          von := some "provider" }]} [] [] ZaehleZeuge.zF none
      (.zaehle "T" "x" ZaehleZeuge.zBody) =
        .error "count over an open table has no static cardinality" := by cbv

/-- The value reader preserves the predicate reader's unheld-guard refusal. -/
theorem count_value_guard_refused_zeuge :
    uWertBody {EingebautLesen.lb with
        tabs := [EingebautLesen.tt]
        locks := [{ name := "L"
                    rank := 1
                    guard := ["T"] }]}
      EingebautLesen.zaehleSlots = .error "access without held guard" := by cbv

/-- Unmodelled finite-domain spellings are refused before either lowering caller. -/
theorem count_value_domain_refused_zeuge :
    uWertBody EingebautLesen.lb (.ext .count ["x", "unknown"] [.variable "T", .tru]) =
      .error "source export: count domain lacks a canonical G expansion" := by cbv

/-- The body reader cannot hide an entry snapshot inside the count predicate. -/
theorem count_value_old_refused_zeuge :
    uWertBody {EingebautLesen.lb with tabs := [EingebautLesen.tt]}
      (.ext .count ["x", "slots"] [.variable "T",
        .bin "==" (.old (.field (.index (.field (.variable "T") "slots") (.variable "x")) "v")) (.lit 0)]) =
      .error "old or result in a body" := by cbv

end Gabbro.Grammatik.Parser.UebersetzeAllg.CountValueWitnesses
