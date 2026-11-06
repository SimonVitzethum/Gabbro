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
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
public import Grammatik.GabbroV.Start.GvStartPflicht
import all Grammatik.Parser.Elab.Uebersetze.Tagged.ProbeResults
import all Grammatik.GabbroV.Start.GvStartPflichta
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.Uebersetze.Tagged.Initializers
import all Init.Data.Repr

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] Nat.log2_def
attribute [local cbv_eval] uSumKonst.eq_def uKonst.eq_def
attribute [local cbv_eval] Gabbro.Grammatik.GabbroV.konstWert.eq_def
  Gabbro.Grammatik.GabbroV.nutzKonst.eq_def
open scoped Gabbro.Grammatik.Parser.Uebersetze

namespace TypedInitializers

open Gabbro.Grammatik.GabbroV

def inner : USum := { name := "Inner", cases := [("InnerEmpty", none), ("InnerFlag", some .bool)] }
def outer : USum := { name := "Outer", cases := [("Empty", none), ("Flag", some .bool), ("Text", some (.str 8)), ("Nested", some (.sum inner.spec))] }
def schemas : List USum := [outer, inner]

theorem static_bool_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Flag" [.tru])) = .ok (.fall 1 (.wahr true)) := by cbv

theorem static_string_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["AB"] []])) =
      .ok (.fall 2 (.text [65, 66])) := by cbv

theorem static_nested_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Nested" [.call "InnerFlag" [.fls]])) =
      .ok (.fall 3 (.fall 1 (.wahr false))) := by cbv

theorem static_missing_payload_refused :
    uSumKonst [] schemas outer (.one (.variable "Flag")) =
      .error "missing tagged payload in static initializer" := by cbv

theorem static_extra_payload_refused :
    uSumKonst [] schemas outer (.one (.call "Empty" [.tru])) =
      .error "missing or extra tagged payload in static initializer" := by cbv

/-- The existing initial-world decoder retains the whole recursively typed value. -/
theorem static_nested_value_zeuge :
    ((uSumKonst [] schemas outer (.one (.call "Nested" [.call "InnerFlag" [.fls]]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) =
      some ⟨⟨3, by decide⟩, ⟨⟨1, by decide⟩, false⟩⟩ := by
  rw [static_nested_payload_zeuge]
  cbv

private def wrongInitializer : { actual : UKonst //
    uSumKonst [] schemas outer (.one (.call "Flag" [.lit 1])) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def longInitializer : { actual : UKonst //
    uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["123456789"] []])) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem static_wrong_payload_refused :
    ((uSumKonst [] schemas outer (.one (.call "Flag" [.lit 1]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) = none := by
  rw [wrongInitializer.property]
  cbv

theorem static_long_string_refused :
    ((uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["123456789"] []]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) = none := by
  rw [longInitializer.property]
  cbv

-- Retain the original two declarations, with no invented function or default unit.
private def staticItems : List SItemTief :=
  [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
    .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]
private def staticSchemas : { actual : List USum // uSums [] staticItems = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def staticRaw : { actual : List UGlob // uGlobs [] [] staticItems = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def staticTyped : { actual : List UGlob //
    uSumGlobs [] staticSchemas.val staticItems staticRaw.val = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
/-- Positive coverage is the actual static collector, before whole-unit function admission. -/
theorem static_collection_zeuge :
    ((uSums [] [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
      .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]).bind fun sums =>
      ((uGlobs [] [] [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
        .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]).bind
        (uSumGlobs [] sums [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
          .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false])).map
        (fun globs => globs.map (·.initK))) = .ok [.fall 0 (.wahr true)] := by
  change ((uSums [] staticItems).bind fun sums =>
    ((uGlobs [] [] staticItems).bind (uSumGlobs [] sums staticItems)).map
      (fun globs => globs.map (·.initK))) = _
  rw [staticSchemas.property, staticRaw.property]
  dsimp only [bind, Except.bind]
  rw [staticTyped.property]
  rfl

tagged_rejected static_without_fn from staticItems
/-- The unchanged global-only fixture is not an executable unit. -/
theorem static_export_without_function_refused :
    elabU [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
      .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false] =
      .error "unit without a fn" := static_without_fn

end TypedInitializers

end Gabbro.Grammatik.Parser.Uebersetze
