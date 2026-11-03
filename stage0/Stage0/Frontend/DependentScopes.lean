module
public import Stage0.Frontend.DependentScopesa
public import Stage0.Frontend.Environments
public import Stage0.Frontend.AliasOrder
public import Stage0.Frontend.AliasMeaning
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
theorem elaborateScopes_dependencies (items : List SItemTief) (result : DerivedScopes items)
    (h : elaborateScopes items = .ok result) :
    AliasAcyclic items ∧ (aliasNames items).Nodup := by
  unfold elaborateScopes at h
  cases ho : orderAliases items with
  | error e =>
    rw [ho] at h
    change Except.error e = Except.ok result at h
    contradiction
  | ok order => exact ⟨order.acyclic, order.unique⟩

/-- Preserve complete conservative scopes once every alias resolves and its graph is checked. -/
theorem elaborateScopes_preserves (items : List SItemTief) (result : DerivedScopes items)
    (order : AliasOrder items) (ho : orderAliases items = .ok order)
    (h : deriveScopes items = .ok result)
    (complete : (constantFunctions result.scope.types items).length = result.scope.functions.length)
    (resolved : aliasesResolved result.scope.declared items = true)
    (meaning : items.all (checkAliasMeaning result.scope.types) = true) :
    elaborateScopes items = .ok result := by
  simp [elaborateScopes, ho, h, complete, resolved, meaning, Except.toOption, Option.filter]
  rfl

/-- The conservative-preservation premises hold jointly for real alias declarations and a
    computed scalar; the complete previous scope is retained, not just its final value. -/
theorem elaborateScopes_preserves_zeuge :
    let items := [SItemTief.typeT [] "Small" [] [] (some (.atom "u8")),
      .typeT [] "Alias" [] [] (some (.atom "Small")),
      .constT "ANSWER" (.atom "Alias") (.one (.bin "+" (.lit 40) (.lit 2)))]
    ∃ result, deriveScopes items = .ok result ∧ elaborateScopes items = .ok result ∧
      result.scope.values = [("ANSWER", 42)] := by
  dsimp only
  refine ⟨(deriveScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · apply elaborateScopes_preserves _ _ ((orderAliases _).toOption.get (by decide +kernel))
    · exact Gabbro.Grammatik.except_ok_get _
    · exact Gabbro.Grammatik.except_ok_get _
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · decide +kernel

/-- A computed alias-typed constant discovers a dependent range and a further alias chain;
    all final bindings and ranges come from the strict original fold, not discovery output. -/
theorem elaborateScopes_dependent_zeuge :
    let items := [SItemTief.typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .typeT [] "Alias" [] [] (some (.atom "Bound")),
      .constT "ANSWER" (.atom "Alias") (.one (.variable "LIMIT"))]
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("LIMIT", 42), ("ANSWER", 42)] ∧
      result.scope.declared = [("Base", (0, 255)), ("Bound", (0, 42)), ("Alias", (0, 42))] ∧
      (deriveScopes items).toOption.isNone = true := by
  dsimp only
  refine ⟨(elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

/-- A constant-backed signature retains the exact narrower parameter/result bounds, distinct
    from the caller's wider range, and is derived from final original values. -/
theorem elaborateScopes_signature_zeuge :
    let bound := STyp.range (.atom "u8") (.lit 0) (.variable "LIMIT") false
    let items := [SItemTief.typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .fnT ⟨"const", "identity", [("x", bound)], some bound, none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "ANSWER" (.atom "Base") (.one (.call "identity" [.lit 42]))]
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("LIMIT", 42), ("ANSWER", 42)] ∧
      result.scope.functions.map (fun f => (f.name, f.params, f.erg)) =
        [("identity", [("x", (0, 42))], (0, 42))] ∧ result.scope.functionsUseValues = true := by
  dsimp only
  refine ⟨(elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

/-- Array-only calls expose incomplete function discovery despite a successful scalar fold.
    The extended path must supply the exact bounded signature to the canonical array evaluator. -/
theorem elaborateScopes_signature_array_zeuge :
    let bound := STyp.range (.atom "u8") (.lit 0) (.variable "LIMIT") false
    let items := [SItemTief.typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .fnT ⟨"const", "identity", [("x", bound)], some bound, none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "VALUES" (.array (.atom "Base") (.lit 1)) (.rows [.one (.call "identity" [.lit 42])])]
    ∃ old result, deriveScopes items = .ok old ∧ old.scope.functions.length = 0 ∧
      elaborateScopes items = .ok result ∧ result.scope.values = [("LIMIT", 42)] ∧
      result.scope.functions.map (fun f => (f.name, f.params, f.erg)) =
        [("identity", [("x", (0, 42))], (0, 42))] ∧ result.scope.functionsUseValues = true := by
  dsimp only
  refine ⟨(deriveScopes _).toOption.get (by decide +kernel),
    (elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

/-- A bounded const call supplies a later alias bound. Discovery must advance beyond LIMIT
    alone; acceptance still records exact original values, final aliases and bounded signatures. -/
theorem elaborateScopes_call_bound_zeuge :
    let bound := STyp.range (.atom "u8") (.lit 0) (.variable "LIMIT") false
    let items := [SItemTief.typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .fnT ⟨"const", "identity", [("x", bound)], some bound, none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "BOUND" (.atom "Base") (.one (.call "identity" [.lit 42])),
      .typeT [] "Result" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "BOUND") false)),
      .constT "ANSWER" (.atom "Result") (.one (.variable "BOUND"))]
    nextCandidates items [("LIMIT", 42)] = [("LIMIT", 42), ("BOUND", 42)] ∧
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("LIMIT", 42), ("BOUND", 42), ("ANSWER", 42)] ∧
      result.scope.declared = [("Base", (0, 255)), ("Result", (0, 42))] ∧
      result.scope.functions.map (fun f => (f.name, f.params, f.erg)) =
        [("identity", [("x", (0, 42))], (0, 42))] ∧
      result.scope.functionsUseValues = true ∧ (deriveScopes items).toOption.isNone = true := by
  dsimp only
  refine ⟨by decide +kernel, (elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

/-- A custom negative range cannot be re-encoded by the frozen collector, but its canonical
    value must still seed dependent aliases. Acceptance rechecks all original scalar declarations. -/
theorem elaborateScopes_custom_negative_bound_zeuge :
    let items := [SItemTief.typeT [] "Small" [] []
        (some (.range (.atom "i8") (.un "-" (.lit 10)) (.lit 100) false)),
      .fnT ⟨"const", "negative", [], some (.atom "Small"), none, []⟩
        (.block [] (some (.ret (some (.bin "-" (.lit 0) (.lit 1)))))),
      .constT "NEGATIVE" (.atom "Small") (.one (.call "negative" [])),
      .typeT [] "Bound" [] []
        (some (.range (.atom "i8") (.variable "NEGATIVE") (.lit 100) false)),
      .constT "ANSWER" (.atom "Bound") (.one (.lit 42))]
    nextCandidates items [] = [("NEGATIVE", -1)] ∧
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("NEGATIVE", -1), ("ANSWER", 42)] ∧
      result.scope.declared = [("Small", (-10, 100)), ("Bound", (-1, 100))] ∧
      result.scope.functions.map (fun f => (f.name, f.params, f.erg)) =
        [("negative", [], (-10, 100))] ∧
      result.scope.functionsUseValues = true ∧ (deriveScopes items).toOption.isNone = true := by
  dsimp only
  refine ⟨by decide +kernel, (elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals decide +kernel

/-- Earlier computed scalars resolve inline scalar ranges and then dependent aliases.
    The final original fold retains all values and the exact exclusive upper bound. -/
theorem elaborateScopes_inline_range_zeuge :
    let inlineType := STyp.range (.atom "u8") (.lit 0)
      (.bin "+" (.variable "LIMIT") (.lit 1)) true
    let items := [SItemTief.typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .constT "BOUND" inlineType (.one (.variable "LIMIT")),
      .typeT [] "Result" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "BOUND") false)),
      .constT "ANSWER" (.atom "Result") (.one (.variable "BOUND"))]
    nextCandidates items [] = [("LIMIT", 42), ("BOUND", 42)] ∧
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("LIMIT", 42), ("BOUND", 42), ("ANSWER", 42)] ∧
      result.scope.declared = [("Base", (0, 255)), ("Result", (0, 42))] ∧
      result.scope.functionsUseValues = true ∧
      (uFeldTyp result.scope.declared inlineType).toOption.isNone = true ∧
      uTyp (result.scope.declared ++ [("LIMIT", (42, 42))]) [] [] [] inlineType = .ok (.int 0 42) := by
  dsimp only
  refine ⟨by decide +kernel, (elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  all_goals first | rfl | decide +kernel

/-- A reverse alias chain with a computed bound supplies exact const-function signatures and
    scalar values. Original-order discovery refuses; the new certified schedule succeeds. -/
theorem elaborateScopes_forward_zeuge :
    let items := [SItemTief.typeT [] "Result" [] [] (some (.atom "Bound")),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .typeT [] "Base" [] [] (some (.atom "u8")),
      .constT "LIMIT" (.atom "Base") (.one (.bin "+" (.lit 40) (.lit 2))),
      .fnT ⟨"const", "identity", [("x", .atom "Result")], some (.atom "Result"), none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "ANSWER" (.atom "Result") (.one (.call "identity" [.variable "LIMIT"]))]
    ∃ result, elaborateScopes items = .ok result ∧
      result.scope.values = [("LIMIT", 42), ("ANSWER", 42)] ∧
      result.scope.declared = [("Bound", (0, 42)), ("Result", (0, 42)), ("Base", (0, 255))] ∧
      result.scope.functions.map (fun f => (f.name, f.params, f.erg)) =
        [("identity", [("x", (0, 42))], (0, 42))] ∧
      (discoverScopes items (items.length + 1) (prepare items).initial).toOption.isNone = true ∧
      AliasAcyclic items := by
  dsimp only
  refine ⟨(elaborateScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (elaborateScopes_dependencies _ ((elaborateScopes _).toOption.get (by decide +kernel))
      (Gabbro.Grammatik.except_ok_get _)).1

end Gabbro.Stage0.Frontend
