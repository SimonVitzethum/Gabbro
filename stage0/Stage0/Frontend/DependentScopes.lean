import Stage0.Frontend.Environments
import Stage0.Frontend.AliasOrder
import Stage0.Frontend.AliasMeaning

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Discovery uses candidate scalar bounds in const-function signatures. Its partial collector
    output remains untrusted until resolveCandidate rechecks the full original source fold.
    Reuse canonical typed evaluation directly: custom-range negatives need no source materialization.
    Failed declarations are skipped only here; final validation checks every original scalar. -/
def nextCandidates (items : List SItemTief) (values : List (String × Int))
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    List (String × Int) :=
  let expanded := aliases values [] order.val
  let env := uAliase values expanded
  let fns := constantFunctions (env ++ values.map (fun c => (c.1, (c.2, c.2)))) expanded
  items.foldl (fun collected item => (typedItem env fns collected item).getD collected) []

/-- A new candidate cannot hide unresolved integer alias declarations, including unused cycles. -/
def aliasesResolved (env : List (String × (Int × Int))) (items : List SItemTief) : Bool :=
  items.all fun
    | .typeT _ name [] _ (some (.atom _)) | .typeT _ name [] _ (some (.range _ _ _ _)) =>
      (env.find? (fun entry => strEq entry.1 name)).isSome
    | _ => true

/-- Validate a discovery candidate by re-evaluating every original scalar at its exact original
    type and then comparing the complete alias fold against those final, ordered values. -/
def resolveCandidate (items : List SItemTief) (candidate : List (String × Int))
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    Except String (DerivedScopes items) :=
  let expanded := aliases candidate [] order.val
  let env := uAliase candidate expanded
  let tentativeFns := constantFunctions (env ++ candidate.map (fun c => (c.1, (c.2, c.2)))) items
  if !aliasesResolved env items then .error "compile-time aliases contain unresolved dependencies or cycles"
  else match typedConstants env tentativeFns items [] with
  | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
  | some preliminary =>
    let fns := constantFunctions (env ++ preliminary.map (fun c => (c.1, (c.2, c.2)))) items
    match h : typedConstants env fns items [] with
    | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
    | some values =>
      if hs : values = preliminary then
        if ha : env = order.val.foldl (aliasStep values) [] then
          let scope : Scopes items := ⟨values, env, fns, values, Or.inr rfl, true, order.val, order.property, ha,
            by simp only [↓reduceIte, hs]; rfl, h⟩
          .ok ⟨scope, by
            change uAliase values (aliases values [] order.val) = env
            simpa only [List.nil_append] using (aliases_collected values [] order.val).trans ha.symm⟩
        else .error "compile-time candidate disagrees with final original alias/type environment"
      else .error "compile-time function signature bounds are not stable"

/-- A successful discovery result has the exact full alias environment derived from the final
    original scalar fold, not the potentially incomplete candidate values. -/
theorem resolveCandidate_final (items : List SItemTief) (candidate : List (String × Int))
    (result : DerivedScopes items) (order : { ordered : List SItemTief // ordered.Perm items })
    (h : resolveCandidate items candidate order = .ok result) :
    result.scope.aliasConstants = result.scope.values ∧
      result.scope.declared = result.scope.aliasOrder.foldl (aliasStep result.scope.values) [] ∧
      result.scope.functionsUseValues = true := by
  unfold resolveCandidate at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · try dsimp only at h
      split at h
      · contradiction
      · split at h
        · split at h
          · rename_i ha
            have he := Except.ok.inj h
            subst result
            exact ⟨rfl, ha, rfl⟩
          · contradiction
        · contradiction

/-- Bounded discovery is not acceptance: only resolveCandidate's canonical full-fold certificate
    may return a scope. Unresolved or cyclic candidates terminate with a precise refusal. -/
def discoverScopes (items : List SItemTief) (fuel : Nat) (candidate : List (String × Int))
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    Except String (DerivedScopes items) :=
  match fuel, candidate with
  | 0, _ => .error "compile-time dependencies remain unresolved"
  | fuel + 1, candidate =>
    match resolveCandidate items candidate order with
    | .ok result => .ok result
    | .error reason =>
      let next := nextCandidates items candidate order
      if next = candidate then .error reason
      else discoverScopes items fuel next order

theorem discoverScopes_final (items : List SItemTief) (fuel : Nat)
    (candidate : List (String × Int)) (result : DerivedScopes items)
    (order : { ordered : List SItemTief // ordered.Perm items })
    (h : discoverScopes items fuel candidate order = .ok result) :
    result.scope.aliasConstants = result.scope.values ∧
      result.scope.declared = result.scope.aliasOrder.foldl (aliasStep result.scope.values) [] ∧
      result.scope.functionsUseValues = true := by
  induction fuel generalizing candidate with
  | zero => simp only [discoverScopes] at h; contradiction
  | succ fuel ih =>
    unfold discoverScopes at h
    split at h
    · rename_i found hf
      have he := Except.ok.inj h
      subst result
      exact resolveCandidate_final _ _ _ _ hf
    · try dsimp only at h
      split at h
      · contradiction
      · exact ih _ h

/-- Preserve complete conservative scopes. Newly resolvable signatures also require discovery,
    even when only an array initializer calls them and the scalar fold already succeeds. The count
    selects a path only; acceptance still requires its full canonical scope certificate. -/
def elaborateScopes (items : List SItemTief) : Except String (DerivedScopes items) := do
  let order ← orderAliases items
  let conservative : Except String (DerivedScopes items) := match deriveScopes items with
    | .ok result =>
      if (constantFunctions result.scope.types items).length = result.scope.functions.length ∧
          aliasesResolved result.scope.declared items = true then .ok result
      else discoverScopes items (items.length + 1) result.scope.values
    | .error _ => discoverScopes items (items.length + 1) (prepare items).initial
  let canonical := conservative.toOption.filter fun result =>
    items.all (checkAliasMeaning result.scope.types)
  match canonical with
  | some result => pure result
  | none =>
    discoverScopes items (items.length + 1) (prepare items).initial ⟨order.ordered, order.permutation⟩

/-- Successful frontend scope discovery includes a checked strict alias dependency rank. -/
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
      uTyp (result.scope.declared ++ [("LIMIT", (42, 42))]) [] inlineType = .ok (.int 0 42) := by
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
