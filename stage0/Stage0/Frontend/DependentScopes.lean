import Stage0.Frontend.Environments

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Discovery may use partial legacy collector output, but it is never an authoritative scope. -/
def nextCandidates (items : List SItemTief) (values : List (String × Int)) : List (String × Int) :=
  let expanded := aliases values [] items
  let env := uAliase values expanded
  let fns := constantFunctions env expanded
  let normalized := constants env fns [] expanded
  uConstsRech (uKonstFns normalized) normalized []

/-- A new candidate cannot hide unresolved integer alias declarations, including unused cycles. -/
def aliasesResolved (env : List (String × (Int × Int))) (items : List SItemTief) : Bool :=
  items.all fun
    | .typeT _ name [] _ (some (.atom _)) | .typeT _ name [] _ (some (.range _ _ _ _)) =>
      (env.find? (fun entry => strEq entry.1 name)).isSome
    | _ => true

/-- Validate a discovery candidate by re-evaluating every original scalar at its exact original
    type and then comparing the complete alias fold against those final, ordered values. -/
def resolveCandidate (items : List SItemTief) (candidate : List (String × Int)) :
    Except String (DerivedScopes items) :=
  let expanded := aliases candidate [] items
  let env := uAliase candidate expanded
  let fns := constantFunctions env items
  if !aliasesResolved env items then .error "compile-time aliases contain unresolved dependencies or cycles"
  else match h : typedConstants env fns items [] with
  | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
  | some values =>
    if ha : env = items.foldl (aliasStep values) [] then
      let scope : Scopes items := ⟨values, env, fns, values, Or.inr rfl, ha, rfl, h⟩
      .ok ⟨scope, by
        change uAliase values (aliases values [] items) = env
        simpa only [List.nil_append] using (aliases_collected values [] items).trans ha.symm⟩
    else .error "compile-time candidate disagrees with final original alias/type environment"

/-- A successful discovery result has the exact full alias environment derived from the final
    original scalar fold, not the potentially incomplete candidate values. -/
theorem resolveCandidate_final (items : List SItemTief) (candidate : List (String × Int))
    (result : DerivedScopes items) (h : resolveCandidate items candidate = .ok result) :
    result.scope.aliasConstants = result.scope.values ∧
      result.scope.declared = items.foldl (aliasStep result.scope.values) [] := by
  unfold resolveCandidate at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i values hv
      split at h
      · rename_i ha
        have he := Except.ok.inj h
        subst result
        exact ⟨rfl, ha⟩
      · contradiction

/-- Bounded discovery is not acceptance: only resolveCandidate's canonical full-fold certificate
    may return a scope. Unresolved or cyclic candidates terminate with a precise refusal. -/
def discoverScopes (items : List SItemTief) : Nat → List (String × Int) → Except String (DerivedScopes items)
  | 0, _ => .error "compile-time dependencies remain unresolved"
  | fuel + 1, candidate =>
    match resolveCandidate items candidate with
    | .ok result => .ok result
    | .error reason =>
      let next := nextCandidates items candidate
      if next = candidate then .error reason
      else discoverScopes items fuel next

theorem discoverScopes_final (items : List SItemTief) (fuel : Nat)
    (candidate : List (String × Int)) (result : DerivedScopes items)
    (h : discoverScopes items fuel candidate = .ok result) :
    result.scope.aliasConstants = result.scope.values ∧
      result.scope.declared = items.foldl (aliasStep result.scope.values) [] := by
  induction fuel generalizing candidate with
  | zero => simp only [discoverScopes] at h; contradiction
  | succ fuel ih =>
    unfold discoverScopes at h
    split at h
    · rename_i found hf
      have he := Except.ok.inj h
      subst result
      exact resolveCandidate_final _ _ _ hf
    · dsimp only at h
      split at h
      · contradiction
      · exact ih _ h

/-- Preserve the already certified conservative path exactly; discover additional scopes only
    after that path refuses, and validate them against the full original canonical declaration fold. -/
def elaborateScopes (items : List SItemTief) : Except String (DerivedScopes items) :=
  match deriveScopes items with
  | .ok result => .ok result
  | .error _ => discoverScopes items (items.length + 1) (prepare items).initial

theorem elaborateScopes_preserves (items : List SItemTief) (result : DerivedScopes items)
    (h : deriveScopes items = .ok result) : elaborateScopes items = .ok result := by
  simp only [elaborateScopes, h]

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

end Gabbro.Stage0.Frontend
