module
public import Grammatik.Parser.Elab.Konst.Scopes.Environments
public import Grammatik.Parser.Elab.Konst.Scopes.AliasOrderFast
public import Grammatik.Parser.Elab.Konst.Scopes.AliasMeaning
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

-- One canonical source-scope implementation, shared with the Stage0 compiler.
namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Discovery uses candidate scalar bounds in const-function signatures. Its partial collector
    output remains untrusted until resolveCandidate rechecks the full original source fold.
    Reuse canonical typed evaluation directly: custom-range negatives need no source materialization.
    Failed declarations are skipped only here; final validation checks every original scalar. -/
def nextCandidates (items : List SItemTief) (values : List (String × Int))
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩)
    (scalars : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    List (String × Int) :=
  let expanded := aliases values [] order.val
  let env := uAliase values expanded
  let fns := constantFunctions (env ++ values.map (fun c => (c.1, (c.2, c.2)))) expanded
  scalars.val.foldl (fun collected item => (typedItem env fns collected item).getD collected) []

/-- A new candidate cannot hide unresolved integer alias declarations, including unused cycles. -/
def aliasesResolved (env : List (String × (Int × Int))) (items : List SItemTief) : Bool :=
  items.all fun
    | .typeT _ name [] _ (some (.atom _)) | .typeT _ name [] _ (some (.range _ _ _ _)) =>
      (env.find? (fun entry => strEq entry.1 name)).isSome
    | _ => true

/-- Validate a discovery candidate by re-evaluating every original scalar at its exact original
    type and then comparing the complete alias fold against those final, ordered values. -/
def resolveCandidate (items : List SItemTief) (candidate : List (String × Int))
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩)
    (scalars : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    Except String (DerivedScopes items) :=
  let expanded := aliases candidate [] order.val
  let env := uAliase candidate expanded
  let tentativeFns := constantFunctions (env ++ candidate.map (fun c => (c.1, (c.2, c.2)))) items
  if !aliasesResolved env items then .error "compile-time aliases contain unresolved dependencies or cycles"
  else match typedConstants env tentativeFns scalars.val [] with
  | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
  | some preliminary =>
    let fns := constantFunctions (env ++ preliminary.map (fun c => (c.1, (c.2, c.2)))) items
    match h : typedConstants env fns scalars.val [] with
    | none => .error "compile-time scalar cannot be evaluated at its canonical declared range"
    | some values =>
      if hs : values = preliminary then
        if ha : env = order.val.foldl (aliasStep values) [] then
          let scope : Scopes items := ⟨values, env, fns, values, Or.inr rfl, true, order.val, order.property, ha,
            by simp only [↓reduceIte, hs]; rfl, scalars.val, scalars.property, h⟩
          .ok ⟨scope, by
            change uAliase values (aliases values [] order.val) = env
            simpa only [List.nil_append] using (aliases_collected values [] order.val).trans ha.symm⟩
        else .error "compile-time candidate disagrees with final original alias/type environment"
      else .error "compile-time function signature bounds are not stable"

/-- A successful discovery result has the exact full alias environment derived from the final
    original scalar fold, not the potentially incomplete candidate values. -/
theorem resolveCandidate_final (items : List SItemTief) (candidate : List (String × Int))
    (result : DerivedScopes items) (order scalars : { ordered : List SItemTief // ordered.Perm items })
    (h : resolveCandidate items candidate order scalars = .ok result) :
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
    (order : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩)
    (scalars : { ordered : List SItemTief // ordered.Perm items } := ⟨items, .refl _⟩) :
    Except String (DerivedScopes items) :=
  match fuel, candidate with
  | 0, _ => .error "compile-time dependencies remain unresolved"
  | fuel + 1, candidate =>
    match resolveCandidate items candidate order scalars with
    | .ok result => .ok result
    | .error reason =>
      let next := nextCandidates items candidate order scalars
      if next = candidate then .error reason
      else discoverScopes items fuel next order scalars

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

/- Successful frontend scope discovery includes a checked strict alias dependency rank. -/

end Gabbro.Stage0.Frontend
