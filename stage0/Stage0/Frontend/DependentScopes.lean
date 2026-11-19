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

end Gabbro.Stage0.Frontend
