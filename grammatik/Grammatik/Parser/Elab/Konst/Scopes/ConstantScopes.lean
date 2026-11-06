module
public import Grammatik.Parser.Elab.Konst.Scopes.Discovery
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantOrder
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantMeaning
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

/-- Final canonical meaning is independent of both discovery and declaration scheduling. -/
def scopeMeaning {items : List SItemTief} (derived : DerivedScopes items) : Bool :=
  items.all (checkAliasMeaning derived.scope.types) &&
    items.all (checkConstantMeaning derived.scope.types derived.scope.functions derived.scope.values)

/-- Retain the previous complete scope when possible. Otherwise use a proved scalar permutation
    with the existing canonical evaluator, alias discovery and signature stability checks. -/
def elaborateConstantScopes (items : List SItemTief) : Except String (DerivedScopes items) := do
  let order ← orderConstants items
  let discover : Unit → Except String (DerivedScopes items) := fun _ => do
    let aliases ← orderAliases items
    let result ← discoverScopes items (items.length + 1) (prepare items).initial
      ⟨aliases.ordered, aliases.permutation⟩ ⟨order.ordered, order.permutation⟩
    if scopeMeaning result then pure result
    else throw "compile-time declarations do not match their canonical final meaning"
  match elaborateScopes items with
  | .ok result =>
    if scopeMeaning result then pure result
    else match discover () with
      | .ok complete => pure complete
      | .error _ => throw "compile-time declarations do not match their canonical final meaning"
  | .error _ => discover ()

/-- A previously complete scope is retained exactly. Only an unsuccessful final
    meaning check falls through to the existing checked dependency schedule. -/
theorem elaborateConstantScopes_preserves (items : List SItemTief)
    (order : ConstantOrder items) (ordered : orderConstants items = .ok order)
    (result : DerivedScopes items) (previous : elaborateScopes items = .ok result)
    (meaning : scopeMeaning result = true) :
    elaborateConstantScopes items = .ok result := by
  simp only [elaborateConstantScopes, ordered, bind, Except.bind, previous,
    meaning, ↓reduceIte, pure, Except.pure]

/-- Every successful path checks all source dependency edges, even unused constants and arrays. -/
theorem elaborateConstantScopes_dependencies (items : List SItemTief) (result : DerivedScopes items)
    (h : elaborateConstantScopes items = .ok result) :
    ConstantAcyclic items ∧ (constantNames items).Nodup := by
  unfold elaborateConstantScopes at h
  cases ho : orderConstants items with
  | error e =>
    rw [ho] at h
    change Except.error e = Except.ok result at h
    contradiction
  | ok order => exact ⟨order.acyclic, order.unique⟩

end Gabbro.Stage0.Frontend
