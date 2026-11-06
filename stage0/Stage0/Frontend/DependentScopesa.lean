module
public import Grammatik.Parser.Elab.Konst.Scopes.Discovery
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

theorem discoverScopes_final (items : List SItemTief) (fuel : Nat)
    (candidate : List (String × Int)) (result : DerivedScopes items)
    (order scalars : { ordered : List SItemTief // ordered.Perm items })
    (h : discoverScopes items fuel candidate order scalars = .ok result) :
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
      exact resolveCandidate_final _ _ _ _ _ hf
    · try dsimp only at h
      split at h
      · contradiction
      · exact ih _ h

end Gabbro.Stage0.Frontend
