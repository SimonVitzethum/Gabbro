module
public import Stage0.Frontend.DependentScopes
public import Stage0.Frontend.ConstantOrder
public import Stage0.Frontend.ConstantMeaning
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

/-- Final canonical meaning is independent of both discovery and declaration scheduling. -/
def scopeMeaning {items : List SItemTief} (derived : DerivedScopes items) : Bool :=
  items.all (checkAliasMeaning derived.scope.types) &&
    items.all (checkConstantMeaning derived.scope.types derived.scope.functions derived.scope.values)

/-- Retain the previous complete scope when possible. Otherwise use a proved scalar permutation
    with the existing canonical evaluator, alias discovery and signature stability checks. -/
def elaborateConstantScopes (items : List SItemTief) : Except String (DerivedScopes items) := do
  let order ← orderConstants items
  match elaborateScopes items with
  | .ok result =>
    if scopeMeaning result then pure result
    else throw "compile-time declarations do not match their canonical final meaning"
  | .error _ =>
    let aliases ← orderAliases items
    let result ← discoverScopes items (items.length + 1) (prepare items).initial
      ⟨aliases.ordered, aliases.permutation⟩ ⟨order.ordered, order.permutation⟩
    if scopeMeaning result then pure result
    else throw "compile-time declarations do not match their canonical final meaning"

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

/-- A forward scalar supplies another scalar's exclusive range and an alias bound. -/
theorem elaborateConstantScopes_forward_zeuge :
    let items := [SItemTief.constT "ANSWER"
        (.range (.atom "u8") (.lit 0) (.bin "+" (.variable "LIMIT") (.lit 1)) true)
        (.one (.variable "LIMIT")),
      .typeT [] "Result" [] [] (some (.atom "Bound")),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .constT "LIMIT" (.atom "u8") (.one (.bin "+" (.variable "BASE") (.lit 2))),
      .constT "BASE" (.atom "u8") (.one (.lit 40))]
    ∃ result, elaborateConstantScopes items = .ok result ∧
      result.scope.values = [("BASE", 40), ("LIMIT", 42), ("ANSWER", 42)] ∧
      result.scope.scalarOrder.Perm items ∧ ConstantAcyclic items := by
  dsimp only
  refine ⟨(elaborateConstantScopes _).toOption.get (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · exact ((elaborateConstantScopes _).toOption.get (by decide +kernel)).scope.scalarPermutation
  · exact (elaborateConstantScopes_dependencies _
      ((elaborateConstantScopes _).toOption.get (by decide +kernel))
      (Gabbro.Grammatik.except_ok_get _)).1

end Gabbro.Stage0.Frontend
