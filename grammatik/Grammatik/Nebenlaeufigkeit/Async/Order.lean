module

public import Grammatik.Nebenlaeufigkeit.Async.Syntax

namespace Gabbro.Grammatik.Async

/-- Each leaf is a nominal child, including leaves of nested joins.
    Argument expressions do not introduce additional future edges. -/
@[expose] public def FutureExpr.callees : FutureExpr → List String
  | .call name _ => [name]
  | .join left right => left.callees ++ right.callees

@[expose] public def AsyncFn.callees (function : AsyncFn) : List String :=
  function.body.flatMap fun
    | .bind .. => []
    | .await _ future _ => future.callees

/-- An ordered batch resolves each child before its parent's generated
    record can refer to it. Unknown names, duplicate declarations, and
    direct or indirect recursive futures all fail the same decision. -/
@[expose] public def asyncOrderB (functions : List AsyncFn) : Bool :=
  let names := functions.map AsyncFn.name
  decide names.Nodup && functions.all fun function =>
    function.callees.all fun child =>
      names.contains child && decide (names.idxOf child < names.idxOf function.name)

@[expose] public def AsyncDependency (functions : List AsyncFn) (child caller : String) : Prop :=
  ∃ function ∈ functions, function.name = caller ∧ child ∈ function.callees

/-- The single batch decision supplies a closed, well-founded child
    relation for construction, polling and destruction of the same
    declaration graph. -/
public theorem asyncOrder_sound {functions : List AsyncFn} (ordered : asyncOrderB functions = true) :
    let names := functions.map AsyncFn.name
    names.Nodup ∧
    (∀ child caller, AsyncDependency functions child caller →
      child ∈ names ∧ names.idxOf child < names.idxOf caller) ∧
    WellFounded (AsyncDependency functions) := by
  intro names
  obtain ⟨distinct, children⟩ := Bool.and_eq_true_iff.mp ordered
  have edge (child caller : String) (dependency : AsyncDependency functions child caller) :
      child ∈ names ∧ names.idxOf child < names.idxOf caller := by
    obtain ⟨function, listed, rfl, called⟩ := dependency
    have valid := List.all_eq_true.mp (List.all_eq_true.mp children function listed) child called
    exact ⟨List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp valid).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2⟩
  exact ⟨of_decide_eq_true distinct, edge,
    Subrelation.wf (fun h => (edge _ _ h).2) (measure names.idxOf).wf⟩

/-- Resolve ready declarations in batches and retain source order within
    each batch. Permutation is proved in the recursion independently of
    the check on the final result. -/
@[expose] public def arrangeAsync : Nat → List String → (todo : List AsyncFn) →
    Except String { ordered : List AsyncFn // ordered.Perm todo }
  | _, _, [] => .ok ⟨[], .refl _⟩
  | 0, _, _ :: _ => .error "async: exhausted declaration ordering"
  | fuel + 1, defined, head :: tail => do
    let todo := head :: tail
    let ready := fun function : AsyncFn => function.callees.all defined.contains
    let available := todo.filter ready
    if available.isEmpty then throw "async: unknown or recursive future dependency"
    let ordered ← arrangeAsync fuel (defined ++ available.map AsyncFn.name)
      (todo.filter fun function => !ready function)
    return ⟨available ++ ordered.val,
      (ordered.property.append_left available).trans (List.filter_append_perm ready todo)⟩

public structure OrderedAsync (functions : List AsyncFn) where
  declarations : List AsyncFn
  permutation : declarations.Perm functions
  checked : asyncOrderB declarations = true

/-- Forward references are resolved before layout. Only the checked
    order is passed on, so the implementation of the search is outside
    the proof of closedness and acyclicity. -/
@[expose] public def orderAsync (functions : List AsyncFn) :
    Except String (OrderedAsync functions) := do
  let ordered ← arrangeAsync functions.length [] functions
  if valid : asyncOrderB ordered.val = true then
    return ⟨ordered.val, ordered.property, valid⟩
  else throw "async: duplicate declaration or inconsistent dependency order"

public theorem OrderedAsync.wellFounded {functions : List AsyncFn} (order : OrderedAsync functions) :
    WellFounded (AsyncDependency functions) := by
  apply Subrelation.wf _ (asyncOrder_sound order.checked).2.2
  rintro child caller ⟨function, member, named, depends⟩
  exact ⟨function, order.permutation.mem_iff.mpr member, named, depends⟩

end Gabbro.Grammatik.Async
