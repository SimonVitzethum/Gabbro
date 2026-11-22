module

public import Grammatik.Nebenlaeufigkeit.Async.Syntax
import Lean.Elab.Tactic.Omega

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

private theorem asyncReady_exists {functions todo : List AsyncFn} {defined : List String}
    (wellFounded : WellFounded (AsyncDependency functions))
    (remaining : ∀ function ∈ todo, function ∈ functions)
    (closed : ∀ function ∈ todo, ∀ child ∈ function.callees,
      child ∈ defined ∨ ∃ declaration ∈ todo, declaration.name = child)
    (nonempty : todo ≠ []) :
    ∃ function ∈ todo, function.callees.all defined.contains = true := by
  have visit (name : String) (accessible : Acc (AsyncDependency functions) name) :
      (∃ function ∈ todo, function.name = name) →
      ∃ function ∈ todo, function.callees.all defined.contains = true := by
    induction accessible with
    | intro name _ ih =>
      rintro ⟨function, member, rfl⟩
      by_cases ready : function.callees.all defined.contains = true
      · exact ⟨function, member, ready⟩
      · classical
        rw [List.all_eq_true] at ready
        obtain ⟨child, missing⟩ := Classical.not_forall.mp ready
        have used : child ∈ function.callees :=
          Classical.byContradiction (fun absent => missing (fun member => False.elim (absent member)))
        have undefined : child ∉ defined := fun present =>
          missing (fun _ => List.contains_iff_mem.mpr present)
        exact ih child ⟨function, remaining function member, rfl, used⟩
          ((closed function member child used).resolve_left undefined)
  obtain ⟨function, tail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  exact visit function.name (wellFounded.apply function.name) ⟨function, List.mem_cons_self, rfl⟩

/-- A finite closed acyclic graph always has an eligible batch. One
    unit of fuel per declaration suffices for the executable scheduler. -/
public theorem arrangeAsync_complete {functions : List AsyncFn}
    (wellFounded : WellFounded (AsyncDependency functions)) :
    ∀ {fuel : Nat} {defined : List String} {todo : List AsyncFn},
      todo.length ≤ fuel → (∀ function ∈ todo, function ∈ functions) →
      (∀ function ∈ todo, ∀ child ∈ function.callees,
        child ∈ defined ∨ ∃ declaration ∈ todo, declaration.name = child) →
      (arrangeAsync fuel defined todo).isOk = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro defined todo enough _ _
    have empty := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    subst todo
    rfl
  | succ fuel ih =>
    intro defined todo enough remaining closed
    cases todo with
    | nil => rfl
    | cons head tail =>
      let todo := head :: tail
      let ready (function : AsyncFn) := function.callees.all defined.contains
      let available := todo.filter ready
      let deferred := todo.filter fun function => !ready function
      obtain ⟨function, member, eligible⟩ := asyncReady_exists wellFounded remaining closed (List.cons_ne_nil _ _)
      have chosen : function ∈ available := List.mem_filter.mpr ⟨member, eligible⟩
      have notEmpty : available.isEmpty = false :=
        List.isEmpty_eq_false_iff_exists_mem.mpr ⟨function, chosen⟩
      have smaller : deferred.length ≤ fuel := by
        have positive : 0 < available.length := List.length_pos_of_mem chosen
        have same := (List.filter_append_perm ready todo).length_eq
        simp only [List.length_append] at same
        change available.length + deferred.length = todo.length at same
        change todo.length ≤ fuel + 1 at enough
        omega
      have nextRemaining : ∀ function ∈ deferred, function ∈ functions :=
        fun function member => remaining function (List.mem_filter.mp member).1
      have nextClosed : ∀ function ∈ deferred, ∀ child ∈ function.callees,
          child ∈ defined ++ available.map AsyncFn.name ∨
            ∃ declaration ∈ deferred, declaration.name = child := by
        intro function member child used
        obtain known | ⟨declaration, present, named⟩ := closed function (List.mem_filter.mp member).1 child used
        · exact .inl (List.mem_append_left _ known)
        · cases accepted : ready declaration with
          | false => exact .inr ⟨declaration,
              List.mem_filter.mpr ⟨present, by rw [accepted]; rfl⟩, named⟩
          | true => exact .inl (List.mem_append_right _ (List.mem_map.mpr
              ⟨declaration, List.mem_filter.mpr ⟨present, accepted⟩, named⟩))
      have continues := ih smaller nextRemaining nextClosed
      change (arrangeAsync fuel (defined ++ available.map AsyncFn.name) deferred).isOk = true at continues
      cases result : arrangeAsync fuel (defined ++ available.map AsyncFn.name) deferred with
      | error reason => simp only [result, Except.isOk, Except.toBool, Bool.false_eq_true] at continues
      | ok ordered =>
        change (arrangeAsync (fuel + 1) defined (head :: tail)).isOk = true
        rw [arrangeAsync]
        change (do
          if available.isEmpty then throw "async: unknown or recursive future dependency"
          let rest ← arrangeAsync fuel (defined ++ available.map AsyncFn.name) deferred
          return ⟨available ++ rest.val, _⟩ :
            Except String { ordered : List AsyncFn // ordered.Perm (head :: tail) }).isOk = true
        simp only [notEmpty, Bool.false_eq_true, ite_false, bind, Except.bind, result,
          pure, Except.pure, Except.isOk, Except.toBool]

end Gabbro.Grammatik.Async
