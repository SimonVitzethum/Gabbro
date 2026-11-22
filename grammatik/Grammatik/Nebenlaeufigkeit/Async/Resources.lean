module

public import Grammatik.Nebenlaeufigkeit.Async.DispatchG
public import Grammatik.Kern.Syntax.Satz.T1Frame

namespace Gabbro.Grammatik.Async

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- These are canonical mark/stage resources, not unchecked natural-number
    receipts. One owner identity may occur only once, including at different
    stages. Copying a record value does not copy these resources. -/
@[expose] public def savedResources (owned : List (D.Marke × Nat)) : List (Res D) :=
  owned.map (Res.vonMarke D)

public theorem savedResources_no_locks (owned : List (D.Marke × Nat)) (lock : D.Lock) :
    Res.held lock ∉ savedResources owned := by
  intro member
  obtain ⟨entry, _, impossible⟩ := List.mem_map.mp member
  cases impossible

public theorem savedResources_unique (owned : List (D.Marke × Nat))
    (unique : (owned.map Prod.fst).Nodup) : (savedResources owned).Nodup := by
  revert unique
  induction owned with
  | nil => intro _; exact List.nodup_nil
  | cons entry rest ih =>
    intro unique
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [savedResources, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih unique.2⟩
    intro member
    obtain ⟨other, inRest, same⟩ := List.mem_map.mp member
    have sameOwner : other.1 = entry.1 := by
      cases entry
      cases other
      cases same
      rfl
    exact unique.1 (List.mem_map.mpr ⟨other, inRest, sameOwner⟩)

/-- An annotation containing no lock names is insufficient. With floor none,
    HeldB is exact; hence even a caller cannot lend an extra held lock to a
    suspended poll. A nonempty floor must NOT discharge this rule. -/
public theorem suspension_no_locks (resources : List (Res D)) (held : List D.Lock)
    (noStaticLocks : ∀ lock, Res.held lock ∉ resources)
    (dynamic : HeldB none resources held) : held = [] := by
  have exactHeld := heldB_none_iff.mp dynamic
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro lock member
  exact noStaticLocks lock ((exactHeld lock).mpr member)

public theorem savedResources_suspend (owned : List (D.Marke × Nat)) (world : World D)
    (dynamic : HeldB none (savedResources owned) world.haelt) : world.haelt = [] :=
  suspension_no_locks _ _ (savedResources_no_locks owned) dynamic

/-- If a proved ordinary segment restores its entry lock set (Brav), every
    Pending boundary after that segment is lock-free as well. -/
public theorem suspension_after_segment (resources : List (Res D)) (before after : World D)
    (noStaticLocks : ∀ lock, Res.held lock ∉ resources)
    (dynamic : HeldB none resources before.haelt) (segment : Brav before after) :
    after.haelt = [] :=
  segment.1.trans (suspension_no_locks resources before.haelt noStaticLocks dynamic)

/-- No world read or permission is hidden in clearing the generated record. -/
public theorem cancelledExpr_places (types : TypeResolution) (f : AsyncFn) :
    (cancelledExpr types f (D := D) (Γ := Γ) (Λ := Λ)).orte = [] := rfl

public theorem cancelledExpr_evaluates (types : TypeResolution) (f : AsyncFn)
    (entry world : World D) (environment : Env D Γ) :
    eval entry (cancelledExpr types f (Λ := Λ)) world environment =
      cancelledValue types f D := rfl

/-- Only successful release reaches the clear, under the EMPTY resource
    index. This does not assert that an arbitrary destructor succeeds: its
    ordinary G contract and the recursive child drop obligations remain due. -/
public theorem cancelEpilogue_success (types : TypeResolution) (f : AsyncFn)
    (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ (stateType types f)) (release : Stmt D V l Γ Λ [])
    (before after : World D) (environment environment' : Env D Γ)
    (released : execStmt O passes calls release before environment = .ok after environment') :
    execBlock O passes calls (cancelEpilogue types f state release) before environment =
      .ok after (environment'.set state (cancelledValue types f D)) := by
  simp only [cancelEpilogue, execBlock, released, execStmt, cancelledExpr_places,
    cancelledExpr_evaluates, World.lese, World.merke, List.map_nil, List.nil_append]

/-- A failure in drop is propagated, rather than silently clearing a future
    and claiming that its resources were discharged. -/
public theorem cancelEpilogue_failure (types : TypeResolution) (f : AsyncFn)
    (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ (stateType types f)) (release : Stmt D V l Γ Λ [])
    (world : World D) (environment : Env D Γ) (failure : Logik D)
    (failed : execStmt O passes calls release world environment = .logik failure) :
    execBlock O passes calls (cancelEpilogue types f state release) world environment =
      .logik failure := by
  simp only [cancelEpilogue, execBlock, failed]

end Gabbro.Grammatik.Async
