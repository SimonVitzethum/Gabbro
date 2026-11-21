module

public import Grammatik.Parser.Elab.UebersetzeAllg

@[expose] public section

namespace Gabbro.Stage0.Frontend

open Gabbro.Grammatik.Parser.Uebersetze

/-- The hosted emitter has a lowering for startup threads. A dynamic
    `start` still needs its own verified clone and join continuation. -/
structure HostedStartShape (u : UProg) : Prop where
  noDynamicRoots : u.gestartet = []
  noErasedStart : ∀ fn ∈ u.fns, UStmt.startS ∉ fn.body

def isDynamicStart : UStmt → Bool
  | .startS => true
  | _ => false

/-- Check the resolved flat statement lists as well as the names collected
    at the surface. A nested statement cannot pass as an empty root list. -/
def checkHostedStarts (u : UProg) : Except String (PLift (HostedStartShape u)) :=
  if roots : u.gestartet = [] then
    if dynamic : u.fns.any (fun fn => fn.body.any isDynamicStart) = true then
      .error "stage0: dynamic start and join have no verified hosted lowering"
    else
      .ok ⟨⟨roots, fun fn member marker => dynamic (List.any_eq_true.mpr
        ⟨fn, member, List.any_eq_true.mpr ⟨.startS, marker, rfl⟩⟩)⟩⟩
  else .error "stage0: dynamic start and join have no verified hosted lowering"

/-- Acceptance is exactly the absence of unsupported dynamic roots and
    statement markers. The executable guard introduces no extra restriction. -/
theorem checkHostedStarts_iff (u : UProg) :
    (checkHostedStarts u).toOption.isSome = true ↔ HostedStartShape u := by
  constructor
  · intro accepted
    cases read : checkHostedStarts u with
    | error error => simp only [read, Except.toOption, Option.isSome_none, Bool.false_eq_true] at accepted
    | ok checked => exact checked.down
  · intro shape
    have clean : u.fns.any (fun fn => fn.body.any isDynamicStart) = false := by
      cases found : u.fns.any (fun fn => fn.body.any isDynamicStart) with
      | false => rfl
      | true =>
        obtain ⟨fn, member, body⟩ := List.any_eq_true.mp found
        obtain ⟨statement, occurs, start⟩ := List.any_eq_true.mp body
        have marker : statement = .startS := by
          cases statement <;> simp only [isDynamicStart, Bool.false_eq_true] at start
          rfl
        exact (shape.noErasedStart fn member (marker ▸ occurs)).elim
    simp only [checkHostedStarts, dite_eq_left shape.noDynamicRoots, clean, Bool.false_eq_true,
      Bool.not_true, dite_false, Except.toOption, Option.isSome_some]

end Gabbro.Stage0.Frontend
