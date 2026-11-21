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

private def isDynamicStart : UStmt → Bool
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

end Gabbro.Stage0.Frontend
