module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Waiting

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  {Value Child : Type}

/-- The concrete G block obligation for one selected phase. Entry and exit
    representations must describe actual frame slots, child storage and
    inventory; they are explicit parameters, not hidden in a callback.
    This interface alone supplies no source elaboration or Model instance. -/
public structure SegmentDuty (model : Model Value Child (World D)) (f : AsyncFn)
    (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (body : Block D V l Γ Λ Λ)
    (entry : State Value Child → World D → Env D Γ → Prop)
    (exit : Event Value → State Value Child → World D → Env D Γ → Prop) : Prop where
  execute : ∀ source before environment event target after cost,
    entry source before environment →
    machineStep model (asyncExpand model f) source before = (event, target, after, cost) →
    ∃ environment', execBlock O passes calls body before environment = .ok after environment' ∧
      exit event target after environment' ∧ HeldB none Λ after.haelt
  costBound : ∀ source before environment event target after cost,
    entry source before environment →
    machineStep model (asyncExpand model f) source before = (event, target, after, cost) →
    cost ≤ kostenBlock 0 prices passes body
  callsAllowed : rufeB direct indirect forever body = true

end Gabbro.Grammatik.Async.Segment
