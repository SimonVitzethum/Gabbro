module
public import Bruecke.Kodierung
public import Gabbro.Body.Finite
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik

/-- A complete operational correspondence, including both loop-control outcomes.
    `state` relates the live local context; `result` and `reason` relate the two result
    channels. Logic and hardware failures correspond to a stuck Body, never success.
    No clause asserts a user duty or assumes that a particular body succeeds. -/
def OperationalRel {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (state : World D → Env D Γ → Gabbro.Body.State → Prop)
    (result : World D → ErgVal D V.erg → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (reason : World D → Fin V.gruende → Gabbro.Body.State → Option Gabbro.Body.Value → Prop) :
    Ausgang V l Γ → Gabbro.Body.Outcome → Prop
  | .ok σ ρ, .running s => state σ ρ s
  | .next _ σ ρ, .exited s => state σ ρ s
  | .leave _ σ ρ, .left s => state σ ρ s
  | .zurueck σ v, .returned s b => result σ v s b
  | .why σ r, .returned s b => reason σ r s b
  | .logik _, .stuck | .hardware _, .stuck => True
  | _, _ => False

/-- The canonical `leave` and `next` leaves keep exactly the current state. -/
theorem loop_control_sim {D : Deklaration} {V : Vertrag D} {Γ : Ctx}
    (state : World D → Env D Γ → Gabbro.Body.State → Prop)
    (result : World D → ErgVal D V.erg → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (reason : World D → Fin V.gruende → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (ρB : Gabbro.Body.Env) (σ : World D) (ρ : Env D Γ) (s : Gabbro.Body.State)
    (h : state σ ρ s) :
    OperationalRel (V := V) (l := true) state result reason
      (.leave rfl σ ρ) (Gabbro.Body.step ρB .leave s) ∧
      OperationalRel (V := V) (l := true) state result reason
        (.next rfl σ ρ) (Gabbro.Body.step ρB .exit s) :=
  ⟨h, h⟩

end Gabbro.Bruecke
