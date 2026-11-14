module
public import Bruecke.Anweisung.Schleife.Retry
public import Bruecke.Anweisung.Schleife.Traverse
public import Bruecke.Anweisung.Zweig.Benannt
public import Gabbro.Body.FiniteWitness
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Non-degenerate joint simulation witness: each pass reaches `next`, the positive
    static bound is exhausted, and the explicit handler returns. Related worlds exist
    for every canonical world by `wgrel_enc`; no unit or string is evaluated. -/
theorem retry_exhaustion_sim_zeuge (u : UProg) (V : Vertrag (declOf u))
    (he : V.erg = none) (v : ErgVal (declOf u) V.erg)
    (σ : World (declOf u)) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (ρB : Gabbro.Body.Env) (fuel : Nat) :
    let state := fun σ (_ : Env (declOf u) []) (s : Gabbro.Body.State) => WGRel u σ s.world
    let result := fun σ (value : ErgVal (declOf u) V.erg) (s : Gabbro.Body.State) b =>
      WGRel u σ s.world ∧ b = ergValOf V.erg value
    OperationalRel state result (fun _ _ _ _ => False)
      (retryLauf (V := V) (l := false) (fun σ ρ => .next rfl σ ρ)
        (fun σ _ => (σ, false)) (fun σ _ => .zurueck σ v) (fuel + 1) σ .nil)
      (Gabbro.Body.step ρB (.retry (fuel + 1) (.lit (.bool false)) [.exit] [.ret none])
        ⟨encG u σ w, β⟩) ∧
    Gabbro.Body.step ρB (.retry (fuel + 1) (.lit (.bool false)) [.exit] [.ret none])
      ⟨encG u σ w, β⟩ = .returned ⟨encG u σ w, β⟩ none := by
  dsimp only
  constructor
  · apply retry_operational_sim
      (fun σ (_ : Env (declOf u) []) (s : Gabbro.Body.State) => WGRel u σ s.world)
      (fun σ value s b => WGRel u σ s.world ∧ b = ergValOf V.erg value)
      (fun _ _ _ _ => False)
      (fun σ ρ => .next rfl σ ρ) (fun σ _ => (σ, false)) (fun σ _ => .zurueck σ v)
      ρB (.lit (.bool false)) [.exit] [.ret none]
    · intro σ ρ s hs
      exact ⟨σ, false, rfl, hs, rfl⟩
    · intro σ ρ s hs
      exact hs
    · intro σ ρ s hs
      exact ⟨hs, (ergValOf_none v he).symm⟩
    · exact wgrel_enc u σ w
  · induction fuel with
    | zero =>
      exact (Gabbro.Body.retry_next ρB 0 _ _ _ _ _ rfl (by rfl)).trans
        (Gabbro.Body.retry_exceeded ρB _ _ _ _ rfl)
    | succ n ih =>
      rw [Gabbro.Body.retry_next ρB (n + 1) _ _ _ _ _ rfl (by rfl)]
      exact ih

/-- A traversal with two distinct actual indices consumes `leave` at the first one.
    The generic relation carries the same canonical world and the real Body state. -/
theorem traverse_leave_sim_zeuge (u : UProg) (V : Vertrag (declOf u))
    (σ : World (declOf u)) (w : Gabbro.Body.World) (β : Gabbro.Body.Binding)
    (ρB : Gabbro.Body.Env) (binder : String) :
    OperationalRel
      (fun σ (_ : Env (declOf u) []) s => WGRel u σ s.world)
      (fun _ (_ : ErgVal (declOf u) V.erg) _ _ => False) (fun _ _ _ _ => False)
      (traverseLauf (V := V) (l := false)
        (fun σ (ρ : Env (declOf u) [.index 2]) => .leave rfl σ ρ)
        (fun σ _ => (σ, true))
        [⟨0, by omega, by omega⟩, ⟨1, by omega, by omega⟩] σ .nil)
      (Gabbro.Body.step ρB (.forEach binder [0, 1] [.leave]) ⟨encG u σ w, β⟩) := by
  apply traverse_operational_sim
    (fun σ (_ : Env (declOf u) []) s => WGRel u σ s.world)
    (fun _ (_ : ErgVal (declOf u) V.erg) _ _ => False) (fun _ _ _ _ => False)
    (fun σ (ρ : Env (declOf u) [.index 2]) => .leave rfl σ ρ)
    (fun i => i.n) ρB binder [.leave]
  · intro i σ ρ s hs
    exact hs
  · exact wgrel_enc u σ w

/-- Semantic lifting is not source admission. The unfinished forms remain refused by
    the actual reader; a caller cannot obtain a carried duty through a fallback. -/
theorem finite_reader_refusals (u : UProg) (fn : UFn) (ns : BodyNames) (x : String) (n : Nat) :
    seqZ u 3 fn ns [.retryBeg n .tru, .ifElse, .blkEnd] = none ∧
    seqZ u 3 fn ns [.leave x, .blkEnd] = none ∧
    seqZ u 3 fn ns [.next x, .blkEnd] = none ∧
    seqZ u 3 fn ns [.matchWhyBeg x, .blkEnd] = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Gabbro.Bruecke
