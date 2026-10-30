/- Runtime loop edges consume the actual block simulation and its world-aware frame. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- A lowered body reaches its backedge with the reserved runtime budget intact.
The equality follows from the body simulation's frame, including reachable calls
and world writes; no separate preservation hypothesis is admitted. -/
theorem Reach.counter_backedge {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {fp pc : W} {lo K Ks counter : Nat} {pr : List Nat}
    {t : T} {m : Mem} {σ : World D} {ρ : Env D Γ} {reserved : Nat}
    {jump b c : BitVec 32} {value : W}
    (body : Reach L fp lo K pr t m pc σ ρ reserved)
    (layout : WIn L fp Ks K) (below : counter < lo) (bound : lo ≤ K)
    (initial : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value)
    (edge : InsAt m pc 18 jump b c) (far : CodeFar pc 1 fp K) :
    ∃ m', Star t m ⟨pc + sx jump, fp⟩ m' ∧
      AgreeW L fp lo K m m' ∧ EnvAt L m' fp ρ reserved ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value := by
  obtain ⟨m', run, frame, env, world, keeps⟩ := body
  have code : CodeAt m pc [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst k
    simpa [II.f] using edge
  have code' := codeAt_agreeWIn layout frame code far
  have edge' := code' 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at edge'
  have hj := Star.one (run_step (t := ⟨pc, fp⟩) edge' (by decide)
    (run_jmp (t := ⟨pc, fp⟩) edge'))
  refine ⟨m', run.trans ?_, frame, env, world, keeps, ?_⟩
  · simpa [II.f] using hj
  · rw [counter_preserved layout frame below bound]
    exact initial

/-- A zero budget executes the real conditional branch into the progress stop,
before an invariant or body can execute. -/
theorem counter_budget_stop {t : T} {m : Mem} {d jump c : BitVec 32}
    (instruction : InsAt m t.pc 19 d jump c)
    (zero : m.rd64 (slot t.fp (sx d)) = some 0)
    (stop : Stops {t with pc := t.pc + sx jump} m 111) :
    Stops t m 111 :=
  Stops.prefix (Star.one (counter_zero instruction zero)) stop

end Gabbro.Stage0.Senke
