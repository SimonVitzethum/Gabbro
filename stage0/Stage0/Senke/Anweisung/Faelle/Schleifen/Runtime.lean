/- Runtime loop edges consume the actual block simulation and its world-aware frame. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- Initialize from the semantic fuel argument itself. The representability
check rejects budgets outside the instruction's signed immediate range. -/
theorem counter_initialize {m : Mem} {pc fp : W} {K counter budget : Nat}
    (code : CodeAt m pc (foreverCounterInit counter (budget : Int)))
    (frame : FrameOK m fp K) (inside : counter < K)
    (small : K < 2 ^ 31) (fuel : budget < 2 ^ 31) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget) := by
  have literal : lit32 (budget : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have run := const_step code frame inside small literal
  refine ⟨_, run, ?_⟩
  rw [BitVec.ofInt_natCast]
  exact rd64_write_same (frame.rd counter inside)

/-- A lowered body reaches its backedge with the reserved runtime budget intact.
The equality follows from the body simulation's frame, including reachable calls
and world writes; no separate preservation hypothesis is admitted. -/
theorem Reach.counter_backedge {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {fp pc : W} {lo K Ks counter : Nat} {pr : List Nat}
    {t : T} {m : Mem} {σ : World D} {ρ : Env D Γ} {reserved : Nat}
    {jump b c : BitVec 32} {value : W}
    (body : Reach L fp lo K pr t m pc σ ρ reserved)
    (layout : WIn L fp Ks K) (hprotected : counter < lo ∨ counter ∈ pr) (bound : lo ≤ K)
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
  · cases hprotected with
    | inl below => rw [counter_preserved layout frame below bound]; exact initial
    | inr member => rw [keeps counter member]; exact initial

/-- A zero budget executes the real conditional branch into the progress stop,
before an invariant or body can execute. -/
theorem counter_budget_stop {t : T} {m : Mem} {d jump c : BitVec 32}
    (instruction : InsAt m t.pc 19 d jump c)
    (zero : m.rd64 (slot t.fp (sx d)) = some 0)
    (stop : Stops {t with pc := t.pc + sx jump} m 111) :
    Stops t m 111 :=
  Stops.prefix (Star.one (counter_zero instruction zero)) stop

/-- Test, decrement, actual simulated body and emitted backedge compose into
one runtime iteration. The body result is the ordinary lowering simulation,
whose frame supplies counter retention even through world writes and calls. -/
theorem counter_iteration {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {fp pc back : W} {lo K Ks counter : Nat} {pr : List Nat}
    {m m1 : Mem} {σ : World D} {ρ : Env D Γ} {reserved : Nat}
    {d stop one jump b c : BitVec 32} {value : W}
    (test : InsAt m pc 19 d stop 0)
    (positive : m.rd64 (slot fp (sx d)) = some value) (nonzero : value ≠ 0)
    (decrement : InsAt m (pc + 16) 4 d d one)
    (unit : m.rd64 (slot fp (sx one)) = some 1)
    (write : m.wr64 (slot fp (sx d)) (value - 1) = some m1)
    (body : Reach L fp lo K pr ⟨pc + 16 + 16, fp⟩ m1 back σ ρ reserved)
    (layout : WIn L fp Ks K) (hprotected : counter < lo ∨ counter ∈ pr)
    (bound : lo ≤ K)
    (location : sx d = BitVec.ofNat 64 counter)
    (edge : InsAt m1 back 18 jump b c) (far : CodeFar back 1 fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨back + sx jump, fp⟩ m' ∧
      EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (value - 1) := by
  have first := Star.one (counter_positive (t := ⟨pc, fp⟩) test positive nonzero)
  have second := Star.one (counter_decrement (t := ⟨pc + 16, fp⟩)
    decrement positive unit write)
  have stored := Runner.Mem.rd64_wr64 write (rd64_some_all positive)
  rw [location] at stored
  obtain ⟨m', rest, _, env, world, _, kept⟩ := Reach.counter_backedge body
    layout hprotected bound stored edge far
  exact ⟨m', first.trans (second.trans rest), env, world, kept⟩

/-- The zero arm reaches the actual emitted exit request with progress code 111.
This does not postulate that a desired stop occurs. -/
theorem counter_budget_stop_code {m : Mem} {pc fp : W} {d jump c : BitVec 32}
    {K scratch : Nat}
    (instruction : InsAt m pc 19 d jump c)
    (zero : m.rd64 (slot fp (sx d)) = some 0)
    (code : CodeAt m (pc + sx jump) (stopC 111 scratch))
    (far : CodeFar (pc + sx jump) 3 fp K) (frame : FrameOK m fp K)
    (room : scratch + 8 ≤ K) (small : K < 2 ^ 31) :
    Stops ⟨pc, fp⟩ m 111 :=
  counter_budget_stop instruction zero (stop_ok code far frame room small (by decide))

/-- Canonical fuel induction at a fixed runtime loop header. `entry` describes
    the concrete counter, code, frame and surrounding program at that header.
    The positive arm simulates just one invariant/body pass (not the loop).
    Continuing passes carry the smaller-fuel entry in their actual runtime result.
    This composition does not by itself discharge those lowering obligations. -/
theorem forever_runtime {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {l : Bool} {reserved : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp pc exit outerLeave outerNext : W} {lo K : Nat} {pr : List Nat}
    (a : D.Annahme)
    (body : World D → Env D Γ → Ausgang (vertragVon D f) true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (entry : Nat → Mem → World D → Env D Γ → Prop)
    (lower : FB ≤ lo)
    (zero : ∀ m σ ρ, entry 0 m σ ρ → Stops ⟨pc, fp⟩ m (hwCode (.fortschritt a)))
    (invalid : ∀ n m σ ρ, entry (n + 1) m σ ρ → (inv σ ρ).2 = false →
      Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife))
    (pass : ∀ n m σ ρ, entry (n + 1) m σ ρ → (inv σ ρ).2 ≠ false →
      match body (inv σ ρ).1 ρ with
      | .ok σ' ρ' | .next _ σ' ρ' =>
        ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
          EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧ Keeps fp pr m m' ∧ entry n m' σ' ρ'
      | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m pc exit pc o reserved) :
    ∀ n m σ ρ, entry n m σ ρ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (foreverLauf (l := l) a body inv n σ ρ) reserved := by
  intro n
  induction n with
  | zero =>
    intro m σ ρ he
    exact zero m σ ρ he
  | succ n ih =>
    intro m σ ρ he
    simp only [foreverLauf]
    by_cases hv : (inv σ ρ).2 = false
    · rw [ite_eq_left hv]
      exact invalid n m σ ρ he hv
    · rw [ite_eq_right hv]
      have hb := pass n m σ ρ he hv
      have again : ∀ σ' ρ',
          (∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
            EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧ Keeps fp pr m m' ∧ entry n m' σ' ρ') →
          Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
            (foreverLauf (l := l) a body inv n σ' ρ') reserved := by
        intro σ' ρ' hr
        obtain ⟨m', run, frame, _, _, keeps, he'⟩ := hr
        exact Sim.prefix lower run frame keeps (ih m' σ' ρ' he')
      generalize body (inv σ ρ).1 ρ = o at hb ⊢
      cases o with
      | ok σ' ρ' => exact again σ' ρ' hb
      | next h σ' ρ' => exact again σ' ρ' hb
      | leave h σ' ρ' => exact hb
      | zurueck | why | logik | hardware => exact hb

end Gabbro.Stage0.Senke
