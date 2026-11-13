module
public import Gabbro.Body.Finite
@[expose] public section

namespace Gabbro.Body

/-- A pass makes the stop condition true at the exact static bound. The final test
    succeeds; the exhaustion handler is not executed. No string equality is evaluated. -/
theorem retry_last_pass_zeuge (ρ : Env) (s : State) (done : String)
    (hs : s.local' done = .bool false) :
    step ρ (.retry 1 (.name done)
      [.bindName done (.lit (.bool true)), .exit]
      [.ret (some (.lit (.int 99)))]) s =
        .running ⟨s.world, bindLocal s.local' done (.bool true)⟩ := by
  let t : State := ⟨s.world, bindLocal s.local' done (.bool true)⟩
  have hc : eval s (.name done) = some (.bool false) := by simp only [eval, hs]
  have hb : exec ρ [.bindName done (.lit (.bool true)), .exit] s = .exited t := by
    simp only [exec, step, eval, t]
  rw [retry_next ρ 0 _ _ _ s t hc hb]
  apply retry_done
  simp only [eval, t, bindLocal_here]

/-- Arbitrarily many `next` outcomes consume exactly the supplied fuel. -/
theorem retry_exhaustion_zeuge (ρ : Env) (s : State) : ∀ n,
    step ρ (.retry n (.lit (.bool false)) [.exit]
      [.ret (some (.lit (.int 7)))]) s = .returned s (some (.int 7))
  | 0 => retry_exceeded ρ _ _ _ s rfl
  | n + 1 =>
      (retry_next ρ n _ _ _ s s rfl (by simp only [exec, step])).trans
        (retry_exhaustion_zeuge ρ s n)

/-- A nonempty traversal stops at `leave`, before a deliberately stuck second statement. -/
theorem finite_controls_zeuge (ρ : Env) (s : State) (x : String) (i j : Int) :
    step ρ (.forEach x [i, j] [.leave, .ret (some (.un .not (.lit (.int 0))))]) s =
      .running ⟨s.world, bindLocal s.local' x (.int i)⟩ := by
  apply forEach_cons_leave
  simp only [exec, step]

/-- The invariant rule and the exact execution witness hold jointly. -/
theorem retry_rule_zeuge (ρ : Env) (n : Nat) :
    OperationalRule ρ (.retry n (.lit (.bool false)) [.exit]
      [.ret (some (.lit (.int 7)))]) (fun _ => True) ∧
    ∀ s, step ρ (.retry n (.lit (.bool false)) [.exit]
      [.ret (some (.lit (.int 7)))]) s = .returned s (some (.int 7)) := by
  refine ⟨retry_rule ρ _ _ _ (fun _ => True) ?_ ?_ ?_ n,
    fun s => retry_exhaustion_zeuge ρ s n⟩
  · intro s _
    exact ⟨false, rfl⟩
  · intro s _
    simp only [exec, step, GoodOutcome]
  · intro s _
    simp only [exec, step, eval, GoodOutcome]

/-- The traversal rule has an inhabited nonempty instance and returns the first
    actual index. Its pass duty and operational result use the same body. -/
theorem forEach_rule_zeuge (ρ : Env) (x : String) :
    OperationalRule ρ (.forEach x [2, 5] [.ret (some (.name x))]) (fun _ => True) ∧
      ∀ s, finalValue (exec ρ [.forEach x [2, 5] [.ret (some (.name x))]] s) =
        some (.int 2) := by
  constructor
  · apply forEach_rule
    intro i _ s _
    simp only [exec, step, eval, bindLocal_here, GoodOutcome]
  · intro s
    let entry : State := ⟨s.world, bindLocal s.local' x (.int 2)⟩
    have hb : exec ρ [.ret (some (.name x))] entry = .returned entry (some (.int 2)) := by
      simp only [exec, step, eval, entry, bindLocal_here]
    rw [exec_singleton, forEach_cons_returned ρ x 2 [5] [.ret (some (.name x))]
      s entry (some (.int 2)) hb]
    rfl

end Gabbro.Body
