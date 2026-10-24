/-
  File:      Grammatik/Berechenbarkeit/RunsUntil.lean
  Subject:   Conditional termination over the EXISTING `foreverLauf` semantics.

  `ExitTrace` records the actual invariant checks and body outcomes on a finite execution;
  it is not a second interpreter. Completion at budget `p` is equivalent to such a trace
  with fewer than `p` continuing passes. Quantifying over budgets recovers conditional
  termination, without treating exhaustion as a successful return.

  `runsUntil` is a Lean abbreviation for `forever { if condition { leave; } body }`.
  It introduces no syntax or machine rule. The body may still fail; a proof that the
  condition eventually becomes true, or a decreasing rank, is a separate obligation.
-/
import Grammatik.Logik.Terminierung.Ausgang

namespace Gabbro.Grammatik.Terminierung

variable {D : Deklaration} {V : Vertrag D} {Γ : Ctx}

/-- A finite path to a normal exit, using exactly the checks and outcomes of `foreverLauf`.
    The index counts continuing passes; the final leaving pass costs one more unit of fuel. -/
inductive ExitTrace (step : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → World D → Env D Γ → Prop where
  | leave {σ ρ σ' ρ'} (hi : (inv σ ρ).2 = true)
      (hs : step (inv σ ρ).1 ρ = .leave rfl σ' ρ') : ExitTrace step inv 0 σ ρ σ' ρ'
  | more {n σ ρ σ1 ρ1 σ' ρ'} (hi : (inv σ ρ).2 = true)
      (hs : step (inv σ ρ).1 ρ = .ok σ1 ρ1 ∨ step (inv σ ρ).1 ρ = .next rfl σ1 ρ1)
      (tail : ExitTrace step inv n σ1 ρ1 σ' ρ') : ExitTrace step inv (n + 1) σ ρ σ' ρ'

variable {step : World D → Env D Γ → Ausgang V true Γ}
  {inv : World D → Env D Γ → World D × Bool}

/-- Every recorded exit is completed by every sufficiently large budget. -/
theorem ExitTrace.run {n σ ρ σ' ρ'} (h : ExitTrace step inv n σ ρ σ' ρ')
    (a : D.Annahme) {p : Nat} (hp : n < p) :
    foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ' := by
  induction h generalizing p with
  | leave hi hs =>
      cases p with
      | zero => omega
      | succ p => rw [foreverLauf]; simp only [hi, Bool.true_eq_false, ↓reduceIte, hs]
  | more hi hs tail ih =>
      cases p with
      | zero => omega
      | succ p =>
          rw [foreverLauf]
          simp only [hi, Bool.true_eq_false, ↓reduceIte]
          rcases hs with hs | hs <;> rw [hs] <;> exact ih (by omega)

/-- A successful execution contains a real exit trace; budget exhaustion never witnesses it. -/
theorem exitTrace_of_run (a : D.Annahme) : ∀ {p : Nat} {σ ρ σ' ρ'},
    foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ' →
      ∃ n, n < p ∧ ExitTrace step inv n σ ρ σ' ρ'
  | 0, _, _, _, _, h => by simp [foreverLauf] at h
  | p + 1, σ, ρ, σ', ρ', h => by
      rw [foreverLauf] at h
      cases hi : (inv σ ρ).2 with
      | false => simp only [hi, ↓reduceIte] at h; cases h
      | true =>
          simp only [hi, Bool.true_eq_false, ↓reduceIte] at h
          cases hs : step (inv σ ρ).1 ρ with
          | ok σ1 ρ1 =>
              rw [hs] at h
              obtain ⟨n, hn, ht⟩ := exitTrace_of_run a h
              exact ⟨n + 1, by omega, .more hi (.inl hs) ht⟩
          | next he σ1 ρ1 =>
              rw [hs] at h
              obtain ⟨n, hn, ht⟩ := exitTrace_of_run a h
              exact ⟨n + 1, by omega, .more hi (.inr hs) ht⟩
          | leave he σ1 ρ1 =>
              rw [hs] at h
              cases h
              exact ⟨0, by omega, .leave hi hs⟩
          | zurueck σ1 v => rw [hs] at h; cases h
          | why σ1 r => rw [hs] at h; cases h
          | logik e => rw [hs] at h; cases h
          | hardware e => rw [hs] at h; cases h

/-- Exact conditional termination: an exit occurs on the actual path within the granted budget. -/
theorem run_iff_exitTrace (a : D.Annahme) (p : Nat) (σ : World D) (ρ : Env D Γ)
    (σ' : World D) (ρ' : Env D Γ) :
    foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ' ↔
      ∃ n, n < p ∧ ExitTrace step inv n σ ρ σ' ρ' :=
  ⟨exitTrace_of_run a, fun ⟨_, hn, ht⟩ => ht.run a hn⟩

/-- With the pass evaluator fixed, adding fuel preserves a normal completion and its result. -/
theorem run_mono (a : D.Annahme) {p q : Nat} (hpq : p ≤ q) {σ ρ σ' ρ'}
    (h : foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ') :
    foreverLauf (l := false) a step inv q σ ρ = .ok σ' ρ' := by
  obtain ⟨n, hn, ht⟩ := exitTrace_of_run a h
  exact ht.run a (by omega)

/-- A loop terminates conditionally iff some finite trace reaches its normal exit. -/
theorem exists_run_iff_exitTrace (a : D.Annahme) (σ : World D) (ρ : Env D Γ) :
    (∃ p σ' ρ', foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ') ↔
      ∃ n σ' ρ', ExitTrace step inv n σ ρ σ' ρ' := by
  constructor
  · rintro ⟨p, σ', ρ', h⟩
    obtain ⟨n, _, ht⟩ := exitTrace_of_run a h
    exact ⟨n, σ', ρ', ht⟩
  · rintro ⟨n, σ', ρ', ht⟩
    exact ⟨n + 1, σ', ρ', ht.run a (by omega)⟩

/-- A decreasing natural rank supplies an explicit sufficient fuel bound. Every check must
    hold, and every pass must either leave or continue at a strictly smaller rank. -/
theorem run_of_rank (a : D.Annahme) (rank : World D → Env D Γ → Nat)
    (progress : ∀ σ ρ, (inv σ ρ).2 = true ∧
      ((∃ σ' ρ', step (inv σ ρ).1 ρ = .leave rfl σ' ρ') ∨
        ∃ σ' ρ', (step (inv σ ρ).1 ρ = .ok σ' ρ' ∨
          step (inv σ ρ).1 ρ = .next rfl σ' ρ') ∧ rank σ' ρ' < rank σ ρ)) :
    ∀ (p : Nat) (σ : World D) (ρ : Env D Γ), rank σ ρ < p →
      ∃ σ' ρ', foreverLauf (l := false) a step inv p σ ρ = .ok σ' ρ' := by
  intro p
  induction p with
  | zero => intro σ ρ h; omega
  | succ p ih =>
      intro σ ρ hp
      obtain ⟨hi, hstep⟩ := progress σ ρ
      rw [foreverLauf]
      simp only [hi, Bool.true_eq_false, ↓reduceIte]
      rcases hstep with ⟨σ', ρ', hs⟩ | ⟨σ', ρ', hs, hr⟩
      · exact ⟨σ', ρ', by rw [hs]⟩
      · rcases hs with hs | hs <;> rw [hs] <;> exact ih σ' ρ' (by omega)

section Syntax

variable {Λ : List (Res D)}

/-- The existing syntax for a pre-test loop: `forever { if condition { leave; } body }`. -/
def untilBody (condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) :
    Block D V true Γ Λ Λ :=
  .cons (.ite condition (.cons (.leave rfl) .nil) body) .nil

/-- Conditional termination is an abbreviation over existing syntax, not a new primitive. -/
def runsUntil (a : D.Annahme) (invariant condition : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) : Stmt D V false Γ Λ Λ :=
  .forever a invariant (untilBody condition body)

/-- Exact semantics of the abbreviation, including the read event of the guard. -/
theorem untilBody_exec (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (untilBody condition body) σ ρ =
      let σc := σ.lese Λ condition.orte
      if wahr? (eval σc condition σc ρ) then .leave rfl σc ρ else execBlock O passes R body σc ρ := by
  change execBlock O passes R (.cons (.ite condition (.cons (.leave rfl) .nil) body) .nil) σ ρ =
    execStmt O passes R (.ite condition (.cons (.leave rfl) .nil) body) σ ρ
  simp only [execBlock]
  cases execStmt O passes R (.ite condition (.cons (.leave rfl) .nil) body) σ ρ <;> rfl

/-- The complete iff, using the actual syntax and its actual execution path. -/
theorem runsUntil_iff (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (invariant condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R (runsUntil a invariant condition body) σ ρ = .ok σ' ρ' ↔
      ∃ n, n < passes ∧ ExitTrace (fun σ ρ => execBlock O passes R (untilBody condition body) σ ρ)
        (fun σ ρ => let σi := σ.lese Λ invariant.orte; (σi, wahr? (eval σi invariant σi ρ)))
        n σ ρ σ' ρ' :=
  run_iff_exitTrace a passes σ ρ σ' ρ'

/-- The guard is an exit site even if it is unsatisfiable. Classification alone therefore
    cannot prove that it is eventually taken. -/
theorem untilBody_has_exit (condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) :
    (befB true true (untilBody condition body)).austritt = true := by
  simp [untilBody, befB, befS, befund_und_austritt]

/-- Successful exit of a guarded loop establishes its actual guard, provided the body has no
    separate `leave`. Logic/hardware failures remain failures, never successful exits. -/
theorem untilBody_exit_guard (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (noLeave : ∀ σ ρ σ' ρ', execBlock O passes R body σ ρ ≠ .leave rfl σ' ρ')
    {σ ρ σ' ρ'}
    (h : execBlock O passes R (untilBody condition body) σ ρ = .leave rfl σ' ρ') :
    wahr? (eval σ' condition σ' ρ') = true := by
  rw [untilBody_exec] at h
  dsimp only at h
  split at h
  · cases h <;> assumption
  · exact False.elim (noLeave _ _ _ _ h)

/-- Every continuing pass observes a false guard. Together with `untilBody_exit_guard`
    and `runsUntil_iff`, this identifies the first successful guard check on the actual path. -/
theorem untilBody_continue_guard (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) {σ ρ σ' ρ'}
    (h : execBlock O passes R (untilBody condition body) σ ρ = .ok σ' ρ' ∨
      execBlock O passes R (untilBody condition body) σ ρ = .next rfl σ' ρ') :
    wahr? (eval (σ.lese Λ condition.orte) condition (σ.lese Λ condition.orte) ρ) = false := by
  rw [untilBody_exec] at h
  dsimp only at h
  cases hc : wahr? (eval (σ.lese Λ condition.orte) condition (σ.lese Λ condition.orte) ρ) with
  | false => rfl
  | true => simp only [hc, ↓reduceIte] at h; rcases h with h | h <;> cases h

/-- **Runs until C**: a normal completion establishes C. It does not assert that C is
    eventually reached, and it does not turn a budget or hardware stop into completion. -/
theorem runsUntil_post (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (invariant condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (noLeave : ∀ σ ρ σ' ρ', execBlock O passes R body σ ρ ≠ .leave rfl σ' ρ')
    {σ ρ σ' ρ'}
    (h : execStmt O passes R (runsUntil a invariant condition body) σ ρ = .ok σ' ρ') :
    wahr? (eval σ' condition σ' ρ') = true := by
  obtain ⟨σ1, ρ1, he, hs⟩ := foreverLauf_ok a _ _ passes σ ρ σ' ρ' h
  exact untilBody_exit_guard O passes R condition body noLeave hs

/-- An explicit rank discharges eventual termination of `runsUntil`. The body is checked
    only when the guard is false; successful completion still satisfies `runsUntil_post`. -/
theorem runsUntil_of_rank (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (invariant condition : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (rank : World D → Env D Γ → Nat)
    (checks : ∀ (σ : World D) (ρ : Env D Γ),
      let σi := σ.lese Λ invariant.orte; wahr? (eval σi invariant σi ρ) = true)
    (decreases : ∀ (σ : World D) (ρ : Env D Γ),
      let σi := σ.lese Λ invariant.orte
      let σc := σi.lese Λ condition.orte
      wahr? (eval σc condition σc ρ) = false →
        ∃ σ' ρ', (execBlock O passes R body σc ρ = .ok σ' ρ' ∨
          execBlock O passes R body σc ρ = .next rfl σ' ρ') ∧ rank σ' ρ' < rank σ ρ)
    (σ : World D) (ρ : Env D Γ) (bound : rank σ ρ < passes) :
    ∃ σ' ρ', execStmt O passes R (runsUntil a invariant condition body) σ ρ = .ok σ' ρ' := by
  apply run_of_rank a rank ?_ passes σ ρ bound
  intro σ ρ
  refine ⟨checks σ ρ, ?_⟩
  rw [untilBody_exec]
  cases hc : wahr? (eval ((σ.lese Λ invariant.orte).lese Λ condition.orte) condition
      ((σ.lese Λ invariant.orte).lese Λ condition.orte) ρ) with
  | true => exact Or.inl ⟨(σ.lese Λ invariant.orte).lese Λ condition.orte, ρ,
      by simp only [hc, ↓reduceIte]⟩
  | false =>
      obtain ⟨σ', ρ', hs, hr⟩ := decreases σ ρ hc
      exact Or.inr ⟨σ', ρ', by simpa only [hc, Bool.false_eq_true, ↓reduceIte] using hs, hr⟩

end Syntax

end Gabbro.Grammatik.Terminierung
