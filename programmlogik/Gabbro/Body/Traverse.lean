module
public import Gabbro.Body.Teil3
@[expose] public section

namespace Gabbro.Body

theorem exec_singleton (ρ : Env) (st : Stmt) (s : State) : exec ρ [st] s = step ρ st s := by
  cases h : step ρ st s <;> simp only [exec, h]

/-- The indices of a counted traversal. -/
def zaehlIndizes (n : Nat) : List Int := (List.range n).map Int.ofNat

/-- **A counted traversal is the traversal of its index list.** -/
theorem step_forCount (ρ : Env) (x : String) (n : Nat) (body : List Stmt) (s : State) :
    step ρ (.forCount x n body) s = step ρ (.forEach x (zaehlIndizes n) body) s := by
  simp only [step, zaehlIndizes]

/-- Operational traversal of the empty list runs zero passes. -/
theorem forEach_nil (ρ : Env) (x : String) (body : List Stmt) (s : State) :
    step ρ (.forEach x [] body) s = .running s := rfl

/-- A running pass continues on precisely the remaining ordered indices. -/
theorem forEach_cons_running (ρ : Env) (x : String) (i : Int) (is : List Int)
    (body : List Stmt) (s s' : State)
    (h : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ = .running s') :
    step ρ (.forEach x (i :: is) body) s = step ρ (.forEach x is body) s' := by
  simp only [step, traverseRun, h]

/-- A return from a pass is a return from the whole traversal. -/
theorem forEach_cons_returned (ρ : Env) (x : String) (i : Int) (is : List Int)
    (body : List Stmt) (s s' : State) (v : Option Value)
    (h : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ = .returned s' v) :
    step ρ (.forEach x (i :: is) body) s = .returned s' v := by
  simp only [step, traverseRun, h]

/-- Finite iteration preserves every world location preserved by one pass. -/
theorem forEach_frame (ρ : Env) (x : String) (body : List Stmt) (p : Place)
    (hb : ∀ s s', finalState (exec ρ body s) = some s' → s'.world p = s.world p) :
    ∀ indices s s', finalState (step ρ (.forEach x indices body) s) = some s' →
      s'.world p = s.world p
  | [], s, s', h => by
    cases h
    rfl
  | i :: is, s, s', h => by
    cases he : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ with
    | running t =>
      have hh := hb ⟨s.world, bindLocal s.local' x (.int i)⟩ t (by simp only [he, finalState])
      have ht := forEach_frame ρ x body p hb is t s'
        (by simpa only [forEach_cons_running ρ x i is body s t he] using h)
      exact ht.trans hh
    | exited t =>
      have hh := hb ⟨s.world, bindLocal s.local' x (.int i)⟩ t (by simp only [he, finalState])
      have ht := forEach_frame ρ x body p hb is t s' (by
        simpa only [step, traverseRun, he] using h)
      exact ht.trans hh
    | left t =>
      simp only [step, traverseRun, he, finalState, Option.some.injEq] at h
      subst s'
      exact hb ⟨s.world, bindLocal s.local' x (.int i)⟩ t (by simp only [he, finalState])
    | returned t v =>
      simp only [step, traverseRun, he, finalState, Option.some.injEq] at h
      subst s'
      exact hb ⟨s.world, bindLocal s.local' x (.int i)⟩ t (by simp only [he, finalState])
    | stuck => simp only [step, traverseRun, he, finalState, reduceCtorEq] at h

end Gabbro.Body
