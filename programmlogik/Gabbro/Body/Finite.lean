module
public import Gabbro.Body.Traverse
@[expose] public section

namespace Gabbro.Body

/-- Total operational rule: a terminal outcome exists and its state satisfies `P`.
    Return and loop control remain distinct; a stuck computation never satisfies it. -/
def GoodOutcome (P : State → Prop) : Outcome → Prop
  | .running s | .exited s | .left s | .returned s _ => P s
  | .stuck => False

def OperationalRule (ρ : Env) (st : Stmt) (P : State → Prop) : Prop :=
  ∀ s, P s → GoodOutcome P (step ρ st s)

theorem forEach_cons_next (ρ : Env) (x : String) (i : Int) (is : List Int)
    (body : List Stmt) (s t : State)
    (h : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ = .exited t) :
    step ρ (.forEach x (i :: is) body) s = step ρ (.forEach x is body) t := by
  simp only [step, traverseRun, h]

theorem forEach_cons_leave (ρ : Env) (x : String) (i : Int) (is : List Int)
    (body : List Stmt) (s t : State)
    (h : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ = .left t) :
    step ρ (.forEach x (i :: is) body) s = .running t := by
  simp only [step, traverseRun, h]

/-- One operational pass per declared index. In contrast to the abstract `LoopRule`,
    the body is executed and no environment answer stands for the loop. -/
theorem forEach_rule (ρ : Env) (x : String) (body : List Stmt) (P : State → Prop) :
    ∀ indices,
      (∀ i ∈ indices, ∀ s, P s →
        GoodOutcome P (exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩)) →
      OperationalRule ρ (.forEach x indices body) P
  | [], _ => fun _ hs => hs
  | i :: is, hb => by
      intro s hs
      have hp := hb i (List.mem_cons_self ..) s hs
      have ht := forEach_rule ρ x body P is
        (fun j hj => hb j (List.mem_cons_of_mem _ hj))
      cases he : exec ρ body ⟨s.world, bindLocal s.local' x (.int i)⟩ with
      | running t =>
          rw [he] at hp
          rw [forEach_cons_running ρ x i is body s t he]
          exact ht t hp
      | exited t =>
          rw [he] at hp
          rw [forEach_cons_next ρ x i is body s t he]
          exact ht t hp
      | left t => simpa only [step, traverseRun, he, GoodOutcome] using hp
      | returned t v => simpa only [step, traverseRun, he, GoodOutcome] using hp
      | stuck => simp only [he, GoodOutcome] at hp

theorem retry_done (ρ : Env) (n : Nat) (stop : Expr) (body overflow : List Stmt)
    (s : State) (hc : eval s stop = some (.bool true)) :
    step ρ (.retry n stop body overflow) s = .running s := by
  cases n <;> simp only [step, retryRun, hc]

theorem retry_exceeded (ρ : Env) (stop : Expr) (body overflow : List Stmt)
    (s : State) (hc : eval s stop = some (.bool false)) :
    step ρ (.retry 0 stop body overflow) s = exec ρ overflow s := by
  simp only [step, retryRun, hc]

theorem retry_running (ρ : Env) (n : Nat) (stop : Expr) (body overflow : List Stmt)
    (s t : State) (hc : eval s stop = some (.bool false))
    (hb : exec ρ body s = .running t) :
    step ρ (.retry (n + 1) stop body overflow) s =
      step ρ (.retry n stop body overflow) t := by
  simp only [step, retryRun, hc, hb]

theorem retry_next (ρ : Env) (n : Nat) (stop : Expr) (body overflow : List Stmt)
    (s t : State) (hc : eval s stop = some (.bool false))
    (hb : exec ρ body s = .exited t) :
    step ρ (.retry (n + 1) stop body overflow) s =
      step ρ (.retry n stop body overflow) t := by
  simp only [step, retryRun, hc, hb]

theorem retry_leave (ρ : Env) (n : Nat) (stop : Expr) (body overflow : List Stmt)
    (s t : State) (hc : eval s stop = some (.bool false))
    (hb : exec ρ body s = .left t) :
    step ρ (.retry (n + 1) stop body overflow) s = .running t := by
  simp only [step, retryRun, hc, hb]

theorem retry_returned (ρ : Env) (n : Nat) (stop : Expr) (body overflow : List Stmt)
    (s t : State) (v : Option Value) (hc : eval s stop = some (.bool false))
    (hb : exec ρ body s = .returned t v) :
    step ρ (.retry (n + 1) stop body overflow) s = .returned t v := by
  simp only [step, retryRun, hc, hb]

/-- The finite rule has three explicit duties: a typed test, a preserving pass and a
    preserving exhaustion handler. The handler is required even at a zero bound. -/
theorem retry_rule (ρ : Env) (stop : Expr) (body overflow : List Stmt) (P : State → Prop)
    (hc : ∀ s, P s → ∃ b, eval s stop = some (.bool b))
    (hb : ∀ s, P s → GoodOutcome P (exec ρ body s))
    (he : ∀ s, P s → GoodOutcome P (exec ρ overflow s)) :
    ∀ n, OperationalRule ρ (.retry n stop body overflow) P
  | 0 => by
      intro s hs
      obtain ⟨b, ht⟩ := hc s hs
      cases b with
      | true => rw [retry_done ρ 0 stop body overflow s ht]; exact hs
      | false => rw [retry_exceeded ρ stop body overflow s ht]; exact he s hs
  | n + 1 => by
      intro s hs
      obtain ⟨b, ht⟩ := hc s hs
      cases b with
      | true => rw [retry_done ρ (n + 1) stop body overflow s ht]; exact hs
      | false =>
          have hp := hb s hs
          cases hx : exec ρ body s with
          | running t =>
              rw [hx] at hp
              rw [retry_running ρ n stop body overflow s t ht hx]
              exact retry_rule ρ stop body overflow P hc hb he n t hp
          | exited t =>
              rw [hx] at hp
              rw [retry_next ρ n stop body overflow s t ht hx]
              exact retry_rule ρ stop body overflow P hc hb he n t hp
          | left t => simpa only [step, retryRun, ht, hx, GoodOutcome] using hp
          | returned t v => simpa only [step, retryRun, ht, hx, GoodOutcome] using hp
          | stuck => simp only [hx, GoodOutcome] at hp

/-- Small-step automation unfolds no strings, contexts or whole units. -/
macro "gabbro_finite" : tactic =>
  `(tactic| first
    | apply Gabbro.Body.forEach_rule
    | apply Gabbro.Body.retry_rule)

end Gabbro.Body
