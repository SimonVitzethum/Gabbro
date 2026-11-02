/- Bounded integer folds reuse the quantifier binder and its restored frame slot. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Count true predicate words. Each iteration restores the borrowed index slot;
    the accumulator stays below the predicate's scratch area. -/
def countC (s d : Nat) (cb : List II) : Nat → Nat → List II
  | _, 0 => [ci 1 d 0 0]
  | j, n + 1 => countC s d cb (j + 1) n ++ quantBindC s (d + 1) j cb ++
      [ci 3 d d (d + 1)]

/-- The exact instruction budget, including binder save/restore and addition. -/
theorem countC_length (s d : Nat) (cb : List II) (j n : Nat) :
    (countC s d cb j n).length = 1 + n * (cb.length + 5) := by
  induction n generalizing j with
  | zero => simp [countC]
  | succ n ih => simp [countC, quantBindC, ih, Nat.succ_mul]; omega

/-- Check both index immediates and the instruction budget before expanding.
    Empty domains emit zero without demanding predicate code. -/
def countL (s d n : Nat) (body : Option (List II × Nat)) : Option (List II × Nat) :=
  if n = 0 then some ([ci 1 d 0 0], d + 1)
  else do
    let cb ← body
    if n < 2 ^ 31 ∧ 1 + n * (cb.1.length + 5) < 2 ^ 31 then
      some (countC s d cb.1 0 n, max cb.2 (d + 4))
    else none

theorem countL_bounds {s d n top : Nat} {body : Option (List II × Nat)} {c : List II}
    (h : countL s d n body = some (c, top)) :
    d < top ∧ n < 2 ^ 31 ∧ c.length < 2 ^ 31 := by
  unfold countL at h
  split at h
  · next zero =>
    subst n
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cb, tb⟩, _, h⟩ := h
    split at h
    · next budget =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      rw [countC_length]
      exact ⟨by omega, budget⟩
    · cases h

end Gabbro.Stage0.Senke
