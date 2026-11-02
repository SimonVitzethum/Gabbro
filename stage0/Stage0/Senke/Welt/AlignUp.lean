/-! Byte alignment arithmetic for canonical layouts. -/
module
public import Stage0.Senke.Welt.WeltAt

@[expose] public section
namespace Gabbro.Stage0.Senke

/-- The smallest multiple of `n` at least `a`; zero imposes no alignment. -/
def alignUp (a n : Nat) : Nat :=
  if n = 0 ∨ a % n = 0 then a else a + (n - a % n)

@[simp] theorem alignUp_zero (a : Nat) : alignUp a 0 = a := by
  simp [alignUp]

@[simp] theorem alignUp_one (a : Nat) : alignUp a 1 = a := by
  simp [alignUp]

theorem le_alignUp (a n : Nat) : a ≤ alignUp a n := by
  unfold alignUp
  split <;> omega

theorem alignUp_le_add (a n : Nat) : alignUp a n ≤ a + n := by
  unfold alignUp
  split <;> omega

theorem alignUp_dvd (a n : Nat) (hn : 0 < n) : n ∣ alignUp a n := by
  unfold alignUp
  split
  next h =>
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rcases h with h | h
    · omega
    · exact h
  next h =>
    have hm := Nat.mod_lt a hn
    have hd := Nat.mod_add_div a n
    refine ⟨a / n + 1, ?_⟩
    rw [Nat.mul_succ]
    omega

end Gabbro.Stage0.Senke
