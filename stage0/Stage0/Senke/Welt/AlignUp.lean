module
/-! Byte alignment arithmetic for canonical layouts. -/
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

/-- The common grid preserves both declared and storage alignment. -/
def wordAlign (n : Nat) : Nat := Nat.lcm 8 n

theorem alignUp_word_grid (off n : Nat) (h : 8 ∣ off) :
    8 ∣ alignUp off (wordAlign n) := by
  by_cases hz : wordAlign n = 0
  · simpa [hz] using h
  · exact Nat.dvd_trans (Nat.dvd_lcm_left 8 n)
      (alignUp_dvd off (wordAlign n) (by omega))

/-- A grid-aligned base and a produced relative offset meet both alignments. -/
theorem aligned_abs (b off N : Nat) (hN : 0 < N)
    (h : Nat.lcm 8 N ∣ b) :
    N ∣ b + alignUp off (wordAlign N) ∧
      8 ∣ b + alignUp off (wordAlign N) := by
  have grid := alignUp_dvd off (wordAlign N) (Nat.lcm_pos (by decide) hN)
  have total := Nat.dvd_add h grid
  exact ⟨Nat.dvd_trans (Nat.dvd_lcm_right 8 N) total,
    Nat.dvd_trans (Nat.dvd_lcm_left 8 N) total⟩

/-- Concrete word and non-word alignment cases. -/
theorem aligned_abs_zeuge :
    (8 ∣ 24 + alignUp 9 (wordAlign 8)) ∧
    (16 ∣ 48 + alignUp 9 (wordAlign 16)) ∧
    (24 ∣ 48 + alignUp 9 (wordAlign 24)) := by
  decide

/-- Relative offsets retain the grid even when the loader base is four. -/
theorem relative_grid_zeuge :
    (0 + alignUp 9 (wordAlign 8)) % 8 = 0 % 8 ∧
    (0 + alignUp 9 (wordAlign 16)) % 8 = 0 % 8 ∧
    (0 + alignUp 9 (wordAlign 24)) % 8 = 0 % 8 ∧
    (4 + alignUp 9 (wordAlign 8)) % 8 = 4 % 8 ∧
    (4 + alignUp 9 (wordAlign 16)) % 8 = 4 % 8 ∧
    (4 + alignUp 9 (wordAlign 24)) % 8 = 4 % 8 := by
  decide

end Gabbro.Stage0.Senke
