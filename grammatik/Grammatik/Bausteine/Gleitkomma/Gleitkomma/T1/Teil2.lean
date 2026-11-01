module

public import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gleitkomma

/-- Monotonicity of the significand decision: a larger value (same
    denominator, quotient-remainder ordered, the upper remainder normalised)
    never rounds down further. `hr₂` is load-bearing (`5,0` vs `3,25` at
    `den = 10` breaks it); the lower remainder needs no bound. -/
theorem rundeInt_monoton (quo₁ rest₁ quo₂ rest₂ den : Nat)
    (hr₂ : rest₂ < den)
    (h : quo₁ * den + rest₁ ≤ quo₂ * den + rest₂) :
    rundeInt quo₁ rest₁ den ≤ rundeInt quo₂ rest₂ den := by
  have hle : quo₁ ≤ quo₂ := by
    by_cases hc : quo₁ ≤ quo₂
    · exact hc
    · have hlt : quo₂ < quo₁ := by omega
      have hsplit : quo₁ = quo₂ + (quo₁ - quo₂) :=
        (Nat.add_sub_cancel' (Nat.le_of_lt hlt)).symm
      have hdecomp : quo₁ * den = quo₂ * den + (quo₁ - quo₂) * den := by
        have hcong := congrArg (· * den) hsplit
        rw [Nat.add_mul] at hcong
        exact hcong
      have hle2 : (quo₁ - quo₂) * den ≤ rest₂ := by omega
      have hge : den ≤ (quo₁ - quo₂) * den := by
        have h1 : (1 : Nat) ≤ quo₁ - quo₂ := by omega
        have h2 := Nat.mul_le_mul h1 (Nat.le_refl den)
        simpa using h2
      omega
  have hrest : quo₁ = quo₂ → rest₁ ≤ rest₂ := by
    intro heq; subst heq; exact Nat.le_of_add_le_add_left h
  rcases Nat.lt_or_ge den (2 * rest₁) with h1 | h1
  · -- Side 1 rounds up.
    have r1 := rundeInt_steig quo₁ rest₁ den h1
    rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
    · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
    · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
      · rw [r1, rundeInt_fall quo₂ rest₂ den k2]
        by_cases heq : quo₁ = quo₂
        · subst heq; have hr := hrest rfl; omega
        · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
      · have htie2 : 2 * rest₂ = den := by omega
        by_cases p2 : quo₂ % 2 = 1
        · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
            unfold rundeInt
            rw [if_neg (by omega : ¬ den < 2 * rest₂),
                if_neg (by omega : ¬ 2 * rest₂ < den),
                if_pos (by simpa using p2)]
          rw [r1, r2]; omega
        · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
            unfold rundeInt
            rw [if_neg (by omega : ¬ den < 2 * rest₂),
                if_neg (by omega : ¬ 2 * rest₂ < den),
                if_neg (by simpa using p2)]
          rw [r1, r2]
          by_cases heq : quo₁ = quo₂
          · subst heq; have hr := hrest rfl; omega
          · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
  · -- Side 1 stays down or ties.
    rcases Nat.lt_or_ge (2 * rest₁) den with k1 | k1
    · have r1 := rundeInt_fall quo₁ rest₁ den k1
      rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
      · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
      · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
        · rw [r1, rundeInt_fall quo₂ rest₂ den k2]; omega
        · by_cases p2 : quo₂ % 2 = 1
          · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
              unfold rundeInt
              rw [if_neg (by omega : ¬ den < 2 * rest₂),
                  if_neg (by omega : ¬ 2 * rest₂ < den),
                  if_pos (by simpa using p2)]
            rw [r1, r2]; omega
          · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
              unfold rundeInt
              rw [if_neg (by omega : ¬ den < 2 * rest₂),
                  if_neg (by omega : ¬ 2 * rest₂ < den),
                  if_neg (by simpa using p2)]
            rw [r1, r2]; omega
    · -- Tie on side 1.
      by_cases p1 : quo₁ % 2 = 1
      · have r1 : rundeInt quo₁ rest₁ den = quo₁ + 1 := by
          unfold rundeInt
          rw [if_neg (by omega : ¬ den < 2 * rest₁),
              if_neg (by omega : ¬ 2 * rest₁ < den),
              if_pos (by simpa using p1)]
        rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
        · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
        · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
          · rw [r1, rundeInt_fall quo₂ rest₂ den k2]
            by_cases heq : quo₁ = quo₂
            · subst heq; have hr := hrest rfl; omega
            · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
          · by_cases p2 : quo₂ % 2 = 1
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_pos (by simpa using p2)]
              rw [r1, r2]; omega
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_neg (by simpa using p2)]
              rw [r1, r2]
              by_cases heq : quo₁ = quo₂
              · subst heq; have hr := hrest rfl; omega
              · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
      · have r1 : rundeInt quo₁ rest₁ den = quo₁ := by
          unfold rundeInt
          rw [if_neg (by omega : ¬ den < 2 * rest₁),
              if_neg (by omega : ¬ 2 * rest₁ < den),
              if_neg (by simpa using p1)]
        rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
        · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
        · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
          · rw [r1, rundeInt_fall quo₂ rest₂ den k2]; omega
          · by_cases p2 : quo₂ % 2 = 1
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_pos (by simpa using p2)]
              rw [r1, r2]; omega
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_neg (by simpa using p2)]
              rw [r1, r2]; omega

/-! ## Theorems: bit lengths bound their numbers. -/

theorem bitlenAux_null (n : Nat) : bitlenAux n 0 = 0 := by rfl

theorem bitlenAux_succ (n fuel : Nat) :
    bitlenAux n (fuel + 1) = if n = 0 then 0 else 1 + bitlenAux (n / 2) fuel := by rfl

theorem bitlenAux_null_all (fuel : Nat) : bitlenAux 0 fuel = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel _ => simp only [bitlenAux_succ, ↓reduceIte]

theorem zweiHoch_succ (k : Nat) : (2 : Nat) ^ (1 + k) = 2 * 2 ^ k := by
  rw [Nat.pow_add]

/-- Upper bound: `fuel` bits suffice whenever the number fits in `fuel` bits. -/
theorem bitlenAux_obere (fuel n : Nat) (h : n < 2 ^ fuel) :
    n < 2 ^ (bitlenAux n fuel) := by
  induction fuel generalizing n with
  | zero => rw [bitlenAux_null]; exact h
  | succ fuel ih =>
    rw [bitlenAux_succ]
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, Nat.pow_zero, Nat.lt_add_one]
    · simp only [hn, if_false]
      have hhalf : n / 2 < 2 ^ fuel := by
        have e : (2 : Nat) ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ 2 fuel
        have hmod := Nat.div_add_mod n 2
        omega
      have ih' := ih (n / 2) hhalf
      have e2 := zweiHoch_succ (bitlenAux (n / 2) fuel)
      have hmod := Nat.div_add_mod n 2
      omega


end Gabbro.Grammatik.Gleitkomma
