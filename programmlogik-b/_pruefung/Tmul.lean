#check @Int.mul_le_mul
#check @Int.mul_nonneg
#check @Int.mul_le_mul_of_nonneg_left
example (a b : Int) (ha : 0 ≤ a) (hb: 0 ≤ b) (h1 : a ≤ 5) (h2 : b ≤ 7) : a * b ≤ 5 * 7 := Int.mul_le_mul h1 h2 hb (by omega)
example (a b c: Int) (h : a * b ≤ 35) (h2 : 0 ≤ a*b) : 0 ≤ a * b + c ∨ c < 0 := by omega
