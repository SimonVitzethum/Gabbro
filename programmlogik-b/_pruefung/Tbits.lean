#check @Nat.and_le_right
#check @Nat.and_le_left
#check @Nat.or_le_two_pow
#check @Nat.xor_lt_two_pow
#check @Nat.or_lt_two_pow
example (n : Int) (h : 0 ≤ n) (h2 : n ≤ 255) : (0:Int) ≤ ↑(n.toNat &&& 251) ∧ (↑(n.toNat &&& 251) : Int) ≤ 255 := by have := Nat.and_le_right (n := n.toNat) (m := 251); omega
