example : (if "p" = "obj" then 1 else 2) = 2 := by simp
example (v : Nat) : (if "p" = "p" then v else 2) = v := by simp
example (v : Nat) : (if "p" = "obj" then v else 2) = 2 := by simp (config := { decide := true })
