/-
  P22 probe, LESESTELLE gap #12 `quote` (G-LEX).
  Rule: the quote is the delimiter U+0022. It opens and closes every string
  and every asm string; it is never content and never reaches the tree.
  Witness: the delimiter code point, checked.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/

/-- Gap #12: the quote delimiter is U+0022. -/
example : '"'.toNat = 34 := rfl
