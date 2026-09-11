/-
  P22 probe, LESESTELLE gap #10 `string` (G-LEX).
  Rule: a string is quote-delimited character runs; adjacent quoted parts
  concatenate (B22 doubling for an embedded quote). Strings stay content of
  claim, reason, assume, section, and asm strings; no constructor takes one.
  Witness: the concatenation of adjacent parts, with checked examples.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/

/-- Gap #10: adjacent quoted parts of one string concatenate. -/
def p22StringParts (parts : List String) : String :=
  String.join parts

example : p22StringParts ["ab", "cd"] = "abcd" := rfl
example : p22StringParts ["say \"hi\"", "!"] = "say \"hi\"!" := rfl
example : p22StringParts [] = "" := rfl
