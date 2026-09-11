/-
  P22 probe, LESESTELLE gap #14 `comment` (G-LEX).
  Rule: a comment starts at `--` and runs to the newline; it is discarded
  before parsing, so the token stream with the comment equals the one
  without. No constructor takes a comment.
  Witness: the `--` head of the rule, with checked examples.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/

/-- Gap #14: a comment starts at `--`. -/
def p22CommentStart (s : String) : Bool :=
  match s.toList with
  | '-' :: '-' :: _ => true
  | _ => false

example : p22CommentStart "-- reason for the bound" = true := rfl
example : p22CommentStart "--" = true := rfl
example : p22CommentStart "- x" = false := rfl
example : p22CommentStart "" = false := rfl
