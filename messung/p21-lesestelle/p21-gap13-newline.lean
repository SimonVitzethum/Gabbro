/-
  GAP-13 `newline` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, thirteenth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): newline = ? end of line ?.
  comment = "--" { char } newline.

  MAPPING RULE (tree vs token). `newline` has no constructor. It is discharged
  in exactly two ways, both before parsing: it TERMINATES a `comment` (the
  comment runs to the newline and both are discarded), and elsewhere it is
  whitespace (dropped). Its only upward effect is line counting for refusal
  positions. A comment therefore leaves no trace in the tree -- not even an
  empty node.

  MINIMAL PARSE WITNESS. Surface `-- hi\nx`: the comment body is `-- hi`,
  the newline ends it, and `x` is the next token. The model below is the
  comment-body cut at the first newline.
-/

namespace P21.Gap13Newline

/-- Comment body: everything before the first newline (which is consumed, not kept). -/
def commentBody : List Char → List Char
  | [] => []
  | c :: cs => if c == '\n' then [] else c :: commentBody cs

-- Surface `-- hi\nx`: body `-- hi`, then the next token starts at `x`.
example : commentBody "-- hi\nx".toList = "-- hi".toList := rfl
-- A comment at end of input without a newline still ends: the body is everything.
example : commentBody "-- hi".toList = "-- hi".toList := rfl
-- The newline itself is never body: an empty comment.
example : commentBody "\n".toList = ([] : List Char) := rfl

-- No carrier link by design: comments are discarded before parsing;
-- nothing of them reaches any constructor.

end P21.Gap13Newline
