/-
  GAP-23 `inductlist` (G-SCHEME) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, twenty-third LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, section 6): inductlist = induct { "," induct }.
  `fndecl` carries `[ "by" inductlist ]`.

  MAPPING RULE (tree vs token). `inductlist` has no constructor: it names the
  compiler-generated induction SCHEMES, and no lemma and no proof step enter
  the term. The parser collects the scheme names as compiler data guiding
  which induction principle the backend generates; the elaborated function
  (signature, contract, body) is identical with the clause removed. The single
  scheme `induct` is p22's even gap; this gap is the LIST.

  MINIMAL PARSE WITNESS. Surface `by induction over descendants of s,
  ancestors of s`: two scheme names, term unchanged. The model below states
  the erasure: the body function ignores the scheme list.
-/

namespace P21.Gap23InductList

/-- Erasure: the elaborated body does not depend on the named schemes. -/
def eraseSchemes (schemes : List String) (body : Nat) : Nat :=
  match schemes with
  | [] => body
  | _ :: rest => eraseSchemes rest body

-- Surface `by induction over descendants of s, ancestors of s`: body unchanged.
example : eraseSchemes ["descendants of s", "ancestors of s"] 7 = 7 := rfl
-- Absent `by` clause: the empty scheme list, same body.
example : eraseSchemes [] 7 = 7 := rfl

-- No carrier link by design: schemes name compiler-generated principles;
-- no lemma and no proof step enter any term.

end P21.Gap23InductList
