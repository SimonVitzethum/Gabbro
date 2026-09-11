/-
  GAP-17 `identlist` (G-NAME) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, seventeenth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): identlist = ident { "," ident }.
  One comma rule (Lexis): separating comma, trailing comma optional.

  MAPPING RULE (tree vs token). `identlist` has no constructor as a term: it
  is the NAME-LIST argument of `maintains`, `preserves`, `clobbers` and
  `measures` lists. The parser splits on commas (dropping the optional
  trailing one), resolves each spelling (GAP-01), and hands the name LIST to
  the enclosing declaration constructor. The commas and the single-string
  spelling are erased; the list is data, not a term.

  MINIMAL PARSE WITNESS. Surface `maintains cdt_wellformed, refcount_matches`
  (SYNTAX.md section 6 example) yields the two names as a list. The model
  below is the split step, including the optional trailing comma.
-/

namespace P21.Gap17IdentList

/-- ASCII-space trim (local: `String.trim` changed type in this toolchain). -/
def trimSp (s : String) : String :=
  let cs := s.toList.dropWhile (· == ' ')
  String.ofList (cs.reverse.dropWhile (· == ' ')).reverse

/-- Comma split over characters (`String.splitOn` does not reduce in this
    toolchain, so the split is explicit; structural on the input). -/
def splitComma : List Char → List (List Char)
  | [] => [[]]
  | ',' :: cs => [] :: splitComma cs
  | c :: cs => match splitComma cs with
    | [] => [[c]]
    | h :: t => (c :: h) :: t

/-- Comma split with the optional trailing comma dropped. -/
def identList (s : String) : List String :=
  ((splitComma s.toList).map (fun cs => trimSp (String.ofList cs))).filter (· != "")

/-- The section-6 witness: two maintained invariants. -/
example : identList "cdt_wellformed, refcount_matches" =
    ["cdt_wellformed", "refcount_matches"] := rfl
-- Trailing comma allowed by the one comma rule: same list.
example : identList "a, b," = ["a", "b"] := rfl
-- The G7 empty case (`clobbers { }` allows empty): no names.
example : identList "" = ([] : List String) := rfl

-- No carrier link by design: the list arrives as name arguments inside the
-- declaration constructors (`maintains` itself is SUGAR over `effects`);
-- there is no list term.

end P21.Gap17IdentList
