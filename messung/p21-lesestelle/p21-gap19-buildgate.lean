/-
  GAP-19 `buildgate` (G-FILTER) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, nineteenth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, section 1): buildgate = "when" "TESTBUILD".
  `item = [ buildgate ] ( ... )`.

  MAPPING RULE (tree vs token). `buildgate` has no constructor: it is a FILTER
  on the item list applied BEFORE the theorem. `gabbro emit --testbuild` opens
  the gate; without the flag a gated item produces no line of C, and the
  shipped tree never contained it. Present items carry no trace of the gate --
  the theorem is about the items that are there. `G001` holds the one breaking
  direction (ungated code calling a gated function), `G002` refuses any other
  condition, `G003` refuses the name as a declaration; `TESTBUILD` is a G6
  identifier in fixed position, not vocabulary.

  MINIMAL PARSE WITNESS. Items `[gated a, b]`: with the flag both survive,
  without it only `b` does -- and `b`'s tree is identical in both runs. The
  model below is the filter; each pair is (name, gated?).
-/

namespace P21.Gap19BuildGate

/-- Item-list filter: a gated item survives iff the testbuild flag is set. -/
def gateFilter (testbuild : Bool) (items : List (String × Bool)) : List String :=
  items.filterMap fun (name, gated) => if gated && !testbuild then none else some name

-- Shipping build: the gated item is gone, the ungated one keeps no trace.
example : gateFilter false [("a", true), ("b", false)] = ["b"] := rfl
-- Testbuild: both present, same `b` as above.
example : gateFilter true [("a", true), ("b", false)] = ["a", "b"] := rfl
-- No gate anywhere: the filter is the identity on names.
example : gateFilter false [("b", false)] = ["b"] := rfl

-- No carrier link by design: filtering happens before the theorem;
-- present items carry no trace of the gate.

end P21.Gap19BuildGate
