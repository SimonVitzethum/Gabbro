/-
  File:      Grammatik/Parser/Rundlauf3.lean
  Subject:   T3 (lane 179): finish the round-trip induction -- widen the
              predicate level by level (MUSE-REPORT-172 "Open" first).

  Lane 172 proved `parse_druck_kern` for `gutKern` by a joint SIZE
  induction (`kernRB`: `RKern n` with four binary-inner invariants),
  and listed the remaining levels with exact blockers: comparisons
  (`BKernCmp`, ~150 lines), bit operators (`BKernBit`, the `+` shape
  one level up), the remaining add/mul spellings (one B-trace
  duplicate plus op-table facts each), calls with argument lists
  (`parseArgs` round trip, ~200 lines), and `sizeof`/`lenof`/
  `aligned` (resisted in lane 161).

  This file takes a different, cheaper road to the same widening.
  Observation: every B-step in Rundlauf2 uses its invariant ONLY at
  strict subterms (the operand legs), and every tower takes its B-leg
  as a hypothesis. So instead of re-running a joint size induction
  per level, this file works with predicate-free legs:

  - `Legs e`: the eight fuel-generalised round-trip legs for ONE
    fixed tree (the `RKern` leg shapes with the size bound dropped).
  - `legsKern`: every `gutKern` tree has legs (repackaged `kernRB`).
  - one generic B-step per new operator group (taking operand legs
    plus op-table facts as hypotheses, no predicate anywhere), one
    generic spelling-blind tower (B-leg to eight legs).

  Each level then defines its predicate as the previous predicate
  plus ONE new layer over the previous predicate's trees, and proves
  legs for it from the previous level's legs. No joint induction is
  re-proved at any level; each level is one green commit.

  Honest limitation (measured, not assumed): each level covers one
  layer of its operators over the previous predicate -- `==` over
  `&` needs the `&` level below the `==` node, which the order
  (comparisons first) does not give. Arbitrary NESTING of new
  operators needs the joint size induction over a recursive
  predicate (lane 172's architecture, ~500 lines to replay the four
  old B-steps over abstract legs). That is the exact remaining
  blocker for full `gut`, stated at the end of this file.
-/
module

public import Grammatik.Parser.Round.Rundlauf3.Teil1
public import Grammatik.Parser.Round.Rundlauf3.Teil2
public import Grammatik.Parser.Round.Rundlauf3.Teil3
public import Grammatik.Parser.Round.Rundlauf3.Teil4
public import Grammatik.Parser.Round.Rundlauf3.Teil5
public import Grammatik.Parser.Round.Rundlauf3.Teil6
