/-
  File:      Grammatik/Parser/Rundlauf2.lean
  Subject:   T3 (lane 172): the round-trip MAIN induction, one level at a
             time (MUSE-REPORT-161 "Open" first).

  Lane 161 built the printer (`druckToks`), the fuel bound
  (`brennstoff`), the printability predicate (`gut`), the stop lemmas
  and the single-constructor primaries, but left `prim_bin`,
  `un_X_all`, `B_one`, `rundlauf_n` and `parse_druck` open: aiming at
  all constructors at once never closed.

  This file avoids that trap: it proves the round trip for a
  SUB-grammar first and widens the predicate level by level, each
  step green before the next starts.

  Step A (this chunk and the next): `gutKern` -- literals, variables,
  unary `!` and parenthesised binary operators of ONE precedence
  level (`+`). The invariant `RKern n` is lane 161's `R n`
  restricted to `gutKern`, with one deliberate change: `parseUnary`
  and `parsePrimary` take NO `ruhig` premise (they run no loop, so a
  loop operator behind the tree never reaches them -- the inner left
  operand of `B` parses with a `+` behind it). `BKern n` is the
  binary-inner parse for `+` with a general tail `W` (the tail
  behind `)` is never inspected, so it takes no follow premise).
  Both are proved together (`kernRB`) by size induction on `n`,
  following the file conventions (no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; every premise used).
-/
module

public import Grammatik.Parser.Round.Rundlauf2.Teil1
public import Grammatik.Parser.Round.Rundlauf2.Teil2
public import Grammatik.Parser.Round.Rundlauf2.Teil3
public import Grammatik.Parser.Round.Rundlauf2.Teil4
public import Grammatik.Parser.Round.Rundlauf2.Teil5
public import Grammatik.Parser.Round.Rundlauf2.Teil6
public import Grammatik.Parser.Round.Rundlauf2.Teil7
public import Grammatik.Parser.Round.Rundlauf2.Teil8
public import Grammatik.Parser.Round.Rundlauf2.Teil9
