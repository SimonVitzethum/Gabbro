/-
  File:      Grammatik/Korpus109.lean
  Subject:   THE G PROGRAM OF `beispiele/109-lockfree-entry-roots.gab`, with the
             bodies of the source, and every premise group of the goal theorem on it.

  The source: tables `T`, `U` (count 4, `u32` field `v`), locks `L`, `M`
  (ranks 0/1, disjoint carriers), leaves `write_a`/`write_b` (`requires Held`,
  one slot write of a constant), distributors `distribute_a`/`distribute_b`
  (`locks` around one call), two `entry` items dispatching to the
  distributors. Every form has a G counterpart: index params are
  `Ty.index (count)`, `requires Held` is the signature-held set, `locks`
  blocks and direct calls are `Stmt`, the entry dispatch roots are the
  declared starts, `costs` is ignored form (like `reads`). No annotation is
  dropped: 109 carries no `deadline`/`falsifier`. No lock invariant is
  declared in the source, so the family is trivially true (owed nowhere).
-/
module

public import Grammatik.Korpus.Programme.Korpus109.Teil1
public import Grammatik.Korpus.Programme.Korpus109.Teil2
