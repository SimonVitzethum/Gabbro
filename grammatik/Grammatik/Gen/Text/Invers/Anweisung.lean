/-
  File:      Grammatik/Gen/Text/Invers/Anweisung.lean
  Subject:   THE ELABORATOR INVERTS THE DELABORATOR ON STATEMENTS AND BLOCKS (Tier 2.1, step 2): the flat
             statement list the elaborator builds (`uAnwReihe`, then `uEnde` for the ender) from the printed body
             is the plain data `uOfBl`/`uOfEnd` computes from the model's body itself.

  Fragment of this step: `let` of a number or a truth value, slot and static writes, `if`, `locks`, `traverse`
  (with its invariant), `return` and `return R::C`. Calls, registers and atomics follow.

  The context is `SInv`, against the accessors of the declaration: `EInv`'s scope description, plus the lock
  side (a lock that guards a table is one of the table's required locks, `D.braucht`; every lock held in `Λ`
  is in `ctx.held`), the result kind of the contract `V`, and the reasons.
-/
module

public import Grammatik.Gen.Text.Invers.Anweisung.Teil1
public import Grammatik.Gen.Text.Invers.Anweisung.Teil2
