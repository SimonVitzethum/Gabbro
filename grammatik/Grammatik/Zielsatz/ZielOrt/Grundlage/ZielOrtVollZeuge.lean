/-
  File:      Grammatik/ZielOrtVollZeuge.lean
  Subject:   WITNESS FOR `ziel_ort_voll` -- a two-thread program whose bodies
             use an indirect call, a loop with `leave`, a reason return caught by
             `let … else`, and an axiom call writing a guarded table under
             its lock; every premise jointly, and a reached run of G with a
             memory change.

  The declaration `vD`: one table (one boolean slot, guarded by the one
  lock), one axiom writing that table, three functions:

  * `ferr` (`or R`, one reason): `return R` -- the error return;
  * `mid`: `if true { let x = ferr() else r => { return } }; return` --
    the reason is caught by the `else` block;
  * `haupt` (holds no lock; every thread's entry):
    `(&mid)(); retry 1 until false { leave } on_exceeded { };
     locks L { ax() }; return` -- an indirect call of `mid` through a
    function pointer, a loop left by `leave`, then the axiom call under the
    table's lock.

  All contracts are `true`: the witness is about the premises and the run,
  not about a clever contract. The oracle `vO` sets the slot to `true` and
  records its write (`GutO`).
-/
module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge.Teil2
