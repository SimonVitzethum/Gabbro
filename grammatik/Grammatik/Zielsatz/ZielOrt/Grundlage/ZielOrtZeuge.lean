/-
  File:      Grammatik/ZielOrtZeuge.lean
  Subject:   WITNESSES FOR `ziel_ort` -- the reference account with a
             lock-free thread entry: every premise jointly, a reached run
             that writes, calls and returns, and a run in which ANOTHER
             thread writes the contract's carrier under the common lock.

  The declaration `zD` is the reference declaration `refD` (one table
  `konto`, two slots of `.int 0 100`, guarded by the one lock) with four
  functions:

  * `einzahlen` (holds the lock): `konto[0] := 100; return`,
    `ensures old(konto[0]) ≤ konto[0]`;
  * `lies` (holds the lock): `let x = konto[0]; return x`,
    `ensures result = konto[0]`;
  * `wrap` (holds the lock, contract `true`): `lies(); einzahlen(); return`;
  * `haupt` (holds NO lock, contract `true`): `locks { wrap() }; return` --
    the entry of every thread.

  Why not `refP` itself: every thread of G starts in some function, and
  both functions of `refD` hold the lock by signature, so no start
  assignment of `refD` is exclusive (`StartExklusiv`) -- a thread entry that
  holds no lock is needed. And why the wrapper: `haupt` takes the lock in a
  `locks` block, so it may not rely on contracts over `konto` (the footprint
  check: callee contract carriers must be guarded by a SIGNATURE lock of the
  caller); `wrap` holds the lock by signature and calls the two functions
  whose contracts mention `konto`. (Also `refP`'s `einzahlen`, "write, then
  call `lies`", is not sequentially correct: `ensures lies` does not promise
  to leave `konto` alone, so a contract-respecting handler may answer with
  `konto[0] = 0`; `einzahlen` here writes last.)
-/
module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge.Teil1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge.Teil2
