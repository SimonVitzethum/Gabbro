/-
  File:      Grammatik/ZielOrtGeraetZeuge.lean
  Subject:   WITNESS FOR `ziel_ort_geraet` -- a two-thread program in which one
             thread reads a device register twice inside its lock-guarded
             section while the other thread writes an unrelated table; a
             register-local oracle; every premise jointly; a reached run with
             memory changes between the two reads; the double-read contract
             holds.

  The declaration `geD`: three tables of one slot (`0 .. 1`) --
  `geraet` (the device's state, guarded by `lg`), `notiz` (the reader's
  scratch table, guarded by `lg`), `tafel` (guarded by `lt`); one readable
  register `R` whose device carrier is `geraet`; four functions:

  * `leser` (holds `lg` by signature, writes `notiz`, `ensures result`):
      `if true { let x = R; notiz[0] := 1; let y = R; return x == y };
       return true`
    The two reads are separated by the reader's OWN write to `notiz`: the
    sequential world changes between them, and only register locality (the
    register's device carrier is `geraet`, not `notiz`) makes `x == y`
    provable -- the user obligation `KoerperGutG` uses `RegLokal`.
  * `haupt` (holds `lg`, thread 0's entry): `leser(); return`;
  * `schreiber` (holds `lt`, thread 1's entry): `tafel[0] := 1; return`;
  * `ruhe` (every other thread): `return`.

  The oracle `geO` answers the register from the device carrier:
  `R = geraet[0]` -- register-local, but NOT memory-independent.

  The run: thread 0 calls `leser`, reads `R` (`0`), writes `notiz`; thread 1
  writes `tafel`; thread 0 reads `R` again (`0`) and returns `0 == 0`. Both
  memory changes lie between the two reads.
-/
module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge.Teil1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge.Teil2
