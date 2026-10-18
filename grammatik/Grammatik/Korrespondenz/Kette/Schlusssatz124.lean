/-
  File:      Grammatik/Schlusssatz124.lean
  Subject:   THE CLOSING THEOREM, STAGE (b), FOR `beispiele/124-two-threads-private.gab`
             (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §7):
             `schlusssatz_124`, and its witness with a contended lock.

  THE EMITTED C (`target/debug/gabbro emit beispiele/124-two-threads-private.gab`,
  binary built from this tree on 2026-09-15), function bodies:

      static void setze(uint32_t x) {
          konto_speicher.slots[0].stand = x;
          konto_speicher.slots[1].stand = x;
      }
      static uint32_t pruefeA(void) {
          return privA_speicher.slots[0].stand;
      }
      static void hauptA(void) {
          privA_speicher.slots[0].stand = 7;
          privA_speicher.slots[1].stand = 7;
          L_nimm();
          {
              setze(30);
          }
          L_gib();
          (void)pruefeA();
      }
      static void hauptB(void) {
          privB_speicher.slots[0].stand = 5;
          L_nimm();
          {
              setze(70);
          }
          L_gib();
      }

  with `typedef struct { uint32_t stand; } T_slot; typedef struct { T_slot
  slots[NSLOTS]; } T; static T T_speicher;` for `T` in `konto`, `privA`,
  `privB`, `NSLOTS = 2`, and `void L_nimm(void); void L_gib(void);` -- the
  runtime's lock primitive, not emitted. No thread is created by the emitted
  code: the runtime starts `hauptA` and `hauptB` (`concurrent { hauptA,
  hauptB }`), which is the premise `FadenStartC`.

  THE ENCODING AS DATA (`c124`): function `0` is `setze` (parameter `x` is
  local `0`), `1` `pruefeA`, `2` `hauptA`, `3` `hauptB`; objects `tab 0`,
  `tab 1`, `tab 2` are `konto_speicher`, `privA_speicher`, `privB_speicher`
  (layout `natLay 2 [uint32_t]`: record size 4, field at 0);
  `T_speicher.slots[k].stand` is `slotA (addr (tab T)) k 2 4 0`; foreign
  function `0` is `L_nimm`, `1` is `L_gib`; the braces `{ setze(30); }` are
  the call itself; `(void)pruefeA();` is the call with its answer dropped.
-/

import Grammatik.Korrespondenz.Kette.Schlusssatz124.T1
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T2
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T3
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T4
