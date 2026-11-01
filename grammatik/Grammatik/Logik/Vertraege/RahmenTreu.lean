/-
  File:      Grammatik/RahmenTreu.lean
  Subject:   **THE FRAME, AT EVERY WORLD** -- `Rahmen` and the held locks,
             without the lock discipline's `HeldB` premise.

  WHY THIS FILE EXISTS. `Satz.lean` proves ONE theorem about a body run
  (`stmt_gutB`/`block_gutB`/`end_gutB`, `rufAt_gut`) and it bundles THREE
  facts under the name `Gut`:

    1. `Rahmen`  -- the run writes no carrier its contract does not name;
    2. `σ'.haelt = σ.haelt` -- every lock it took it gave back;
    3. every event it left is GOOD and the trace stays consistent.

  Fact 3 is what needs the lock discipline: an access event is good only if
  the locks its `Λ` names are HELD, and a `nimmt` event is good only if the
  lock ranks strictly above everything held. So the whole theorem carries
  `HeldB bo Λ σ.haelt` -- a premise about the ENTRY WORLD.

  Facts 1 and 2 do not need it, and this file says so by proving them alone,
  by the same induction with the premise deleted:

    * a write goes to a carrier the constructor's own `hw : V.schreibt t =
      true` names -- nothing about locks;
    * a read (`lese`) appends `zugriff` events, which `offen` ignores
      (`lese_haelt`);
    * `locks L { .. }` is `nimmt L`, the body, `gibt L`, and
      `offen (gibt L :: nimmt L h :: s) = (L :: offen s).erase L = offen s`
      -- `List.erase` takes the FIRST occurrence, so this holds even at a
      world that ALREADY holds `L`. (Such a world is not well-disciplined,
      and `Gut` rightly refuses it: the `nimmt` event is not good there. But
      the frame and the held set survive it.)

  WHAT IT BUYS. `RufRahmenTreu P (rufAt P O passes n)` -- the frame half of
  `RespektiertRahmen` for the model's own call handler, at EVERY world --
  which `rufAt_gut` gives only at worlds meeting
  `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt`.
  Part 4 of the closing theorem quantifies over ANY Gabbro world, so it was
  carried as a named hypothesis of `rufAt_nurAbstieg` (RufLogik.lean) until
  this file. See `messung/muse/OPUS-BERICHT-RAHMEN.md`.

  THE ONE PREMISE THAT STAYS is the hardware's: an axiom answer keeps the
  frame of its `effects` and leaves the held locks alone (`TreuO`, the first
  two conjuncts of `GutO`). That is H1 and it is named, not hidden.
-/
module

public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil3
