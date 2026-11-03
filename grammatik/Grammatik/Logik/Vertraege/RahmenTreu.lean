/-
  File:      Grammatik/RahmenTreu.lean
  Subject:   **THE FRAME AND THE HELD LOCKS, WITHOUT THE TRACE** -- `Rahmen`
              and the held locks, without the trace quality's `Brav` premise.

  WHY THIS FILE EXISTS. `Satz.lean` proves ONE theorem about a body run
  (`stmt_gutB`/`block_gutB`/`end_gutB`, `rufAt_gut`) and it bundles THREE
  facts under the name `Gut`:

    1. `Rahmen`  -- the run writes no carrier its contract does not name;
    2. `σ'.haelt = σ.haelt` -- every lock it took it gave back;
    3. every event it left is GOOD and the trace stays consistent.

  Fact 3 is what needs the full lock discipline. Facts 1 and 2 need only its
  static half: the entry discipline (`HeldB` at the callee entry, transported
  with `RufPasst`) and the static scope discipline (`ScopesOkProg`: every
  scoped return spares the residual and respects the floor). This file proves
  them alone, by the same induction with the trace deleted from the
  conclusion:

    * a write goes to a carrier the constructor's own `hw : V.schreibt t =
      true` names -- nothing about locks;
    * a read (`lese`) appends `zugriff` events, which `offen` ignores
      (`lese_haelt`);
    * `locks L { .. }` is `nimmt L`, the body, `gibt L`, and
      `offen (gibt L :: nimmt L h :: s) = (L :: offen s).erase L = offen s`
      -- `List.erase` takes the FIRST occurrence, so this holds even at a
      world that ALREADY holds `L`;
    * a call restores the frame: the callee's normal return keeps every held
      lock (`TreuR` under the transported entry discipline), a propagated
      reason collapses its release (`TreuRet.toTreu_entry`) before the
      continuation runs. A `TreuRet` prefix alone transports only returning
      outcomes -- the false `TreuAusgang.vorRet` (C11) is replaced by the
      call-specific `vorCall`.

  WHAT IT BUYS. `RufRahmenTreu P (rufAt P O passes n)` -- the frame half of
  `RespektiertRahmen` for the model's own call handler, at every disciplined
  world -- which `rufAt_gut` gives only together with the trace. The entry
  discipline cannot be deleted: a callee return may release scopes, and only
  the discipline makes the release vacuous at the call boundary.

  THE PREMISES THAT STAY are the hardware's (an axiom answer keeps the frame
  of its `effects` and leaves the held locks alone: `TreuO`, the first two
  conjuncts of `GutO` -- that is H1 and it is named, not hidden), the static
  scope discipline (`ScopesOkProg`) and the entry discipline (`HeldB`).
-/
module

public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindBlock
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindEnd
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil3
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil4
