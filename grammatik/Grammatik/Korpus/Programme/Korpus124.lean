/-
  File:      Grammatik/Korpus124.lean
  Subject:   THE G PROGRAM OF `beispiele/0124-two-threads-private.gab`, with the
             bodies of the source (stage (b) of the translation-validation
             plan, §7), and every premise group of the goal theorem on it.

  WHY A NEW MODEL. The exporter refuses 124 (`gabbro lean-g`: `LG003
  requires-clause in setze has no G form`, measured 2026-09-15); its hand
  model `mP` (`MehrfadenZeuge.lean`) differs from the source in two BODIES:
  `pruefeA` there returns nothing and reads nothing, while the source's
  `pruefeA` returns `privA.slots[0].stand`; and `mP` has an extra idle
  function `ruhe`. The C the emitter writes reads `privA` in `pruefeA`, so a
  simulation of that C needs a G program that reads it too -- otherwise the
  C footprint of the call `(void)pruefeA();` is not covered by any G access,
  and the race transfer (`rennfreiC_aus_sim`) has nothing to stand on.

  This file is `mP` with the source's bodies: functions `setze`, `pruefeA`,
  `hauptA`, `hauptB` (no `ruhe`: the runtime's idle root is `mitRuhe`'s),
  `pruefeA : -> Stand` returning `privA[0]`, no table invariant (the source
  declares none).

  THE CONTRACTS, AND ONE FINDING. Contracts are the user's logic; they do not
  change the C. They are the source's, except `setze`'s `ensures`: the source
  says only `konto.slots[0].stand == x`, and with that `ensures` the release
  check of `hauptA`'s `locks L { setze(30) }` fails for a callee answer the
  contract admits (`konto[1]` is free), so obligation (b) of the goal theorem
  does NOT hold for the source as written. The model keeps `mP`'s
  `ensures konto[0] == konto[1] && konto[0] == x` (the strongest the body
  meets). Reported in PLAN §7; the source is not changed here.

  UPDATE 2026-09-17 (lane 204, merge `5ececd63`, OFFEN O12 half (1)): the
  source now carries exactly this `ensures`
  (`konto.slots[0].stand == konto.slots[1].stand && konto.slots[0].stand == x`),
  so `kP`'s contracts are the source's without exception. The paragraph above
  is kept as the record of the finding.
-/
module

public import Grammatik.Korpus.Programme.Korpus124.Teil1
public import Grammatik.Korpus.Programme.Korpus124.Teil2
