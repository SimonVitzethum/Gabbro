/-
  File:      Grammatik/Zielsatz/RuheNutzer.lean
  Subject:   THE USER'S LOGIC AND THE HARDWARE ASSUMPTIONS TRANSFER TO
             P.mitRuhe (the runtime's idle root, MitRuhe.lean).

  * `logikPflicht_mitRuhe`: `LogikPflicht P S Q` (the body half of `NutzerPflicht`) gives
    `LogikPflicht P.mitRuhe S.mitRuhe (axEnsRuhe Q)`. At `some f` the
    obligation of `D.mitRuhe` quantifies over oracles, moves and handlers of
    `D.mitRuhe`; each is answered by one of `D` (`Orakel.zurueck`,
    `umweltZ`, `rufZuD`) in the same class, and the translated body runs as
    the body (`rumpfH_mitRuhe`, MitRuheSperre.lean). At the root `none`
    (body `return`, `ensures true`, no reason, writes nothing) the
    obligation holds outright.
  * `hardware_mitRuhe`: `HardwareAnnahmen O Q` gives
    `HardwareAnnahmen O.mitRuhe (axEnsRuhe Q)`.

  `axEnsRuhe Q` -- the declared axiom ensures of `D.mitRuhe`: `Q` on the
  translated-back answer world and result. It is not in `Spec.lean`: the
  statement names `Q` only on `P`; the flagships on `P.mitRuhe` are
  instantiated with this family.
-/
module

public import Grammatik.Zielsatz.Faeden.RuheNutzer.Teil1
public import Grammatik.Zielsatz.Faeden.RuheNutzer.Teil2
