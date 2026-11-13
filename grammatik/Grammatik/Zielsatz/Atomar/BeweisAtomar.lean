/-
  File:      Grammatik/Zielsatz/BeweisAtomar.lean
  Subject:   THE GOAL WITH THE ATOMIC RELY, PROVED (Opus lane O25c, 2026-09-26, OFFEN O25).

  * `gabbro_ziel` -- THE GOAL with the call-site duties (`BeweisAtomar/Fremd.lean`); `gabbro_ziel_voll`
    -- the goal under the full summary premise (`BeweisAtomar/Voll.lean`);
  * `zielX_rely` / `zielX_aus` -- every leg of `ZielX` at every machine GX reaches, from the four premise groups
    with the rely (generic in the declaration);
  * `zielFX_aus` -- every leg of `ZielFX` on every thread machine over GX (spawns and joins);
  * `geteiltV_mitRuhe_eq` -- the admitted shared atomics of `P.mitRuhe` are those of `P`;
  * `gabbro_zielX` -- the statement;
  * `geteiltV_leer` / `zielF_of_X` / `gabbroZiel_aus_X` -- THE EMBEDDING: on every unit the
    checker of before accepts there is no admitted shared atomic, GX is G there, and the
    statement of before follows word for word;
  * `akzeptiertSpec_verbindeX`, `gabbro_ziel_verbundX`, `verbund_aus_X` -- the same for linked
    units.
-/
module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Teil1
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Teil2
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Voll
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd
