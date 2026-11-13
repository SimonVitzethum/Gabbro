/- THE GOAL STATEMENT (C08 R3b, 2026-11-13): `GabbroZiel` with the call-site duties of software
   foreign items as premise (b). It lives beside `Spec.lean` because its premises
   (`CallSitePflicht` over GX runs, `ForeignVertrag`, `PostDeckt`, `HardwareAnnahmenHw`) are stated
   over the machine of the goal, which itself imports `Spec.lean`. The header of `Spec.lean` lists
   every named assumption of this statement. -/
module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.FremdRuf.T10Run

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-- **GABBRO_ZIEL** (since C08 R3b, 2026-11-13: WITH THE CALL-SITE DUTIES). The conclusion is the one
    of `GabbroZielVoll`, over the thread machine over GX with the atomic rely. Premise (c) no longer
    assumes a software foreign item's unconditional summary: its `requires` is owed by the user at
    every call a run reaches (`CallSitePflicht`), its `ensures` is relied on only where that pre held
    -- by the body duties (`NutzerPflichtA`, whose oracle class asks the summary only at question worlds whose pre
    holds) and by the binding's proof (`ForeignVertrag`: under the pre, every answer meets the post;
    every answer decodes), with the post covering the declared summary (`PostDeckt`). Hardware and
    unresolved items keep their unconditional summaries in (c) (`HardwareAnnahmenHw`). Its `GutO`
    component still covers ALL items, including software bindings: frame respect, preservation of
    held locks in every world, and the prescribed trace suffix when the declared write guards are
    held, remain explicit assumptions in (c). These software obligations are not discharged by
    `ForeignVertrag` or `CallSitePflicht`. -/
def GabbroZiel : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the bodies, with the rely
    CallSitePflicht E →                                         -- (b) software pres at every call
    PostDeckt E →                                               -- (b) software posts cover summaries
    ∀ O : Orakel D, ForeignVertrag E O →                        -- (b) the software binding's proof
    HardwareAnnahmenHw O E.Q →                                  -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K

end Gabbro.Grammatik.Zielsatz
