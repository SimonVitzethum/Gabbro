/-
  File:      Grammatik/Zielsatz/Atomar/GabbroZielFremd.lean
  Subject:   THE GOAL WITH THE FOREIGN PREMISE SPLIT (C08) -- premise (c) narrowed to the
             named hardware, the software part of the foreign ensures moved into (b).

  `GabbroZiel` takes `HardwareAnnahmen O E.Q` as (c); its third conjunct, `AxVertragO`, says
  every answer of every foreign item meets the declared ensures. Since C08 an item declares
  its provenance (`Deklaration.axHerkunft`): an OS service, provider or syscall binding is
  SOFTWARE -- its implementation proves the ensures, it is user logic about the actual binding
  `O`, not an assumption about the machine. `GabbroZielFremd` states the goal with the two
  parts apart:

    (b)  `NutzerPflichtA E` and `AxVertragOSw E.Q O`  -- the user's logic, and the software
         items' ensures against the actual binding `O`;
    (c') `HardwareAnnahmenHw O E.Q`                   -- only the named hardware: frame,
         register locality, the ensures of the items not declared software.

  Nothing is weakened and nothing is claimed more: the narrowed (c') together with the software
  duty IS the old (c) (`hardwareAnnahmen_of_split`), so `gabbro_ziel_fremd` is the proved
  statement of before with the premise provenance corrected. A unit with no software item has
  `AxVertragOSw` for free (`axVertragOSw_ohne`) and (c') is (c) word for word. The conditional,
  call-site form of the software duty (the contract's pre proved at each call) replaces the
  unconditional premise in the replay proofs together with `CallSitePflicht`.
-/
module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Grammatik.Logik.Ruf.FremdRuf.T8

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

/-- **GABBRO_ZIEL with the foreign premise split** (C08): the software items' ensures is part of
    the user's side (b), about the actual binding `O`; the hardware premise (c') names only the
    hardware. -/
def GabbroZielFremd : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, AxVertragOSw E.Q O →                        -- (b) the software items' ensures
    HardwareAnnahmenHw O E.Q →                                  -- (c') the named hardware only
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K

/-- **The goal with the foreign premise split, PROVED**: from `gabbro_ziel` by recombining the
    software and hardware parts of the foreign ensures. -/
theorem gabbro_ziel_fremd : GabbroZielFremd := by
  intro C D _ E fs ls cs hC hN O hSw hHw passes sp init hL lebt0 K hK
  exact gabbro_ziel C D E fs ls cs hC hN O (hardwareAnnahmen_of_split hHw hSw) passes sp init hL
    lebt0 K hK

/-- The statement of before follows: a unit whose items are all software-free needs no software
    duty, and its narrowed hardware premise is the old one. -/
theorem gabbro_ziel_fremd_ohne (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (hfrei : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software)
    (O : Orakel D) (hH : HardwareAnnahmenHw O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (FadenStart E.P.mitRuhe sp init lebt0) K) :
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K :=
  gabbro_ziel_fremd C D E fs ls cs hC hN O (axVertragOSw_ohne hfrei) hH passes sp init hL lebt0 K hK

end Gabbro.Grammatik.Zielsatz
