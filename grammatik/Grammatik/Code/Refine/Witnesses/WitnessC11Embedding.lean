module

public import Grammatik.Code.Refine.Witnesses.WitnessC11Resources
public import Grammatik.Zielsatz.Einbettung.Zeuge

@[expose] public section

namespace Gabbro.Code.Lower.WitC11

open Gabbro.Grammatik
open Gabbro.Grammatik.Einbettung

/-- The populated lowering fixture has no hardware answer carrying pointers. -/
def fixtureAntwortFrei : Einbettung.AntwortFrei Wit.wD where
  regFrei := fun r => nomatch r
  regFreiG := fun r => nomatch r
  atomFrei := fun g => nomatch g
  aergFrei := fun a => nomatch a
  aparamsFrei := fun a => nomatch a
  rtypFrei := fun r => nomatch r

def fixtureEmbedding := einE Wit.wD Wit.WFn.wipe

def fixtureRueck := rueckE Wit.wD Wit.WFn.wipe fixtureAntwortFrei

/-- Adding a real callback preserves the populated fixture's signatures. -/
theorem sigTreu_einE_zeuge : fixtureEmbedding.SigTreu :=
  sigTreu_einE Wit.wD Wit.WFn.wipe

/-- All four fixture bodies extend together with the callback. -/
theorem fort_einE_zeuge :
    fixtureEmbedding.Fortsetzung (sigTreu_einE Wit.wD Wit.WFn.wipe)
      Wit.wP (programmE Wit.wD Wit.WFn.wipe Wit.wP) :=
  fort_einE Wit.wD Wit.WFn.wipe Wit.wP

/-- A true payload inhabits the value relation of the concrete extension. -/
theorem vrel_valE_zeuge :
    fixtureEmbedding.VRel fixtureRueck .bool true (fixtureEmbedding.valE .bool true) :=
  fixtureEmbedding.vrel_valE fixtureRueck .bool true

/-- Restriction relates the concrete extension's true payload to its source. -/
theorem vrel_valZ_zeuge :
    fixtureEmbedding.VRel fixtureRueck .bool (fixtureEmbedding.valZ fixtureRueck .bool true) true :=
  fixtureEmbedding.vrel_valZ fixtureRueck .bool true

/-- The inhabited relation supplies the restriction equality through its generic theorem. -/
theorem valZ_vrel_zeuge :
    fixtureEmbedding.valZ fixtureRueck .bool (fixtureEmbedding.valE .bool true) = true :=
  fixtureEmbedding.valZ_vrel fixtureRueck .bool vrel_valE_zeuge

end Gabbro.Code.Lower.WitC11
