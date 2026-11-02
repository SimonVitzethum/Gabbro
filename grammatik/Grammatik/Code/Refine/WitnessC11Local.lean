module

public import Grammatik.Code.Refine.WitnessC11Embedding

@[expose] public section

namespace Gabbro.Code.Lower.WitC11

open Gabbro.Grammatik
open Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik.Einbettung

/-- A table-bearing invariant is local because its Boolean is constant. -/
def fixtureSperr : SperrInv Wit.wD := ⟨fun _ => [.inl ()], fun _ _ => true⟩

def fixtureAx : AxEns Wit.wD := fun a => nomatch a

/-- Locality is transferred on the concrete table and lock. -/
theorem sperrE_lokal_zeuge :
    SperrInvLokal (sperrE Wit.wD Wit.WFn.wipe fixtureAntwortFrei fixtureSperr) :=
  sperrE_lokal Wit.wD Wit.WFn.wipe fixtureAntwortFrei (fun _ _ _ _ => rfl)

/-- The axiom-free fixture retains its explicit locality obligation. -/
theorem axE_lokal_zeuge :
    AxEnsLokal (axE Wit.wD Wit.WFn.wipe fixtureAntwortFrei fixtureAx) :=
  axE_lokal Wit.wD Wit.WFn.wipe fixtureAntwortFrei (fun a => nomatch a)

/-- A live lock survives embedding injectively. -/
theorem resE_inj_zeuge : (Res.held () : Res Wit.wD) = Res.held () :=
  fixtureEmbedding.resE_inj (a := Res.held ()) (b := Res.held ()) rfl

/-- A Boolean payload uses the generic payload-restriction theorem. -/
theorem nrel_valZ_zeuge :
    Nutzlast.restrict fixtureEmbedding.num fixtureEmbedding.tnum
      (fun n value => fixtureRueck.zeiger n value.1 value.2) (some .bool)
      (fixtureEmbedding.valE .bool true) = true :=
  fixtureEmbedding.nrel_valZ fixtureRueck (some .bool) true
    (fixtureEmbedding.valE .bool true) vrel_valE_zeuge

/-- The populated source program satisfies all concrete callback transfer conditions. -/
theorem uebernahmeE_zeuge :
    fixtureEmbedding.Uebernahme fixtureRueck (sigTreu_einE Wit.wD Wit.WFn.wipe)
      Wit.wP fixtureSperr fixtureAx (fun _ => True)
      (programmE Wit.wD Wit.WFn.wipe Wit.wP)
      (sperrE Wit.wD Wit.WFn.wipe fixtureAntwortFrei fixtureSperr)
      (axE Wit.wD Wit.WFn.wipe fixtureAntwortFrei fixtureAx) (fun _ => True) :=
  uebernahmeE Wit.wD Wit.WFn.wipe fixtureAntwortFrei Wit.wP fixtureSperr fixtureAx
    (fun _ => True) (fun _ => True) (fun _ h => h)

end Gabbro.Code.Lower.WitC11
