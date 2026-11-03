module

public import Grammatik.Code.Refine.Witnesses.WitnessC11
public import Grammatik.Kern.Syntax.Syntax.Teil4
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

public section

namespace Gabbro.Code.Lower.WitC11

open Gabbro.Grammatik

/-- The existing scoped-return fixture supplies exact residual resources. -/
theorem genauVon_zeuge :
    ([] : List (Res Wit.wD)).Perm (vertragVon Wit.wD Wit.WFn.wipe).ende :=
  c11retR.genauVon rfl

/-- Exact resources construct inhabited scoped-return evidence. -/
theorem vonGenau_zeuge :
    ∃ R : RueckRessourcen Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) [], R.scopes = [] :=
  ⟨RueckRessourcen.vonGenau (List.Perm.refl []), rfl⟩

/-- Adding the idle root preserves access to the fixture's four-slot table. -/
theorem darfR_zeuge : darf Wit.wD.mitRuhe () (([] : List (Res Wit.wD)).map resR) :=
  darfR (Wit.wDarf [])

/-- Shifting signature numbers preserves the fixture's self-conformance. -/
theorem sigR_zeuge :
    SigPasst Wit.wD.rang (sigR (Wit.wD.signatur Wit.WFn.wipe))
      (sigR (Wit.wD.signatur Wit.WFn.wipe)) :=
  SigPasst.sigR (SigPasst.refl _ _)

/-- Zero-admitting array syntax survives the idle-root type transport. -/
theorem zeroAdmitting_tyR_zeuge : ZeroAdmitting (tyR (.arr (.int 0 255) 4)) :=
  zeroAdmitting_tyR (.arrZero (.intZero (by decide) (by decide)))

end Gabbro.Code.Lower.WitC11
