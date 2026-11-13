module
public import Bruecke.Teil.Pflichten
public import Bruecke.Anweisung.Lokal.Umfang
@[expose] public section

/-!
# Partial bridge duties for bodies with local bindings

The carried call-closed set owes binder freshness and Body duties over `zuBodyB`.
Open body, interface and start duties are exactly those of the partial bridge.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Carried functions satisfy the partial shape conditions and have fresh local binders. -/
structure GetragenB (u : UProg) (C : Fin u.fns.length → Prop) : Prop extends Getragen u C where
  frisch : ∀ c, C c → BindFrisch (fnAt u c)

end Gabbro.Bruecke
