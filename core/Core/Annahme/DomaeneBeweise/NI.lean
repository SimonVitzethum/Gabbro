/-
  File:      core/Core/Annahme/DomaeneBeweise/NI.lean
  Subject:   MK-17 item 2 — the domain noninterference connection `DomaenenNIAussage`
              over elaborated units. An accepted elaborated unit is noninterferent by the
              pinned NI leg (`niAkzeptiert`), whatever its domain plan; the channel premise
              `KanalTragenNiedrig` records the design intent that cross-domain traffic is
              low-labelled. The earlier partial results (the equivalence with the generic
              accepted-implies-noninterference claim and its missing run-level bridges) are
              removed: NI holds only for elaborated units, where the fragment theorem closes it.
-/
module

public import Core.Annahme.Domaene
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Ziel.Korrektheit

/-- **The domain NI connection over elaborated units**: the accepted elaborated unit is
    noninterferent by the pinned NI leg; the channel premise over the unit's own table
    is carried unused. -/
theorem domaenenNI_elaboriert (P : Katalog.Plattform) : DomaenenNIAussage P := by
  intro t hakk _
  exact niAkzeptiert P t hakk

end Gabbro.Core.Annahme
