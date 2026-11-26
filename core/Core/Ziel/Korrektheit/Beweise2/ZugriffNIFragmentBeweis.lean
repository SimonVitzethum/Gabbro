/-
  THE ACCESS-FRAGMENT NONINTERFERENCE LEG, UNCONDITIONAL. The pinned family packet
  `Beobachtung.zugriffNI` is proved from the run-level access coupling with the proved
  step-existence and graph-coupling premises; `zugriffNIFragmentAusFamilie` then discharges
  the access-fragment leg with that packet.
-/
module

public import Core.Ziel.Korrektheit.Beweise2.ZugriffNIFragment
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert
public import Core.Beobachtung.Fluss.Beweise.ZugriffNI

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

/-- The pinned access-fragment NI leg, with no remaining hypothesis. -/
theorem zugriffNIFragment : ZugriffNIFragmentAussage :=
  zugriffNIFragmentAusFamilie Beobachtung.zugriffNI zugriffSchrittExistiert

end Gabbro.Core.Ziel.Korrektheit
