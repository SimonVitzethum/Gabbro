/-
  THE ACCESS-FRAGMENT NONINTERFERENCE LEG, UNCONDITIONAL. The concrete access-form packet
  `Beobachtung.zugriffFormNI` is proved from the run-level coupling with both premises closed;
  the fragment leg consumes that packet and the proved liveness of the memory model.
-/
module

public import Core.Ziel.Korrektheit.Beweise2.ZugriffFragmentAusTeilen
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert
public import Core.Beobachtung.Fluss.Beweise.Zugriff.NI

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

/-- The pinned access-fragment NI leg, with no remaining hypothesis. -/
theorem zugriffNIFragment : ZugriffNIFragmentAussage :=
  zugriffNIFragmentAusTeilen zugriffSchrittExistiert Beobachtung.zugriffFormNI

end Gabbro.Core.Ziel.Korrektheit
