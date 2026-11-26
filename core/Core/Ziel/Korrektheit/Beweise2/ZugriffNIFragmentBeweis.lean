/-
  THE ACCESS-FRAGMENT NONINTERFERENCE LEG, UNCONDITIONAL. Both premises of
  `zugriffNIFragmentAusTeilen` are proved: the step existence of every access form
  (`zugriffSchrittExistiert`, the machine refuses ill-formed forms) and the run-level graph
  coupling (`Beobachtung.speicherGraphKopplung`, from the crash-bounded graph invariant).
-/
module

public import Core.Ziel.Korrektheit.Beweise2.ZugriffFragmentAusTeilen
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert
public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphKopplungBeweis

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

/-- The pinned access-fragment NI leg, with no remaining hypothesis. -/
theorem zugriffNIFragment : ZugriffNIFragmentAussage :=
  zugriffNIFragmentAusTeilen zugriffSchrittExistiert Beobachtung.speicherGraphKopplung

end Gabbro.Core.Ziel.Korrektheit
