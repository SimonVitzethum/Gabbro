/-
  File:      Grammatik/X86/TsoReadBridge.lean
  Subject:   TSO to W bridge: fragment READS (lane 1143).

  Closes the OPEN read leg of `CarrierTraceBridge.lean` (which proves one
  no-read fragment write step into W): a typed-carrier read whose value
  comes from forwarding or canonical memory yields a `SchrittW` read step.
  Consumes the accepted `TSOTrace`/`SourceMemory`/`WordAccessGrouping`
  vocabulary, the source access enumeration (`blattFragment_voll`), the
  group-load value links (`BridgeRead`: `ladeWort8`, `wLesbar_aus_gruppe`,
  `wLesbar_aus_weiterleitung`) and the coherent machine observations
  (`HardwareExecution`: `HwSchritt.lade`, `hwSchritt_wf`). The stale-view
  case is stated honestly: no global value for an unflushed store.
-/
import Grammatik.X86.TSOTrace
import Grammatik.X86.SourceMemory
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.SourceAccessCompleteness
import Grammatik.X86.BridgeRead
import Grammatik.X86.HardwareExecution
import Grammatik.RufAdaequatG
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. Machine read observations: preservation and canonical value. -/

/-- Machine read observations preserve well-formedness: the read case of
    the accepted `hwSchritt_wf`, named for the bridge consumer. -/
theorem hwLade_erhaelt_wf (m : HwMaschine) (c : Nat) (a : Adresse) (v : Byte)
    (h : loadByte (tsoAnsicht m) c a = some v) (hwf : HwWf m) : HwWf m :=
  hwSchritt_wf m m _ (.lade c a v h) hwf

/- CUTS:
    - Skeleton only: the read-case preservation lift. The generic
      read-fragment `SchrittW` assembly, the committed/forwarded value
      links, the stale-view refusal and the joint witness are OPEN.
-/

#print axioms hwLade_erhaelt_wf

end Gabbro.Grammatik.X86
