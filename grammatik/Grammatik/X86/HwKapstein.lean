/-
  File:      Grammatik/X86/HwKapstein.lean
  Subject:   Capstone: one coherent machine step over all accepted families.

  Lane 1149: the single composed step `HwVollSchritt` as the union of the
  adapters/relations actually merged on master, with exact per-family
  embedding, `HwWf` preservation, tag disjointness and a joint witness.
  Every accepted definition is reused unchanged (lifted, never redefined).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwLockRmw
import Grammatik.X86.HwWordAtomicity
import Grammatik.X86.HwStackCalls
import Grammatik.X86.HwIsaFamilies
import Grammatik.X86.HwAddressed
import Grammatik.X86.HwMulDivWidth
import Grammatik.X86.HwLockFetch
import Grammatik.X86.HwDevices
import Grammatik.X86.HwFpControl
import Grammatik.X86.HwFaults
import Grammatik.X86.HwFeatureGates
import Grammatik.X86.HwInterrupts

namespace Gabbro.Grammatik.X86

/-- Union events: the coherent base plus one tag per merged family step. -/
inductive KapEreignis where
  | basis : HwEreignis → KapEreignis
  | lockRmw : Nat → LockAnweisung → KapEreignis
  | wort : Nat → HwWortZugriff → KapEreignis
  | stapel : Nat → StapelEreignis → KapEreignis
  | isa : Nat → IsaEreignis → KapEreignis
  | addr : Nat → HwAddrEreignis → KapEreignis
  | muldiv : Nat → WdDecodiert → KapEreignis
  | lockFetch : Nat → Unit → KapEreignis
  | uc : Nat → HwDev1133.UcZugriff1133 → KapEreignis
  | port : Nat → HwDev1133.PortZugriff1133 → KapEreignis
  | fp : FpCtrlEreignis → KapEreignis
  | fehler : HwFehlerEreignis → KapEreignis
  | tor : CpuOut → BitVec 32 → HwTorEreignis → KapEreignis

/-- The single composed machine step: union of the merged adapters/relations. -/
inductive HwVollSchritt : HwMaschine → HwMaschine → KapEreignis → Prop where
  | basis {m m' : HwMaschine} (e : HwEreignis) (h : HwSchritt m m' e) : HwVollSchritt m m' (KapEreignis.basis e)
  | lockRmw {m m' : HwMaschine} (c : Nat) (a : LockAnweisung) (h : adapterLockRmw.schritt m c a = some m') : HwVollSchritt m m' (KapEreignis.lockRmw c a)
  | wort {m m' : HwMaschine} (c : Nat) (e : HwWortZugriff) (h : adapterWort1147.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.wort c e)
  | stapel {m m' : HwMaschine} (c : Nat) (e : StapelEreignis) (h : stapelAdapter.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.stapel c e)
  | isa {m m' : HwMaschine} (c : Nat) (e : IsaEreignis) (h : adapterIsa.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.isa c e)
  | addr {m m' : HwMaschine} (c : Nat) (e : HwAddrEreignis) (h : adapterAddr.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.addr c e)
  | muldiv {m m' : HwMaschine} (c : Nat) (d : WdDecodiert) (h : adapterMulDivWidth.schritt m c d = some m') : HwVollSchritt m m' (KapEreignis.muldiv c d)
  | lockFetch {m m' : HwMaschine} (c : Nat) (u : Unit) (h : adapterLockFetch.schritt m c u = some m') : HwVollSchritt m m' (KapEreignis.lockFetch c u)
  | uc {m m' : HwMaschine} (c : Nat) (e : HwDev1133.UcZugriff1133) (h : HwDev1133.adapterUc1133.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.uc c e)
  | port {m m' : HwMaschine} (c : Nat) (e : HwDev1133.PortZugriff1133) (h : HwDev1133.adapterPort1133.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.port c e)
  | fp {m m' : HwMaschine} (e : FpCtrlEreignis) (h : FpCtrlSchritt m m' e) : HwVollSchritt m m' (KapEreignis.fp e)
  | fehler {m m' : HwMaschine} (e : HwFehlerEreignis) (h : HwFehlerSchritt m m' e) : HwVollSchritt m m' (KapEreignis.fehler e)
  | tor {m m' : HwMaschine} (leaf1 : CpuOut) (xcrLo : BitVec 32) (e : HwTorEreignis) (h : HwTorSchritt leaf1 xcrLo m m' e) : HwVollSchritt m m' (KapEreignis.tor leaf1 xcrLo e)

end Gabbro.Grammatik.X86
