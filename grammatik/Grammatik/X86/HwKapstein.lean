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

/-! ## 1. Well-formedness: every union step preserves `HwWf`.

  Each arm lifts it own family's accepted preservation lemma; profiles
  are untouched by every arm. The addressed arm needs a two-line joint
  helper since its file states store/load preservation separately. -/

/-- Every addressed adapter step preserves well-formedness. -/
theorem kap_adapterAddr_wf (m m' : HwMaschine) (c : Nat)
    (e : HwAddrEreignis)
    (h : adapterAddr.schritt m c e = some m') (hwf : HwWf m) :
    HwWf m' := by
  cases e with
  | store b f ripNext src len =>
    have h2 : hwAddrStore m c b f ripNext src len = some m' := h
    exact hwAddrStore_wf m m' c b f ripNext src len h2 hwf
  | load b f ripNext dst len =>
    have h2 : hwAddrLoad m c b f ripNext dst len = some m' := h
    exact hwAddrLoad_wf m m' c b f ripNext dst len h2 hwf
  | verweigert =>
    rw [adapterAddr_verweigert] at h
    cases h

/-- Every union step preserves well-formedness. -/
theorem kap_wf (m m' : HwMaschine) (k : KapEreignis)
    (h : HwVollSchritt m m' k) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | basis e hstep => exact hwSchritt_wf m m' e hstep hwf
  | lockRmw c a hstep => exact adapterLockRmw_wf m c a m' hstep hwf
  | wort c e hstep => exact adapterWort1147_wf m m' c e hstep hwf
  | stapel c e hstep => exact stapelAdapter_wf m c e m' hstep hwf
  | isa c e hstep => exact adapterIsa_wf m m' c e hstep hwf
  | addr c e hstep => exact kap_adapterAddr_wf m m' c e hstep hwf
  | muldiv c d hstep => exact adapterMulDivWidth_wf m c d m' hwf hstep
  | lockFetch c u hstep => exact adapterLockFetch_wf m c u m' hstep hwf
  | uc c e hstep => exact HwDev1133.adapterUc1133_wf m m' c e hstep hwf
  | port c e hstep => exact HwDev1133.adapterPort1133_wf m m' c e hstep hwf
  | fp e hstep => exact fpCtrlSchritt_wf m m' e hstep hwf
  | fehler e hstep => exact hwFehlerSchritt_wf m m' e hstep hwf
  | tor leaf1 xcrLo e hstep => exact hwTorSchritt_wf leaf1 xcrLo m m' e hstep hwf

/-! ## 2. Exact embedding: each family step is a union step and back.

  Forward is the constructor; backward inverts it. No new behaviour
  hides behind any tag: the old evaluator rides along unchanged. -/

/-- The coherent base embeds exactly. -/
theorem kap_basis_embedded (m m' : HwMaschine) (e : HwEreignis) :
    HwSchritt m m' e ↔ HwVollSchritt m m' (KapEreignis.basis e) := by
  constructor
  · intro h
    exact .basis e h
  · intro h
    cases h with
    | basis _ hstep => exact hstep

/-- LOCK/RMW embeds exactly. -/
theorem kap_lock_embedded (m m' : HwMaschine) (c : Nat)
    (a : LockAnweisung) :
    adapterLockRmw.schritt m c a = some m' ↔
      HwVollSchritt m m' (KapEreignis.lockRmw c a) := by
  constructor
  · intro h
    exact .lockRmw c a h
  · intro h
    cases h with
    | lockRmw _ _ heq => exact heq

/-- Whole-word access embeds exactly. -/
theorem kap_wort_embedded (m m' : HwMaschine) (c : Nat)
    (e : HwWortZugriff) :
    adapterWort1147.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.wort c e) := by
  constructor
  · intro h
    exact .wort c e h
  · intro h
    cases h with
    | wort _ _ heq => exact heq

/-- Stack/call/return embeds exactly. -/
theorem kap_stapel_embedded (m m' : HwMaschine) (c : Nat)
    (e : StapelEreignis) :
    stapelAdapter.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.stapel c e) := by
  constructor
  · intro h
    exact .stapel c e h
  · intro h
    cases h with
    | stapel _ _ heq => exact heq

/-- The ISA strand embeds exactly. -/
theorem kap_isa_embedded (m m' : HwMaschine) (c : Nat)
    (e : IsaEreignis) :
    adapterIsa.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.isa c e) := by
  constructor
  · intro h
    exact .isa c e h
  · intro h
    cases h with
    | isa _ _ heq => exact heq

/-- Addressed (SIB) access embeds exactly. -/
theorem kap_addr_embedded (m m' : HwMaschine) (c : Nat)
    (e : HwAddrEreignis) :
    adapterAddr.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.addr c e) := by
  constructor
  · intro h
    exact .addr c e h
  · intro h
    cases h with
    | addr _ _ heq => exact heq

/-- Mul/div widths embed exactly. -/
theorem kap_muldiv_embedded (m m' : HwMaschine) (c : Nat)
    (d : WdDecodiert) :
    adapterMulDivWidth.schritt m c d = some m' ↔
      HwVollSchritt m m' (KapEreignis.muldiv c d) := by
  constructor
  · intro h
    exact .muldiv c d h
  · intro h
    cases h with
    | muldiv _ _ heq => exact heq

/-- Fetched LOCK dispatch embeds exactly. -/
theorem kap_lockFetch_embedded (m m' : HwMaschine) (c : Nat) (u : Unit) :
    adapterLockFetch.schritt m c u = some m' ↔
      HwVollSchritt m m' (KapEreignis.lockFetch c u) := by
  constructor
  · intro h
    exact .lockFetch c u h
  · intro h
    cases h with
    | lockFetch _ _ heq => exact heq

/-- Uncached device access embeds exactly. -/
theorem kap_uc_embedded (m m' : HwMaschine) (c : Nat)
    (e : HwDev1133.UcZugriff1133) :
    HwDev1133.adapterUc1133.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.uc c e) := by
  constructor
  · intro h
    exact .uc c e h
  · intro h
    cases h with
    | uc _ _ heq => exact heq

/-- Port access embeds exactly. -/
theorem kap_port_embedded (m m' : HwMaschine) (c : Nat)
    (e : HwDev1133.PortZugriff1133) :
    HwDev1133.adapterPort1133.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.port c e) := by
  constructor
  · intro h
    exact .port c e h
  · intro h
    cases h with
    | port _ _ heq => exact heq

/-- Scalar FP/MXCSR embeds exactly. -/
theorem kap_fp_embedded (m m' : HwMaschine) (e : FpCtrlEreignis) :
    FpCtrlSchritt m m' e ↔ HwVollSchritt m m' (KapEreignis.fp e) := by
  constructor
  · intro h
    exact .fp e h
  · intro h
    cases h with
    | fp _ hstep => exact hstep

/-- Ordered faults embed exactly. -/
theorem kap_fehler_embedded (m m' : HwMaschine) (e : HwFehlerEreignis) :
    HwFehlerSchritt m m' e ↔ HwVollSchritt m m' (KapEreignis.fehler e) := by
  constructor
  · intro h
    exact .fehler e h
  · intro h
    cases h with
    | fehler _ hstep => exact hstep

/-- Feature gates embed exactly. -/
theorem kap_tor_embedded (m m' : HwMaschine) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (e : HwTorEreignis) :
    HwTorSchritt leaf1 xcrLo m m' e ↔
      HwVollSchritt m m' (KapEreignis.tor leaf1 xcrLo e) := by
  constructor
  · intro h
    exact .tor leaf1 xcrLo e h
  · intro h
    cases h with
    | tor _ _ _ hstep => exact hstep

end Gabbro.Grammatik.X86
