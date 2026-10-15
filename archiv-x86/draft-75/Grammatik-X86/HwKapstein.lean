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
import Grammatik.X86.HwVector
import Grammatik.X86.HwSystemForms
import Grammatik.X86.HwNestedInterrupts
import Grammatik.X86.HwDrainGeneric
import Grammatik.X86.HwForwardingGeneric
import Grammatik.X86.HwLoadedImage
import Grammatik.X86.HwBildInstanzen

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
  | vec : HwVecEreignis → KapEreignis
  | drain : Nat → DrainEreignis → KapEreignis
  | fwd : Nat → FwdEreignis → KapEreignis
  | nested : Nat → AsyncEreignis → AsyncEreignis → KapEreignis
  | int : Nat → AsyncEreignis → KapEreignis
  | system : Nat → SysSteuer → SysEreignis → KapEreignis
  | bild : Nat → ExtInstr → KapEreignis
  | instanzen : Nat → ExtInstr → KapEreignis

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
  | vec {m m' : HwMaschine} (e : HwVecEreignis) (h : HwVecSchritt m m' e) : HwVollSchritt m m' (KapEreignis.vec e)
  | drain {m m' : HwMaschine} (c : Nat) (e : DrainEreignis) (h : drainAdapter.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.drain c e)
  | fwd {m m' : HwMaschine} (c : Nat) (e : FwdEreignis) (h : fwdAdapter.schritt m c e = some m') : HwVollSchritt m m' (KapEreignis.fwd c e)
  | nested {m m' : HwMaschine} (c : Nat) (ev1 ev2 : AsyncEreignis) (h : adapterVerschachtelt.schritt m c (ev1, ev2) = some m') : HwVollSchritt m m' (KapEreignis.nested c ev1 ev2)
  | int {m m' : HwMaschine} (c : Nat) (ev : AsyncEreignis) (h : adapterInterrupt1125.schritt m c ev = some m') : HwVollSchritt m m' (KapEreignis.int c ev)
  | system {m m' : HwMaschine} (c : Nat) (st : SysSteuer) (e : SysEreignis) (h : adapterSystem.schritt m c (st, e) = some m') : HwVollSchritt m m' (KapEreignis.system c st e)
  | bild {m m' : HwMaschine} (c : Nat) (i : ExtInstr) (h : adapterBild.schritt m c i = some m') : HwVollSchritt m m' (KapEreignis.bild c i)
  | instanzen {m m' : HwMaschine} (c : Nat) (i : ExtInstr) (h : adapterInstanzen.schritt m c i = some m') : HwVollSchritt m m' (KapEreignis.instanzen c i)

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

/-! ## 1b. Well-formedness helpers for the extended arms.

  Single async delivery, the shared register-path plug behind the
  loaded-image/instance tags, and the system snapshot plug all keep
  profiles untouched; each lifts its accepted preservation shape. -/

/-- Every single async delivery preserves well-formedness. -/
theorem kap_adapterInterrupt_wf (m m' : HwMaschine) (c : Nat)
    (ev : AsyncEreignis)
    (h : adapterInterrupt1125.schritt m c ev = some m') (hwf : HwWf m) :
    HwWf m' := by
  unfold adapterInterrupt1125 at h
  cases hr : asyncSchritt m c ev ev.steuer with
  | none => simp [hr] at h
  | some r =>
    simp [hr] at h
    cases h
    exact asyncSchritt_wf_allgemein m c ev ev.steuer r hr hwf

/-- The shared register-path plug preserves well-formedness: only
    core data moves, profiles are untouched. Behind both the
    loaded-image and the instance tags. -/
theorem kap_adapterInteger666_wf (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : adapterInteger666.schritt m c i = some m') (hwf : HwWf m) :
    HwWf m' := by
  unfold adapterInteger666 at h
  simp only at h
  cases hs : stepExt i (projFp m c) (m.bereit c) with
  | weiter t' =>
    rw [hs] at h
    simp only at h
    cases h
    exact setKernDaten_wf _ _ _ hwf
  | halt =>
    rw [hs] at h
    simp only at h
    cases h
  | verweigert =>
    rw [hs] at h
    simp only at h
    cases h

/-- The system snapshot plug preserves well-formedness: an admitted
    leg installs core data and memory only, both profiles untouched. -/
theorem kap_adapterSystem_wf (m m' : HwMaschine) (c : Nat)
    (st : SysSteuer) (e : SysEreignis)
    (h : adapterSystem.schritt m c (st, e) = some m') (hwf : HwWf m) :
    HwWf m' := by
  unfold adapterSystem at h
  simp only at h
  cases hs : sysSnapSchritt m c st e with
  | ok k' stp mem' =>
    rw [hs] at h
    simp only at h
    cases h
    exact hwf
  | fehler f =>
    rw [hs] at h
    simp only at h
    cases h
  | verweigert =>
    rw [hs] at h
    simp only at h
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
  | vec e hstep => exact hwVecSchritt_wf m m' e hstep hwf
  | drain c e hstep => exact drainAdapter_wf m c e m' hstep hwf
  | fwd c e hstep => exact fwdAdapter_wf m c e m' hstep hwf
  | nested c ev1 ev2 hstep => exact adapterVerschachtelt_wf m c (ev1, ev2) m' hstep hwf
  | int c ev hstep => exact kap_adapterInterrupt_wf m m' c ev hstep hwf
  | system c st e hstep => exact kap_adapterSystem_wf m m' c st e hstep hwf
  | bild c i hstep => exact kap_adapterInteger666_wf m m' c i hstep hwf
  | instanzen c i hstep => exact kap_adapterInteger666_wf m m' c i hstep hwf

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

/-- Packed integer vectors embed exactly. -/
theorem kap_vec_embedded (m m' : HwMaschine) (e : HwVecEreignis) :
    HwVecSchritt m m' e ↔ HwVollSchritt m m' (KapEreignis.vec e) := by
  constructor
  · intro h
    exact .vec e h
  · intro h
    cases h with
    | vec _ hstep => exact hstep

/-- Generic drains embed exactly. -/
theorem kap_drain_embedded (m m' : HwMaschine) (c : Nat)
    (e : DrainEreignis) :
    drainAdapter.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.drain c e) := by
  constructor
  · intro h
    exact .drain c e h
  · intro h
    cases h with
    | drain _ _ heq => exact heq

/-- Generic forwarding embeds exactly. -/
theorem kap_fwd_embedded (m m' : HwMaschine) (c : Nat)
    (e : FwdEreignis) :
    fwdAdapter.schritt m c e = some m' ↔
      HwVollSchritt m m' (KapEreignis.fwd c e) := by
  constructor
  · intro h
    exact .fwd c e h
  · intro h
    cases h with
    | fwd _ _ heq => exact heq

/-- Nested delivery embeds exactly. -/
theorem kap_nested_embedded (m m' : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) :
    adapterVerschachtelt.schritt m c (ev1, ev2) = some m' ↔
      HwVollSchritt m m' (KapEreignis.nested c ev1 ev2) := by
  constructor
  · intro h
    exact .nested c ev1 ev2 h
  · intro h
    cases h with
    | nested _ _ _ heq => exact heq

/-- Single async delivery embeds exactly. -/
theorem kap_int_embedded (m m' : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) :
    adapterInterrupt1125.schritt m c ev = some m' ↔
      HwVollSchritt m m' (KapEreignis.int c ev) := by
  constructor
  · intro h
    exact .int c ev h
  · intro h
    cases h with
    | int _ _ heq => exact heq

/-- System forms embed exactly. -/
theorem kap_system_embedded (m m' : HwMaschine) (c : Nat)
    (st : SysSteuer) (e : SysEreignis) :
    adapterSystem.schritt m c (st, e) = some m' ↔
      HwVollSchritt m m' (KapEreignis.system c st e) := by
  constructor
  · intro h
    exact .system c st e h
  · intro h
    cases h with
    | system _ _ _ heq => exact heq

/-- Loaded-image steps embed exactly (register-path plug). -/
theorem kap_bild_embedded (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr) :
    adapterBild.schritt m c i = some m' ↔
      HwVollSchritt m m' (KapEreignis.bild c i) := by
  constructor
  · intro h
    exact .bild c i h
  · intro h
    cases h with
    | bild _ _ heq => exact heq

/-- Loader instances embed exactly (register-path plug). -/
theorem kap_instanzen_embedded (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr) :
    adapterInstanzen.schritt m c i = some m' ↔
      HwVollSchritt m m' (KapEreignis.instanzen c i) := by
  constructor
  · intro h
    exact .instanzen c i h
  · intro h
    cases h with
    | instanzen _ _ heq => exact heq

/-- Exhibited vector union step: the `paddb` register row on core 0. -/
theorem kap_step_vec :
    HwVollSchritt hvecWitStart hvecWitM1
      (KapEreignis.vec
        (.vecReg 0 basisCpu basisKontrolle hvecWitD1)) :=
  (kap_vec_embedded _ _ _).mp hvecWit_reg_schritt

/-- Exhibited drain union step: the generic word store on core 0. -/
theorem kap_step_drain :
    ∃ m1, HwVollSchritt drainWitM0 m1
      (KapEreignis.drain 0 (.speichere drainWitAdr drainWitWort)) := by
  have hlen := drainWit_puffer8
  cases hP : drainWitPush with
  | none =>
    rw [drainWitBufLen, hP] at hlen
    cases hlen
  | some m1 =>
    have heq : drainAdapter.schritt drainWitM0 0
        (.speichere drainWitAdr drainWitWort) = some m1 := hP
    exact ⟨m1, (kap_drain_embedded _ _ _ _).mp heq⟩

/-- Exhibited forwarding union step: the generic word store on core 0. -/
theorem kap_step_fwd :
    ∃ m1, HwVollSchritt witFwdM0 m1
      (KapEreignis.fwd 0 (.speichere witFwdAdr witFwdWort)) := by
  have hlen := witFwd_puffer8
  cases hP : witFwdPush with
  | none =>
    rw [witFwdBufLen, hP] at hlen
    cases hlen
  | some m1 =>
    have heq : fwdAdapter.schritt witFwdM0 0
        (.speichere witFwdAdr witFwdWort) = some m1 := hP
    exact ⟨m1, (kap_fwd_embedded _ _ _ _).mp heq⟩

/-! ## 3. Refusals and the interrupt boundary.

  DMA, fault-as-state-step, the ISA/addressed refusal events and bare
  LOCK requests admit nothing: each cites its accepted refusal. Async
  interrupt delivery is not a closed `HwMaschine` step (the machine
  stores no IDT/TSS/IF state); its sync side embeds exactly through
  the accepted extended machine. -/

/-- What is NOT admitted stays refused. -/
theorem kap_verweigert :
    (∀ (m : HwMaschine) (c : Nat) (e : HwDev1133.DmaZugriff1133),
      HwDev1133.adapterDma1133.schritt m c e = none) ∧
    (∀ (m : HwMaschine) (c : Nat) (f : PrioritaetsFehler),
      adapterFehler1123.schritt m c f = none) ∧
    (∀ (m : HwMaschine) (c : Nat),
      adapterIsa.schritt m c .verweigert = none) ∧
    (∀ (m : HwMaschine) (c : Nat),
      adapterAddr.schritt m c .verweigert = none) ∧
    (∀ (m : HwMaschine) (c : Nat) (b : SperrBefehl),
      hwLockAnfrage m c b = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m c e
    exact HwDev1133.adapterDma1133_verweigert m c e
  · intro m c f
    exact adapterFehler1123_verweigert m c f
  · intro m c
    exact adapterIsa_verweigert m c
  · intro m c
    exact adapterAddr_verweigert m c
  · intro m c b
    exact hwLock_verweigert m c b

/-- Interrupts: the sync side embeds exactly through the union base.
    Async delivery needs the extended control machine and is no closed
    union step (see CUTS). -/
theorem kap_interrupt_sync (s s' : HwIntMaschine) (e : HwEreignis)
    (h : HwIntSchritt s s' (IntEreignis.syncEv e)) :
    ∃ m', s'.hw = m' ∧ s'.steuer = s.steuer ∧
      HwVollSchritt s.hw m' (KapEreignis.basis e) := by
  obtain ⟨m', hm1, hm2, hstep⟩ := hwIntSchritt_sync_nur s s' e h
  exact ⟨m', hm1, hm2, (kap_basis_embedded s.hw m' e).mp hstep⟩

/-! ## 4. Disjointness: no family shadows another.

  Union tags are pairwise distinct by construction (one number per
  family); on bytes, the width dispatcher defers to the unified chain
  wherever it accepts (the accepted priority lemma, lifted). -/

/-- Union tag: one number per family. -/
def kapTag : KapEreignis → Nat
  | .basis _ => 0
  | .lockRmw _ _ => 1
  | .wort _ _ => 2
  | .stapel _ _ => 3
  | .isa _ _ => 4
  | .addr _ _ => 5
  | .muldiv _ _ => 6
  | .lockFetch _ _ => 7
  | .uc _ _ => 8
  | .port _ _ => 9
  | .fp _ => 10
  | .fehler _ => 11
  | .tor _ _ _ => 12
  | .vec _ => 13
  | .drain _ _ => 14
  | .fwd _ _ => 15
  | .nested _ _ _ => 16
  | .int _ _ => 17
  | .system _ _ _ => 18
  | .bild _ _ => 19
  | .instanzen _ _ => 20

/-- The base tag never coincides with a family tag: no family shadows
    the coherent base, and families are pairwise distinct by the same
    tag argument (see CUTS for the byte-decoder side). -/
theorem kap_tags_disjoint :
    (∀ (e : HwEreignis) (c : Nat) (a : LockAnweisung),
      KapEreignis.basis e ≠ KapEreignis.lockRmw c a) ∧
    (∀ (e : HwEreignis) (c : Nat) (w : HwWortZugriff),
      KapEreignis.basis e ≠ KapEreignis.wort c w) ∧
    (∀ (e : HwEreignis) (c : Nat) (s : StapelEreignis),
      KapEreignis.basis e ≠ KapEreignis.stapel c s) ∧
    (∀ (e : HwEreignis) (c : Nat) (i : IsaEreignis),
      KapEreignis.basis e ≠ KapEreignis.isa c i) ∧
    (∀ (e : HwEreignis) (c : Nat) (a : HwAddrEreignis),
      KapEreignis.basis e ≠ KapEreignis.addr c a) ∧
    (∀ (e : HwEreignis) (c : Nat) (d : WdDecodiert),
      KapEreignis.basis e ≠ KapEreignis.muldiv c d) ∧
    (∀ (e : HwEreignis) (c : Nat) (u : Unit),
      KapEreignis.basis e ≠ KapEreignis.lockFetch c u) ∧
    (∀ (e : HwEreignis) (c : Nat) (u : HwDev1133.UcZugriff1133),
      KapEreignis.basis e ≠ KapEreignis.uc c u) ∧
    (∀ (e : HwEreignis) (c : Nat) (p : HwDev1133.PortZugriff1133),
      KapEreignis.basis e ≠ KapEreignis.port c p) ∧
    (∀ (e : HwEreignis) (f : FpCtrlEreignis),
      KapEreignis.basis e ≠ KapEreignis.fp f) ∧
    (∀ (e : HwEreignis) (f : HwFehlerEreignis),
      KapEreignis.basis e ≠ KapEreignis.fehler f) ∧
    (∀ (e : HwEreignis) (leaf1 : CpuOut) (xcrLo : BitVec 32)
      (t : HwTorEreignis),
      KapEreignis.basis e ≠ KapEreignis.tor leaf1 xcrLo t) ∧
    (∀ (e : HwEreignis) (v : HwVecEreignis),
      KapEreignis.basis e ≠ KapEreignis.vec v) ∧
    (∀ (e : HwEreignis) (c : Nat) (d : DrainEreignis),
      KapEreignis.basis e ≠ KapEreignis.drain c d) ∧
    (∀ (e : HwEreignis) (c : Nat) (f : FwdEreignis),
      KapEreignis.basis e ≠ KapEreignis.fwd c f) ∧
    (∀ (e : HwEreignis) (c : Nat) (ev1 ev2 : AsyncEreignis),
      KapEreignis.basis e ≠ KapEreignis.nested c ev1 ev2) ∧
    (∀ (e : HwEreignis) (c : Nat) (ev : AsyncEreignis),
      KapEreignis.basis e ≠ KapEreignis.int c ev) ∧
    (∀ (e : HwEreignis) (c : Nat) (st : SysSteuer) (s : SysEreignis),
      KapEreignis.basis e ≠ KapEreignis.system c st s) ∧
    (∀ (e : HwEreignis) (c : Nat) (i : ExtInstr),
      KapEreignis.basis e ≠ KapEreignis.bild c i) ∧
    (∀ (e : HwEreignis) (c : Nat) (i : ExtInstr),
      KapEreignis.basis e ≠ KapEreignis.instanzen c i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro e c a h
    cases h
  · intro e c w h
    cases h
  · intro e c s h
    cases h
  · intro e c i h
    cases h
  · intro e c a h
    cases h
  · intro e c d h
    cases h
  · intro e c u h
    cases h
  · intro e c u h
    cases h
  · intro e c p h
    cases h
  · intro e f h
    cases h
  · intro e f h
    cases h
  · intro e leaf1 xcrLo t h
    cases h
  · intro e v h
    cases h
  · intro e c d h
    cases h
  · intro e c f h
    cases h
  · intro e c ev1 ev2 h
    cases h
  · intro e c ev h
    cases h
  · intro e c st s h
    cases h
  · intro e c i h
    cases h
  · intro e c i h
    cases h

/-- Byte-decoder priority, lifted: wherever the unified chain accepts,
    the width dispatcher answers the unified form -- no pilot or
    extension form is shadowed by the width arm. -/
theorem kap_decode_prioritaet (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeMulDivWidth bs = some (.ext i, rest) :=
  decodeMulDivWidth_prefers_ext bs i rest h

/-! ## 5. Joint witness: reached union steps on two cores.

  One exhibited union step per family with a computable adapter (the
  equation is closed and decided or extracted from the family's own
  reached witness), beside the families' joint witnesses. Non-degenerate:
  locked words move 10 to 15, buffered stores forward to the owner only
  and drain into shared memory, all observed from both cores. -/

/-- Exhibited LOCK/RMW union step: core 0 locked-adds 5 to word 10. -/
theorem kap_step_lock :
    ∃ m1, HwVollSchritt hwLockWitStart m1
      (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9)) := by
  cases hN : hwLockWitNach1 with
  | none =>
    have hwort := hwLockWit_nach1_wort
    rw [hN] at hwort
    cases hwort
  | some m1 =>
    have heq : adapterLockRmw.schritt hwLockWitStart 0
        (.ok (.xadd64 .rax .rbp 0) 9) = some m1 := hN
    exact ⟨m1, (kap_lock_embedded _ _ _ _).mp heq⟩

/-- Exhibited stack union step: core 0 buffers word 42 at its slot. -/
theorem kap_step_stapel :
    ∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.stapel 0 (.push stapelWitWort)) := by
  have hlen := stapelWit_puffer8
  cases hP : stapelWitPush with
  | none =>
    rw [stapelWitBufLen, hP] at hlen
    cases hlen
  | some m1 =>
    have heq : stapelAdapter.schritt stapelWitM0 0
        (.push stapelWitWort) = some m1 := hP
    exact ⟨m1, (kap_stapel_embedded _ _ _ _).mp heq⟩

/-- Exhibited word union step: the same buffered word through the
    whole-word adapter at the acting core's slot. -/
theorem kap_step_wort :
    ∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.wort 0
        (.wortAusgabe (stapelSlot stapelWitM0 0) stapelWitWort)) := by
  have hlen := stapelWit_puffer8
  cases hP : stapelWitPush with
  | none =>
    rw [stapelWitBufLen, hP] at hlen
    cases hlen
  | some m1 =>
    have heq : adapterWort1147.schritt stapelWitM0 0
        (.wortAusgabe (stapelSlot stapelWitM0 0) stapelWitWort) =
        some m1 := hP
    exact ⟨m1, (kap_wort_embedded _ _ _ _).mp heq⟩

/-- Exhibited ISA union step: core 0 issues one byte at the stack slot. -/
theorem kap_step_isa :
    ∃ m', HwVollSchritt stapelWitM0 m'
      (KapEreignis.isa 0
        (.gibAus stapelWitSlotAddr (BitVec.ofNat 8 7))) := by
  have hlen : (adapterIsa.schritt stapelWitM0 0
      (.gibAus stapelWitSlotAddr (BitVec.ofNat 8 7))).map
      (fun m => (m.puffer 0).length) = some 1 := by
    decide
  cases hA : adapterIsa.schritt stapelWitM0 0
      (.gibAus stapelWitSlotAddr (BitVec.ofNat 8 7)) with
  | none =>
    rw [hA] at hlen
    cases hlen
  | some m' =>
    exact ⟨m', (kap_isa_embedded _ _ _ _).mp hA⟩

/-- Exhibited FP union step: core 0 issues one byte at the stack slot
    through the shared TSO byte event. -/
theorem kap_step_fp :
    ∃ m', HwVollSchritt stapelWitM0 m'
      (KapEreignis.fp
        (.schreibAusgabe 0 stapelWitSlotAddr (BitVec.ofNat 8 7))) := by
  have hlen : (issueByte (tsoAnsicht stapelWitM0) 0 stapelWitSlotAddr
      (BitVec.ofNat 8 7)).map (fun s => (s.puffer 0).length) =
      some 1 := by
    decide
  cases hI : issueByte (tsoAnsicht stapelWitM0) 0 stapelWitSlotAddr
      (BitVec.ofNat 8 7) with
  | none =>
    rw [hI] at hlen
    cases hlen
  | some s' =>
    exact ⟨setTso stapelWitM0 s',
      .fp _ (FpCtrlSchritt.gibAus 0 _ _ s' hI)⟩

/-- Exhibited base union step: core 0 observes the zeroed slot byte. -/
theorem kap_step_basis :
    HwVollSchritt stapelWitM0 stapelWitM0
      (KapEreignis.basis
        (.leseBeob 0 stapelWitSlotAddr (BitVec.ofNat 8 0))) := by
  have hload : loadByte (tsoAnsicht stapelWitM0) 0 stapelWitSlotAddr =
      some (BitVec.ofNat 8 0) := by
    decide
  exact (kap_basis_embedded _ _ _).mp (HwSchritt.lade 0 _ _ hload)

/-- Exhibited addressed union step: the SIB 32-bit store on core 0. -/
theorem kap_step_addr :
    ∃ m1, HwVollSchritt hwAddrWitM0 m1
      (KapEreignis.addr 0
        (.store .b32 hwAddrWitForm hwAddrWitNext .rax 7)) := by
  have hlen := hwAddrWit_store_buf
  cases hM : hwAddrWitM1 with
  | none =>
    rw [hM] at hlen
    cases hlen
  | some m1 =>
    have heq : adapterAddr.schritt hwAddrWitM0 0
        (.store .b32 hwAddrWitForm hwAddrWitNext .rax 7) = some m1 := hM
    exact ⟨m1, (kap_addr_embedded _ _ _ _).mp heq⟩

/-- Exhibited fault union step: core 1 carries the ordered fetch #PF
    and steps to itself with the fault event. -/
theorem kap_step_fehler :
    HwVollSchritt hwWitStart hwWitStart
      (KapEreignis.fehler (HwFehlerEreignis.fehler 1 ⟨.abruf, .pf⟩)) := by
  exact .fehler _
    (HwFehlerSchritt.fehler 1 hwFehlerZLeer hwFehlerPgDunkel ⟨false⟩
      ⟨fun _ => false⟩ false ⟨.abruf, .pf⟩ hwFehler_wit_wahl)

/-- Exhibited fetched-LOCK union step: the fetch decides, core 0 adds. -/
theorem kap_step_lockFetch :
    ∃ m1, HwVollSchritt hwLockWitStart m1
      (KapEreignis.lockFetch 0 ()) := by
  cases hN : hwLockWitNach1 with
  | none =>
    have hwort := hwLockWit_nach1_wort
    rw [hN] at hwort
    cases hwort
  | some m1 =>
    have hfetch : hwLockFetchSchritt hwLockWitStart 0 = some m1 := by
      rw [hwLockFetchWit_nach1]
      exact hN
    have heq : adapterLockFetch.schritt hwLockWitStart 0 () =
        some m1 := hfetch
    exact ⟨m1, (kap_lockFetch_embedded _ _ _ _).mp heq⟩

/-- Exhibited width union step: core 0 divides 17 by 5 (quotient 3). -/
theorem kap_step_muldiv :
    ∃ m', HwVollSchritt wdHwWitStart m'
      (KapEreignis.muldiv 0 ⟨WdBefehl.divWd .w32 .rcx, 2⟩) := by
  have hdiv := wdHw_div_rax
  cases hS : wdSchritt (⟨WdBefehl.divWd .w32 .rcx, 2⟩ : WdDecodiert)
      (projZustand wdHwWitStart 0) with
  | hardwareHalt =>
    have ho : wdHwOutDiv = .halt :=
      wdHwRegSchritt_halt _ _ _ hS
    rw [ho] at hdiv
    simp [wdHwRegOut] at hdiv
  | misslungen =>
    have ho : wdHwOutDiv = .verweigert :=
      wdHwRegSchritt_verweigert _ _ _ hS
    rw [ho] at hdiv
    simp [wdHwRegOut] at hdiv
  | ok s' =>
    exact ⟨_, (kap_muldiv_embedded _ _ _ _).mp
      (adapterMulDivWidth_ok _ _ _ _ hS)⟩

/-- Exhibited gate union step: the admitted vector step under observed
    SSE2 and OS vector state. -/
theorem kap_step_tor :
    HwVollSchritt hwWitStart (setKernVonFp hwWitStart 0 hwTorWitT')
      (KapEreignis.tor zeugeOut1 (BitVec.ofNat 32 0x6)
        (.ausf 0 (.vec hwTorWitV))) := by
  exact .tor _ _ _
    (HwTorSchritt.ok 0 _ _ hwTor_basis_vec_offen hwTorWit_ext_vec
      hwTorWit_vec_mem)

/-- Exhibited uncached union step: the UC store retires under the
    triple gate, changing nothing on the machine. -/
theorem kap_step_uc :
    HwVollSchritt hwWitStart hwWitStart
      (KapEreignis.uc 0
        (.speichere .b64 HwDev1133.witDev1133 (BitVec.ofNat 64 7)
          HwDev1133.witProfil1133)) := by
  have hz : breiteZugelassen hwWitStart.hw (hwWitStart.bereit 0)
      Breite.b64 = true := by
    decide
  have hu : istUc HwDev1133.witProfil1133 HwDev1133.witDev1133 8 =
      true := by
    decide
  have hf : imFenster HwDev1133.witDev1133 8 = true := by
    decide
  exact (kap_uc_embedded _ _ _ _).mp
    (HwDev1133.ucAdapterSchritt_speichern hwWitStart 0 .b64
      HwDev1133.witDev1133 (BitVec.ofNat 64 7) HwDev1133.witProfil1133
      hz hu hf)

/-! ## 6. Joint witness: every exhibited premise together.

  One reached union step per tag with a computable adapter, the two
  decoder pins (new width row takes the width arm, overlapping rows
  keep the unified arm), the planted refusals, well-formedness, and
  the shared non-degeneracy: locked words move 10 to 15 on two cores,
  buffered stores forward to the owner only, drains change actual
  shared memory observed from both cores. Family-internal joint
  inhabitation stays in each family's own `_zeuge`; the port tag is
  embedded by equation only (see CUTS). -/

/-- Joint capstone witness over the coherent machine. -/
theorem kap_zeuge :
    (∃ m1, HwVollSchritt hwLockWitStart m1
      (KapEreignis.lockRmw 0 (.ok (.xadd64 .rax .rbp 0) 9))) ∧
    (∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.stapel 0 (.push stapelWitWort))) ∧
    (∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.wort 0
        (.wortAusgabe (stapelSlot stapelWitM0 0) stapelWitWort))) ∧
    (∃ m', HwVollSchritt stapelWitM0 m'
      (KapEreignis.isa 0
        (.gibAus stapelWitSlotAddr (BitVec.ofNat 8 7)))) ∧
    (∃ m', HwVollSchritt stapelWitM0 m'
      (KapEreignis.fp
        (.schreibAusgabe 0 stapelWitSlotAddr (BitVec.ofNat 8 7)))) ∧
    HwVollSchritt stapelWitM0 stapelWitM0
      (KapEreignis.basis
        (.leseBeob 0 stapelWitSlotAddr (BitVec.ofNat 8 0))) ∧
    (∃ m1, HwVollSchritt hwAddrWitM0 m1
      (KapEreignis.addr 0
        (.store .b32 hwAddrWitForm hwAddrWitNext .rax 7))) ∧
    HwVollSchritt hwWitStart hwWitStart
      (KapEreignis.fehler (HwFehlerEreignis.fehler 1 ⟨.abruf, .pf⟩)) ∧
    (∃ m1, HwVollSchritt hwLockWitStart m1
      (KapEreignis.lockFetch 0 ())) ∧
    (∃ m', HwVollSchritt wdHwWitStart m'
      (KapEreignis.muldiv 0 ⟨WdBefehl.divWd .w32 .rcx, 2⟩)) ∧
    HwVollSchritt hwWitStart (setKernVonFp hwWitStart 0 hwTorWitT')
      (KapEreignis.tor zeugeOut1 (BitVec.ofNat 32 0x6)
        (.ausf 0 (.vec hwTorWitV))) ∧
    HwVollSchritt hwWitStart hwWitStart
      (KapEreignis.uc 0
        (.speichere .b64 HwDev1133.witDev1133 (BitVec.ofNat 64 7)
          HwDev1133.witProfil1133)) ∧
    HwVollSchritt hvecWitStart hvecWitM1
      (KapEreignis.vec
        (.vecReg 0 basisCpu basisKontrolle hvecWitD1)) ∧
    (∃ m1, HwVollSchritt drainWitM0 m1
      (KapEreignis.drain 0 (.speichere drainWitAdr drainWitWort))) ∧
    (∃ m1, HwVollSchritt witFwdM0 m1
      (KapEreignis.fwd 0 (.speichere witFwdAdr witFwdWort))) ∧
    decodeMulDivWidth [natByte 247, natByte 225] =
      some (.wd (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ :
        WdDecodiert), []) ∧
    decodeMulDivWidth [natByte 73, natByte 247, natByte 224] =
      some (.ext (.muldiv ⟨.mulRax .r8, 3⟩), []) ∧
    HwDev1133.adapterDma1133.schritt hwWitStart 0
      (HwDev1133.DmaZugriff1133.lese hwWitAdr 8) = none ∧
    adapterFehler1123.schritt hwWitStart 1 ⟨.abruf, .pf⟩ = none ∧
    hwLockSchritt hwLockWitStart 0 (.ud .lockAufRegister 5) = none ∧
    stapelAdapter.schritt stapelWitM0 1
      (.ruf (BitVec.ofNat 64 4101)) = none ∧
    HwWf hwWitStart ∧ HwWf hwLockWitStart ∧ HwWf stapelWitM0 ∧
    read64 hwLockWitStart.mem hwLockWitAdr = some 10 ∧
    hwLockWort hwLockWitAdr hwLockWitNach1 = some 15 ∧
    hwLockSicht hwLockWitNach1 1 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 99)) ∧
    hwLockSicht hwLockWitNach1 0 hwLockWitFremdAdr =
      some (some (BitVec.ofNat 8 0)) ∧
    stapelWitLoadEigen = some (some stapelWitWort) ∧
    stapelWitLoadFremd = some (some stapelWitNull) ∧
    stapelWitNachRead = some (some stapelWitWort) ∧
    hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
    hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
    hwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  refine ⟨kap_step_lock, kap_step_stapel, kap_step_wort, kap_step_isa,
    kap_step_fp, kap_step_basis, kap_step_addr, kap_step_fehler,
    kap_step_lockFetch, kap_step_muldiv, kap_step_tor, kap_step_uc,
    kap_step_vec, kap_step_drain, kap_step_fwd,
    pin_wdHw_wdmul32, pin_wdHw_ext_mul64,
    HwDev1133.adapterDma1133_verweigert _ _ _,
    adapterFehler1123_verweigert _ _ _, hwLockWit_reg_ud,
    stapelWit_ruf_fehlalign_verweigert, hwWitStart_wf,
    hwLockWitStart_wf, stapelWit_wf, hwLockWit_anfang,
    hwLockWit_nach1_wort, hwLockWit_nach1_eigen_sicht,
    hwLockWit_nach1_fremd_sicht, stapelWit_weiterleitung,
    stapelWit_fremd_alt, stapelWit_spuelung_aendert_speicher,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    definition lifted, never redefined):
    - the single composed step `HwVollSchritt` as the union of ALL
      merged `HwMaschine` adapters/relations: basis, lockRmw, wort,
      stapel, isa, addr, muldiv, lockFetch, uc, port, fp, fehler,
      tor, vec, drain, fwd, nested, int, system, bild, instanzen
      (21 tags);
    - exact per-family embedding (21 iffs: each family step is a
      union step and back, no new behaviour behind any tag);
    - `HwWf` preservation by the union (`kap_wf`, via each family's
      accepted lemma plus three small helpers for single delivery,
      the shared register-path plug and the system plug);
    - tag disjointness: the base never coincides with any family tag
      (`kap_tags_disjoint`); byte-decoder priority for the one checked
      overlap, width-vs-unified (`kap_decode_prioritaet` with the
      width-arm-takes-new-row and overlap-keeps-unified-arm pins in
      `kap_zeuge`);
    - refusals stay refused: DMA, fault-as-state-step, the
      ISA/addressed refusal events, bare LOCK (`kap_verweigert`);
    - interrupt sync side embeds through the union base
      (`kap_interrupt_sync`);
    - joint witness `kap_zeuge`: 15 exhibited union steps (lock,
      stapel, wort, isa, fp, basis, addr, fehler, lockFetch, muldiv,
      tor, uc, vec, drain, fwd), decoder pins, refusals,
      well-formedness, and shared non-degeneracy (locked words move
      10 to 15 on two cores, owner-only forwarding, drains change
      actual shared memory observed from both cores).
    NOT proved here, and not claimed:
    - port, nested, int, system, bild, instanzen tags are embedded by
      equation only: their successes are exhibited in their family
      files (port selection, nest run, delivery runs, system run on
      `SysMaschine`, loaded-image byteschritt equalities), not
      re-exhibited as union steps here;
    - async delivery carries its control snapshot in the event; no
      independent control-state model is built here;
    - `HwBildFamilien` (fetch/decoder family lemmas) and
      `HwFeatureStep` (gate refinements of the tor arm) add no byte
      step plug and have no separate tag; cited, not re-stepped;
    - byte-decoder disjointness beyond width-vs-unified stays open
      (LOCK fetch vs unified fetch overlap is family-local); no
      unhandled overlap was found;
    - no hardware correspondence beyond self-consistency (silicon and
      timing assumptions live in the family files, not re-checked
      here); no W/GX bridge; no source, checker, contract, entry,
      ABI, loader, budget or liveness claim.
-/

#print axioms kap_wf
#print axioms kap_basis_embedded
#print axioms kap_lock_embedded
#print axioms kap_wort_embedded
#print axioms kap_stapel_embedded
#print axioms kap_isa_embedded
#print axioms kap_addr_embedded
#print axioms kap_muldiv_embedded
#print axioms kap_lockFetch_embedded
#print axioms kap_uc_embedded
#print axioms kap_port_embedded
#print axioms kap_fp_embedded
#print axioms kap_fehler_embedded
#print axioms kap_tor_embedded
#print axioms kap_vec_embedded
#print axioms kap_drain_embedded
#print axioms kap_fwd_embedded
#print axioms kap_nested_embedded
#print axioms kap_int_embedded
#print axioms kap_system_embedded
#print axioms kap_bild_embedded
#print axioms kap_instanzen_embedded
#print axioms kap_adapterAddr_wf
#print axioms kap_adapterInterrupt_wf
#print axioms kap_adapterInteger666_wf
#print axioms kap_adapterSystem_wf
#print axioms kap_verweigert
#print axioms kap_interrupt_sync
#print axioms kap_tags_disjoint
#print axioms kap_decode_prioritaet
#print axioms kap_step_lock
#print axioms kap_step_stapel
#print axioms kap_step_wort
#print axioms kap_step_isa
#print axioms kap_step_fp
#print axioms kap_step_basis
#print axioms kap_step_addr
#print axioms kap_step_fehler
#print axioms kap_step_lockFetch
#print axioms kap_step_muldiv
#print axioms kap_step_tor
#print axioms kap_step_uc
#print axioms kap_step_vec
#print axioms kap_step_drain
#print axioms kap_step_fwd
#print axioms kap_zeuge

end Gabbro.Grammatik.X86
