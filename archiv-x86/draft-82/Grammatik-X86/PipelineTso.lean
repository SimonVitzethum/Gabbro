/-
  File:      Grammatik/X86/PipelineTso.lean
  Subject:   Pipeline correctness over the multi-core TSO machine (lane 1169).
  Skeleton: single-core embedding of pipeline states into HwMaschine.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.FenceDrain

namespace Gabbro.Grammatik.X86.PipelineTso

open Gabbro.Grammatik.X86

/-- Embed a pipeline state on core `c`: shared memory, core data, empty buffers. -/
def pipeHw (s : Zustand) (c : Nat) (hw : HwProfil) (ber : Nat → BereitProfil) : HwMaschine :=
  ⟨s.speicher, fun d =>
    if d = c then ⟨s.register, s.flags, s.rip, fun _ => BitVec.ofNat 128 0, kontextReset⟩
    else ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags, BitVec.ofNat 64 0,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩,
    fun _ => [], hw, ber⟩

/-- The embedding starts with empty buffers on every core. -/
theorem pipeHw_puffer_leer (s : Zustand) (c : Nat) (hw : HwProfil)
    (ber : Nat → BereitProfil) (d : Nat) :
    (pipeHw s c hw ber).puffer d = [] := rfl

/-- Empty buffers are foreign-free at every footprint. -/
theorem pipeHw_fremdFrei (s : Zustand) (c : Nat) (hw : HwProfil)
    (ber : Nat → BereitProfil) (a : Adresse) :
    FremdFrei (tsoAnsicht (pipeHw s c hw ber)) c a := by
  intro d hne e hmem
  have hbuf : (tsoAnsicht (pipeHw s c hw ber)).puffer d = [] := rfl
  rw [hbuf] at hmem
  cases hmem

/-- The acting core projects back to the pipeline state. -/
theorem pipeHw_proj (s : Zustand) (c : Nat) (hw : HwProfil)
    (ber : Nat → BereitProfil) :
    projZustand (pipeHw s c hw ber) c = s := by
  unfold pipeHw projZustand
  simp

/-- A successful pilot step with unchanged memory embeds as a machine `reg` step. -/
theorem pipeHw_reg_einbettung (m : HwMaschine) (c : Nat) (d : Decodiert)
    (s' : Zustand)
    (h : schritt d (projZustand m c) = some s')
    (hmem : s'.speicher = m.mem) :
    HwSchritt m (setKernVonFp m c { projFp m c with kern := s' })
      (.regAusf c (.pilot d)) := by
  apply HwSchritt.reg c (.pilot d) { projFp m c with kern := s' }
  · exact hwPilot_weiter m c d (m.bereit c) s' h
  · simpa using hmem

/-- TSO buffering is transparent for the issuing core: its own load forwards. -/
theorem pipeTso_issue_forward (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : issueByte s c a v = some s')
    (hrd : s.mem.lesbar a = true) :
    loadByte s' c a = some v :=
  load_nach_issue s s' c a v h hrd

/-- An issue changes no canonical byte: the store sits in the buffer. -/
theorem pipeTso_issue_still (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : issueByte s c a v = some s') (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x :=
  issue_kein_speicher s s' c a v h x

/-- A machine issue event changes no canonical byte. -/
theorem pipeTso_hw_issue_still (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : HwSchritt m m' (.schreibAusgabe c a v)) (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwGibAus_kein_speicher m m' c a v h x

/-- A word store appends exactly the eight canonical entries. -/
theorem pipeTso_wort_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v :=
  hwWortAusgabe_puffer m c a v m' h

/-- A word store changes no canonical byte. -/
theorem pipeTso_wort_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c a v m' h x

/-- GROUPED READ-BACK on a drain trace: the exclusion-checked drain
    installs the whole word unsplit in canonical memory. -/
theorem pipeTso_gruppe_liest (s2 sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s2 c a v) (hles : lesbar8 s2.mem a = true)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = []) (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    read64 sN.mem a = some v :=
  wort_gruppe_liest_zurueck s2 sN t c a v hgrp hles hspur hend hleer hstoer

/-- Every drained footprint byte holds the word's little-endian byte. -/
theorem pipeTso_drain_bytes (s2 sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s2 c a v)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = []) (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (k : Nat) (hk : k < 8) :
    sN.mem.bytes (addrOff a k) = wortByte v k := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s2.puffer c = (wortEintraege a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k', _hk0, _hk8, _hbufN, hinst⟩ :=
    drain_installiert_aux c a v s2 sN t hspur hstoer 0 (Nat.zero_le 8)
      hbase (fun j hj => absurd hj (by omega)) sN hend
  have hlen0 : (sN.puffer c).length = 0 := by
    rw [hleer]
    rfl
  rw [_hbufN, List.length_drop, wortEintraege_laenge] at hlen0
  have hk_eq : k' = 8 := by omega
  subst hk_eq
  exact hinst k hk

/-- Every SC-stored footprint byte holds the word's little-endian byte. -/
theorem pipeTso_write64_bytes (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write64 m a v = some m') (k : Nat) (hk : k < 8) :
    m'.bytes (addrOff a k) = wortByte v k := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytes m a v (addrOff a k) = wortByte v k
    unfold writeBytes
    exact writeBytesN_hit m a v 8 k (by omega) (by omega)
  · rw [if_neg hc] at hwr
    cases hwr

/-- THE DRAIN EQUALS THE SOURCE STORE: the SC `write64` and the
    exclusion-checked grouped drain agree on the word value and on
    every footprint byte. This is the memory outcome other cores
    observe after the drain. -/
theorem pipeTso_write64_trifft_drain (m m' : Speicher) (a : Adresse)
    (v : Wort) (hwr : write64 m a v = some m')
    (hrd : lesbar8 m a = true)
    (s2 sN : TSOZustand) (t : List TSOZustand) (c : Nat)
    (hgrp : WortGruppe s2 c a v) (hles : lesbar8 s2.mem a = true)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = []) (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    read64 m' a = some v ∧ read64 sN.mem a = some v ∧
      ∀ k : Nat, k < 8 →
        m'.bytes (addrOff a k) = sN.mem.bytes (addrOff a k) := by
  refine ⟨read64_nach_write64 m m' a v hwr hrd,
    wort_gruppe_liest_zurueck s2 sN t c a v hgrp hles hspur hend hleer hstoer,
    fun k hk => ?_⟩
  rw [pipeTso_write64_bytes m m' a v hwr k hk,
    pipeTso_drain_bytes s2 sN t c a v hgrp hspur hend hleer hstoer k hk]

/-- REFUSAL: every LOCK request refuses (shared atomics out of scope). -/
theorem pipeTso_refuses_lock (m : HwMaschine) (c : Nat)
    (b : SperrBefehl) :
    hwLockAnfrage m c b = none :=
  hwLock_verweigert m c b

/-- REFUSAL: a partial buffer is no word group (tearing refused). -/
theorem pipeTso_refuses_tear (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hne : s.puffer c ≠ wortEintraege a v) :
    ¬ WortGruppe s c a v :=
  hwTeilwort_keine_gruppe s c a v hne

/-- REFUSAL: a foreign footprint entry refuses the group. -/
theorem pipeTso_refuses_foreign (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (d : Nat) (hne : d ≠ c)
    (e : TSOEintrag) (hmem : e ∈ s.puffer d)
    (hfuss : e.addr ∈ Fuss a) :
    ¬ WortGruppe s c a v :=
  hwGruppe_verweigert_bei_fremdeintrag s c a v d hne e hmem hfuss

/-- REFUSAL: LOCK has no TSO step (shared atomics out of scope). -/
theorem pipeTso_refuses_atomic_step (s s' : TSOZustand) :
    ¬ LockSchritt s s' :=
  kein_lock_schritt s s'

/-- Poison probe: a concrete LOCK request refuses. -/
theorem pipeTso_probe_lock :
    hwLockAnfrage hwWitStart 0 (.xadd64 hwWitAdr 7) = none := rfl

/-- Poison probe: two of eight bytes are no word (tearing). -/
theorem pipeTso_probe_tear :
    ¬ WortGruppe ⟨hwWitMem, fun d =>
      if d = 0 then (wortEintraege hwWitAdr hwWitWort).take 2 else []⟩
      0 hwWitAdr hwWitWort := by
  apply hwTeilwort_keine_gruppe
  decide

/-- Poison probe: the overlap state never groups. -/
theorem pipeTso_probe_overlap :
    ¬ WortGruppe hwWitOverlap 0 hwWitAdr hwWitWort :=
  hwWitOverlap_keine_gruppe

/-- WITNESS (non-degenerate, memory-changing): the joint two-core run
    forwards the buffered byte on the acting core, hides it from the
    other core, then drains 0 to 42 in actual shared memory, observed
    from both cores. -/
theorem pipeTso_zeuge :
    hwWitMem.bytes hwWitAdr = BitVec.ofNat 8 0 ∧
      hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      hwWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) :=
  ⟨hwWit_anfang_null, hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher, hwWit_fremd_neu⟩

/- CUTS:
  Proved here:
  - single-core embedding `pipeHw` of a pipeline `Zustand` into
    `HwMaschine` (shared memory, core data on `c`, empty buffers),
    with round-trip `pipeHw_proj` and empty-buffer foreign freedom
    `pipeHw_fremdFrei` at every footprint;
  - register-path embedding `pipeHw_reg_einbettung`: a successful
    pilot `schritt` that leaves memory alone is a machine `reg` step
    (accepted `hwPilot_weiter` plus the memory-unchanged gate);
  - TSO transparency for the acting core: own-load forwarding
    (`pipeTso_issue_forward` from `load_nach_issue`), issue
    memory-silence (`pipeTso_issue_still`, `pipeTso_hw_issue_still`),
    word-issue shape and silence (`pipeTso_wort_puffer`,
    `pipeTso_wort_still`);
  - drain-equals-source: grouped read-back (`pipeTso_gruppe_liest`
    from `wort_gruppe_liest_zurueck`), per-byte drain and `write64`
    facts (`pipeTso_drain_bytes`, `pipeTso_write64_bytes`), and the
    joint word/byte agreement (`pipeTso_write64_trifft_drain`): the
    SC store and the exclusion-checked grouped drain read back the
    same word and agree on every footprint byte -- the memory outcome
    other cores observe after the drain;
  - refusals: LOCK (`pipeTso_refuses_lock`,
    `pipeTso_refuses_atomic_step`), tearing (`pipeTso_refuses_tear`
    plus decide probe `pipeTso_probe_tear`), foreign footprint
    (`pipeTso_refuses_foreign` plus `pipeTso_probe_overlap`), with a
    concrete LOCK probe (`pipeTso_probe_lock`);
  - non-degenerate memory-changing witness `pipeTso_zeuge` (0 to 42
    in actual shared memory, forwarding plus foreign views).
  NOT proved here, and not claimed:
  - no full `pipeline_correct` lift onto `HwMaschine`: the block
    lowering, validator, optimiser certificates, layout separation
    and loaded-image connection are reused as stated, not re-proved
    under TSO; store instructions must take the issue/drain path,
    never the `reg` gate (memory-changing steps are excluded from
    `pipeHw_reg_einbettung` by the `hmem` premise);
  - no whole-word atomicity beyond grouped drains, no LOCK RMW path,
    no shared-atomic contracts (out of scope, refused);
  - no per-access target-to-W/GX simulation, no fairness, progress,
    timing or budget transfer, no interrupt/device/MMIO model;
  - pilot ISA only, through the accepted `Befehl`/`Codec`/`schritt`
    and TSO byte equations; no hardware correspondence beyond the
    accepted canonical definitions.
-/

#print axioms pipeHw_puffer_leer
#print axioms pipeHw_fremdFrei
#print axioms pipeHw_proj
#print axioms pipeHw_reg_einbettung
#print axioms pipeTso_issue_forward
#print axioms pipeTso_issue_still
#print axioms pipeTso_hw_issue_still
#print axioms pipeTso_wort_puffer
#print axioms pipeTso_wort_still
#print axioms pipeTso_gruppe_liest
#print axioms pipeTso_drain_bytes
#print axioms pipeTso_write64_bytes
#print axioms pipeTso_write64_trifft_drain
#print axioms pipeTso_refuses_lock
#print axioms pipeTso_refuses_tear
#print axioms pipeTso_refuses_foreign
#print axioms pipeTso_refuses_atomic_step
#print axioms pipeTso_probe_lock
#print axioms pipeTso_probe_tear
#print axioms pipeTso_probe_overlap
#print axioms pipeTso_zeuge

end Gabbro.Grammatik.X86.PipelineTso
