/-
  File:      Grammatik/X86/MfenceDrainOwn.lean
  Subject:   MFENCE drain-own semantics over the canonical TSO target state.

  Lane 780: MFENCE orders prior loads/stores before later ones AND drains
  the OWN store buffer; draining another core's buffer is explicitly NOT
  claimed (no MFENCE-everywhere discharge). Reuses the ONE canonical
  `TSOZustand`/`flushKern`/`loadByte` of `Grammatik.X86.TSO`, the bounded
  local drain `drainVoll`/`drainKernN` of `Grammatik.X86.FenceDrain`, the
  gate `lockSchritt .mfence` of `Grammatik.X86.LockedOps`, and the canonical
  MFENCE bytes/decoder `pinMfence`/`decodeLock` of
  `Grammatik.X86.LockedInstructionExecution`. No second IR, no second
  evaluator, no source/checker/goal change.

  Manual provenance (reused, not re-decided; local snapshot
  `.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US Sep 2026, verified
  2026-10-02): MFENCE Vol. 2B 4-15 -- 0F AE with ModRM reg field 6
  (processor ignores the r/m field), orders loads/stores, needs SSE2
  (CPUID.01H:EDX.SSE2[26]). The drain itself is the TSO flush iteration;
  silicon timing of the drain is NOT modelled.
-/
import Grammatik.X86.FenceDrain
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- MFENCE as drain-then-gate on the acting core: flush the OWN buffer
    fully. The gate (`zaunBereit`) holds afterwards by `drain_voll_bereit`.
    Foreign buffers are untouched by construction (`flushKern` frame). -/
def mfenceDrain (s : TSOZustand) (c : Nat) : Option TSOZustand :=
  drainVoll s c

/-- Byte-facing MFENCE step: only the decoded MFENCE form drains; every
    other decode outcome (LOCK rows, #UD markers, refusal) is `none`.
    Bytes are checked data, never trusted metadata. -/
def mfenceSchrittAusBytes (bs : List Byte) (s : TSOZustand) (c : Nat) :
    Option TSOZustand :=
  match decodeLock bs with
  | some (.ok .mfence _, _) => drainVoll s c
  | _ => none

/-! ## Byte dispatch: only the decoded MFENCE form drains. -/

/-- The canonical MFENCE bytes decode to the fence form (reused pin). -/
theorem mfenceBytes_dekodiert :
    decodeLock pinMfence = some (LockAnweisung.ok .mfence 3, []) :=
  pin_lock_mfence_decodiert

/-- Byte-step equation: decoded MFENCE bytes run the own-buffer drain. -/
theorem mfenceSchrittAusBytes_ok (s s' : TSOZustand) (c : Nat)
    (rest : List Byte)
    (hdec : decodeLock pinMfence = some (LockAnweisung.ok .mfence 3, rest))
    (hdrain : drainVoll s c = some s') :
    mfenceSchrittAusBytes pinMfence s c = some s' := by
  unfold mfenceSchrittAusBytes
  rw [hdec]
  exact hdrain

/-! ## Drain frame: own buffer emptied, fence ready, foreign intact. -/

/-- A successful MFENCE drain leaves the OWN buffer empty. -/
theorem mfenceDrain_leert (s s' : TSOZustand) (c : Nat)
    (h : mfenceDrain s c = some s') :
    s'.puffer c = [] := by
  unfold mfenceDrain at h
  exact drain_voll_leer s s' c h

/-- A successful MFENCE drain makes the local fence ready. -/
theorem mfenceDrain_bereit (s s' : TSOZustand) (c : Nat)
    (h : mfenceDrain s c = some s') :
    zaunBereit s' c = true := by
  unfold mfenceDrain at h
  exact drain_voll_bereit s s' c h

/-- A successful MFENCE drain never changes another core's buffer. -/
theorem mfenceDrain_fremd (s s' : TSOZustand) (c : Nat)
    {d : Nat} (hd : d ≠ c)
    (h : mfenceDrain s c = some s') :
    s'.puffer d = s.puffer d := by
  unfold mfenceDrain at h
  unfold drainVoll at h
  exact drain_fremd_puffer _ s s' c hd h

/-! ## Order: prior stores visible, later loads canonical. -/

/-- After a successful MFENCE drain the acting core forwards nothing:
    every readable load observes canonical memory. Prior stores are
    globally visible before any later load on this core. -/
theorem mfenceDrain_ordnung (s s' : TSOZustand) (c : Nat)
    (h : mfenceDrain s c = some s')
    (a : Adresse) (hrd : s'.mem.lesbar a = true) :
    loadByte s' c a = some (s'.mem.bytes a) := by
  have hempty := mfenceDrain_leert s s' c h
  have hneu : neuestens (s'.puffer c) a = none := by
    simp [hempty, neuestens]
  exact load_ohne_eintrag s' c a hneu hrd

/-- FIFO order under a full MFENCE drain: two buffered stores become
    visible in issue order; the younger never overtakes the older. -/
theorem mfenceDrain_fifo (s s' : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (hbuf : s.puffer c = [⟨a, v⟩, ⟨b, w⟩])
    (hdrain : mfenceDrain s c = some s')
    (hne : a ≠ b) :
    s'.mem.bytes a = v ∧ s'.mem.bytes b = w := by
  unfold mfenceDrain drainVoll at hdrain
  have hlen : (s.puffer c).length = 2 := by
    rw [hbuf]
    rfl
  rw [hlen] at hdrain
  cases hf1 : flushKern s c with
  | none =>
    have hnone : drainKernN s c (1 + 1) = none := by
      simp [drainKernN, hf1]
    rw [show (2 : Nat) = 1 + 1 from rfl] at hdrain
    rw [hnone] at hdrain
    cases hdrain
  | some s1 =>
    have hstep : drainKernN s c (1 + 1) = drainKernN s1 c 1 := by
      simp [drainKernN, hf1]
    rw [show (2 : Nat) = 1 + 1 from rfl, hstep] at hdrain
    have htail : s1.puffer c = [⟨b, w⟩] :=
      flush_entfernt_kopf s s1 c hf1 ⟨a, v⟩ [⟨b, w⟩] hbuf
    cases hf2 : flushKern s1 c with
    | none =>
      have hnone2 : drainKernN s1 c 1 = none := by
        simp [drainKernN, hf2]
      rw [hnone2] at hdrain
      cases hdrain
    | some s2 =>
      have hstep2 : drainKernN s1 c 1 = some s2 := by
        simp [drainKernN, hf2]
      rw [hstep2] at hdrain
      have hss : s2 = s' := by simpa using hdrain
      subst hss
      have e1 := flush_schreibt_kopf s s1 c hf1 ⟨a, v⟩ [⟨b, w⟩] hbuf
      have fr := flush_rahmen s1 s2 c hf2 ⟨b, w⟩ [] htail a hne
      refine ⟨by rw [fr]; exact e1,
        flush_schreibt_kopf s1 s2 c hf2 ⟨b, w⟩ [] htail⟩

/-! ## Drain steps are TSO steps: reached runs extend through MFENCE. -/

/-- A bounded drain extends any reached run, flush by flush. -/
theorem drainKernN_erreichbar_von (s0 s s' : TSOZustand) (c : Nat)
    (hr : TSOErreichbar s0 s)
    (n : Nat) (h : drainKernN s c n = some s') :
    TSOErreichbar s0 s' := by
  have gen : ∀ (k : Nat) (t t' : TSOZustand),
      TSOErreichbar s0 t → drainKernN t c k = some t' →
        TSOErreichbar s0 t' := by
    intro k
    induction k with
    | zero =>
      intro t t' hr0 ht
      simp only [drainKernN] at ht
      cases ht
      exact hr0
    | succ k ih =>
      intro t t' hr0 ht
      simp only [drainKernN] at ht
      cases hf : flushKern t c with
      | none =>
        rw [hf] at ht
        cases ht
      | some t1 =>
        rw [hf] at ht
        simp only at ht
        exact ih t1 t' (.schritt hr0 (.flush _ _ _ hf)) ht
  exact gen n s s' hr h

/-- A successful MFENCE drain extends any reached run. -/
theorem mfenceDrain_erreichbar_von (s0 s s' : TSOZustand) (c : Nat)
    (hr : TSOErreichbar s0 s)
    (h : mfenceDrain s c = some s') :
    TSOErreichbar s0 s' := by
  unfold mfenceDrain drainVoll at h
  exact drainKernN_erreichbar_von s0 s s' c hr _ h

/-! ## Gate versus drain: the gate refuses what the drain flushes. -/

/-- The accepted gate alone refuses a nonempty buffer, while the drain
    succeeds on it and observably changes memory. -/
theorem mfenceDrain_vs_gate :
    lockSchritt .mfence 0 fdS2 = none ∧
      mfenceDrain fdS2 0 = some fdS3 ∧
      fdS2.mem.bytes fdX ≠ fdS3.mem.bytes fdX := by
  refine ⟨rfl, ?_, fd_speicher_aendert⟩
  unfold mfenceDrain
  exact fd_voll_schritt

/-! ## Refusals: no foreign discharge, no neighbour admission. -/

/-- PROVED REFUSAL (no MFENCE-everywhere): a successful own-drain keeps
    every foreign pending entry pending, byte-identical. -/
theorem mfenceDrain_loest_fremd_nicht :
    ∃ (s s' : TSOZustand),
      mfenceDrain s 0 = some s' ∧ s.puffer 1 ≠ [] ∧ s'.puffer 1 ≠ [] ∧
        s'.puffer 1 = s.puffer 1 := by
  refine ⟨fdS2, fdS3, ?_, fd_fremd_wartend.1, fd_fremd_wartend.2,
    fd_fremd_bleibt⟩
  unfold mfenceDrain
  exact fd_voll_schritt

/-- Truncated MFENCE bytes refuse: the lone escape is nothing. -/
theorem mfenceAbgeschnitten15_verweigert :
    decodeLock [natByte 15] = none := by
  decide

/-- Truncated MFENCE bytes refuse: escape plus second byte is nothing. -/
theorem mfenceAbgeschnitten15AE_verweigert :
    decodeLock [natByte 15, natByte 174] = none := by
  decide

/-- The LFENCE-adjacent shape (reg field 5, not 6) is no MFENCE. -/
theorem mfenceNachbarLFENCE_verweigert :
    decodeLock [natByte 15, natByte 174, natByte 232] = none := by
  decide

/-- LOCK before MFENCE parses to the fence #UD marker, never the fence. -/
theorem mfenceMitLock_ist_ud :
    decodeLock [natByte 240, natByte 15, natByte 174, natByte 240] =
      some (LockAnweisung.ud .lockAufZaun 4, []) := by
  decide

/-- The byte step refuses the LFENCE-adjacent shape. -/
theorem mfenceSchrittAusBytes_nachbar_verweigert :
    mfenceSchrittAusBytes [natByte 15, natByte 174, natByte 232]
      fdS2 0 = none := by
  unfold mfenceSchrittAusBytes
  simp [mfenceNachbarLFENCE_verweigert]

/-- The byte step refuses LOCK before MFENCE (parsed #UD never drains). -/
theorem mfenceSchrittAusBytes_lock_verweigert :
    mfenceSchrittAusBytes [natByte 240, natByte 15, natByte 174,
      natByte 240] fdS2 0 = none := by
  unfold mfenceSchrittAusBytes
  simp [mfenceMitLock_ist_ud]

/-! ## Target connection: decoded MFENCE drains the own buffer only. -/

/-- **MFENCE drain-own connection.** Decoded MFENCE bytes run the
    own-buffer drain on a reached state: afterwards the own buffer is
    empty and fence-ready, every foreign buffer is byte-identical (and
    stays pending), later loads on the acting core observe canonical
    memory, and the drained state is reached. Draining another core is
    NOT claimed. -/
theorem MfenceDrainOwn_verbindung (s2 s3 : TSOZustand) (rest : List Byte)
    (hdec : decodeLock pinMfence = some (LockAnweisung.ok .mfence 3, rest))
    (hreach : TSOErreichbar fdStart s2)
    (hdrain : mfenceSchrittAusBytes pinMfence s2 0 = some s3)
    (hpend : s2.puffer 1 ≠ []) :
    s3.puffer 0 = [] ∧ zaunBereit s3 0 = true ∧
      s3.puffer 1 = s2.puffer 1 ∧ s3.puffer 1 ≠ [] ∧
      (∀ a : Adresse, s3.mem.lesbar a = true →
        loadByte s3 0 a = some (s3.mem.bytes a)) ∧
      TSOErreichbar fdStart s3 := by
  have hdrain' : mfenceDrain s2 0 = some s3 := by
    unfold mfenceSchrittAusBytes at hdrain
    rw [hdec] at hdrain
    exact hdrain
  refine ⟨mfenceDrain_leert s2 s3 0 hdrain',
    mfenceDrain_bereit s2 s3 0 hdrain',
    mfenceDrain_fremd s2 s3 0 (d := 1) (by decide) hdrain',
    ?_, ?_,
    mfenceDrain_erreichbar_von fdStart s2 s3 0 hreach hdrain'⟩
  · rw [mfenceDrain_fremd s2 s3 0 (d := 1) (by decide) hdrain']
    exact hpend
  · intro a hrd
    exact mfenceDrain_ordnung s2 s3 0 hdrain' a hrd

/-- Joint witness for `MfenceDrainOwn_verbindung`: all premises together
    on the reached two-core run that observably changes memory. -/
theorem MfenceDrainOwn_verbindung_zeuge :
    ∃ (s2 s3 : TSOZustand) (rest : List Byte),
      decodeLock pinMfence = some (LockAnweisung.ok .mfence 3, rest) ∧
      TSOErreichbar fdStart s2 ∧
      mfenceSchrittAusBytes pinMfence s2 0 = some s3 ∧
      s2.puffer 1 ≠ [] ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX ∧
      s2.puffer 0 ≠ [] := by
  refine ⟨fdS2, fdS3, [], pin_lock_mfence_decodiert, ?_, ?_,
    fd_fremd_wartend.1, fd_speicher_aendert, by decide⟩
  · exact .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
      (.issue _ _ _ _ _ fd_schritt2)
  · exact mfenceSchrittAusBytes_ok fdS2 fdS3 0 []
      pin_lock_mfence_decodiert fd_voll_schritt

/- CUTS:
    Proved here (all over the REUSED canonical `TSOZustand`/`flushKern`/
    `loadByte`, `FenceDrain.drainVoll`, `LockedOps.lockSchritt .mfence`
    and `LockedInstructionExecution.decodeLock`/`pinMfence` -- no new
    machine, no new decoder row, no new instruction, no source claim):
    - MFENCE as drain-then-gate on the acting core (`mfenceDrain` IS
      `drainVoll`): own buffer emptied, fence ready afterwards, foreign
      buffers byte-identical;
    - byte-facing dispatch (`mfenceSchrittAusBytes`): only the decoded
      MFENCE form drains; LOCK rows, #UD markers and refusals are `none`;
    - order: no forwarding after the drain (later loads observe canonical
      memory) plus two-store FIFO visibility in issue order;
    - drain steps ARE TSO steps: reached runs extend through MFENCE;
    - gate versus drain: the accepted gate refuses the nonempty buffer
      that the drain flushes, with an observable memory change;
    - proved refusals: foreign discharge (no MFENCE-everywhere), truncated
      bytes, the LFENCE-adjacent reg-field shape, LOCK before MFENCE;
    - target `MfenceDrainOwn_verbindung` with joint non-degenerate
      memory-changing reached witness `_zeuge`.
    NOT proved here, and not claimed:
    - No foreign drain: `mfenceDrain_loest_fremd_nicht` exhibits the
      surviving foreign entry; no theorem discharges another core.
    - No SFENCE/LFENCE, no LOCK RMW, no widths beyond the TSO bytes.
    - No register/flag/RIP claim at the TSO level: `TSOZustand` carries
      no register file or flags; the fetched level (`lockSchrittVoll`,
      only RIP advances on the admitted empty-buffer fence) is reused,
      not restated.
    - No SSE2/feature-gate restatement: admission lives with the accepted
      `lockSchrittVoll`/`merkmalZugelassen`; the drain step itself is the
      TSO flush iteration.
    - No silicon timing, progress, fairness, cycle bound, interrupts,
      devices, MMIO/DMA, faults beyond explicit refusal.
    - No source/W/GX simulation, no checker/contract/budget/goal change.
-/

#print axioms mfenceDrain
#print axioms mfenceSchrittAusBytes
#print axioms mfenceBytes_dekodiert
#print axioms mfenceSchrittAusBytes_ok
#print axioms mfenceDrain_leert
#print axioms mfenceDrain_bereit
#print axioms mfenceDrain_fremd
#print axioms mfenceDrain_ordnung
#print axioms mfenceDrain_fifo
#print axioms drainKernN_erreichbar_von
#print axioms mfenceDrain_erreichbar_von
#print axioms mfenceDrain_vs_gate
#print axioms mfenceDrain_loest_fremd_nicht
#print axioms mfenceAbgeschnitten15_verweigert
#print axioms mfenceAbgeschnitten15AE_verweigert
#print axioms mfenceNachbarLFENCE_verweigert
#print axioms mfenceMitLock_ist_ud
#print axioms mfenceSchrittAusBytes_nachbar_verweigert
#print axioms mfenceSchrittAusBytes_lock_verweigert
#print axioms MfenceDrainOwn_verbindung
#print axioms MfenceDrainOwn_verbindung_zeuge

end Gabbro.Grammatik.X86
