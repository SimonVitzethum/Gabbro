/-
  File:      Grammatik/X86/ComposeFenceOrder.lean
  Subject:   Composition closing: fence placement to per-access concurrent
             equivalence (no fence removed on race-freedom alone).

  Lane 837 (connection wave): composes the already-accepted fence-order legs
  (`FenceDrain.drainVoll`, `MfenceDrainOwn.mfenceDrain`,
  `SfenceStoreNarrow.sfenceOrdnet`, `LfenceLoadNarrow.lfenceSchritt`) into one
  checked closing step over arbitrary admitted drain pairs. No new machine,
  no new decoder row, no second evaluator, no source/checker/goal change.

  Producer/consumer interface closed here:
  - Producer: the three accepted fence legs (drain-own MFENCE, store-only
    SFENCE order, load-only LFENCE step) over the ONE canonical `TSOZustand`.
  - Consumer: per-access concurrent equivalence -- after the composed step the
    acting core observes canonical memory on every readable access, foreign
    buffers stay byte-identical, and no fence is removed on race-freedom
    (address separation) alone.
-/
import Grammatik.X86.MfenceDrainOwn
import Grammatik.X86.SfenceStoreNarrow
import Grammatik.X86.LfenceLoadNarrow

namespace Gabbro.Grammatik.X86

/-- The composed fence-order postcondition: own buffer drained and fence-ready,
    foreign buffers byte-identical, acting core canonically loaded. -/
def fenceOrdnungGeschlossen (s2 s3 : TSOZustand) : Prop :=
  s3.puffer 0 = [] ∧
  zaunBereit s3 0 = true ∧
  s3.puffer 1 = s2.puffer 1

/-! ## 1. Fence-order closing over arbitrary admitted drain pairs. -/

/-- **Fence-order closing.** On any reached state whose own-buffer MFENCE
    drain succeeds with a foreign entry pending, all three accepted fence
    legs hold jointly: the own buffer is drained and fence-ready, the
    foreign buffer stays byte-identical and pending, every later readable
    load on the acting core observes canonical memory, the drained state
    is reached, SFENCE orders exactly store-before-store, LFENCE admits
    the same state without draining and never claims the full barrier --
    while MFENCE refuses that very state, so the fence is not removable
    on race-freedom (address separation) alone. Every premise is used:
    `hdrain` for the drain legs, `hreach` for the reached leg, `hpend`
    for the foreign-pending leg, `hvoll` for the MFENCE-refusal leg. -/
theorem ComposeFenceOrder_verbindung (s2 s3 : TSOZustand)
    (hreach : TSOErreichbar fdStart s2)
    (hdrain : mfenceDrain s2 0 = some s3)
    (hpend : s2.puffer 1 ≠ [])
    (hvoll : s2.puffer 0 ≠ []) :
    s3.puffer 0 = [] ∧
    zaunBereit s3 0 = true ∧
    s3.puffer 1 = s2.puffer 1 ∧
    s3.puffer 1 ≠ [] ∧
    (∀ a : Adresse, s3.mem.lesbar a = true →
      loadByte s3 0 a = some (s3.mem.bytes a)) ∧
    TSOErreichbar fdStart s3 ∧
    sfenceOrdnet .schreibe .schreibe = true ∧
    sfenceOrdnet .lese .lese = false ∧
    (lfenceSchritt s2 0).1.puffer = s2.puffer ∧
    (lfenceSchritt s2 0).1.mem.bytes = s2.mem.bytes ∧
    (lfenceSchritt s2 0).2.istMfence = false ∧
    lockSchritt .mfence 0 s2 = none := by
  have e1 := mfenceDrain_leert s2 s3 0 hdrain
  have e2 := mfenceDrain_bereit s2 s3 0 hdrain
  have e3 := mfenceDrain_fremd s2 s3 0 (d := 1) (by decide) hdrain
  have e4 : s3.puffer 1 ≠ [] := by rw [e3]; exact hpend
  have e6 := mfenceDrain_erreichbar_von fdStart s2 s3 0 hreach hdrain
  have e7 := sfence_ordnet_schreibe
  have e8 := sfence_ordnet_last_nicht.1
  have e9 := mfence_verweigert_bei_vollem_puffer s2 0 hvoll
  refine ⟨e1, e2, e3, e4, ?_, e6, e7, e8, rfl, rfl, rfl, e9⟩
  intro a hrd
  exact mfenceDrain_ordnung s2 s3 0 hdrain a hrd

/-! ## 2. Refusals: no fence removed on race-freedom alone. -/

/-- **PROVED REFUSAL (no removal on race-freedom alone).** The two cores
    buffer disjoint bytes (`fdX ≠ fdY`: no race between the pending
    stores), yet removing core 0's fence observably changes core 1's
    load of `fdX` and canonical memory. Address separation alone does
    not justify fence removal; the drain is load-bearing. -/
theorem ComposeFenceOrder_keinEntfernen_ohne_zaun :
    ∃ (s2 s3 : TSOZustand),
      mfenceDrain s2 0 = some s3 ∧
      s2.puffer 0 ≠ [] ∧ s2.puffer 1 ≠ [] ∧
      fdX ≠ fdY ∧
      loadByte s2 1 fdX ≠ loadByte s3 1 fdX ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX := by
  refine ⟨fdS2, fdS3, ?_, by decide, fd_fremd_wartend.1, by decide, ?_,
    fd_speicher_aendert⟩
  · unfold mfenceDrain
    exact fd_voll_schritt
  · rw [fd_fremd_liest_alt, fd_fremd_liest_neu]
    decide

/-- **Planted byte refusals.** Truncated MFENCE bytes and the
    LFENCE-adjacent shape never run the byte-facing drain step. -/
theorem ComposeFenceOrder_bytes_verweigern :
    mfenceSchrittAusBytes [natByte 15] fdS2 0 = none ∧
    mfenceSchrittAusBytes [natByte 15, natByte 174, natByte 232]
      fdS2 0 = none := by
  refine ⟨?_, ?_⟩
  · simp [mfenceSchrittAusBytes, mfenceAbgeschnitten15_verweigert]
  · simp [mfenceSchrittAusBytes, mfenceNachbarLFENCE_verweigert]

/-! ## 3. Joint witness: all premises together, non-degenerate. -/

/-- Joint witness for `ComposeFenceOrder_verbindung`: all premises hold
    together on the reached two-core run whose local drain observably
    changes canonical memory. Non-degenerate: two issued stores on two
    cores, a memory-changing drain, and the drained state reached. -/
theorem ComposeFenceOrder_verbindung_zeuge :
    ∃ (s2 s3 : TSOZustand),
      TSOErreichbar fdStart s2 ∧
      mfenceDrain s2 0 = some s3 ∧
      s2.puffer 1 ≠ [] ∧
      s2.puffer 0 ≠ [] ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX ∧
      TSOErreichbar fdStart s3 := by
  have hr : TSOErreichbar fdStart fdS2 :=
    .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
      (.issue _ _ _ _ _ fd_schritt2)
  have hd : mfenceDrain fdS2 0 = some fdS3 := by
    unfold mfenceDrain
    exact fd_voll_schritt
  exact ⟨fdS2, fdS3, hr, hd, fd_fremd_wartend.1, by decide,
    fd_speicher_aendert,
    mfenceDrain_erreichbar_von fdStart fdS2 fdS3 0 hr hd⟩

/- CUTS:
    Proved here (all over the REUSED canonical `TSOZustand` and the
    accepted legs `drainVoll`/`mfenceDrain`/`sfenceOrdnet`/`lfenceSchritt`
    with their byte decoders -- no new machine, no new decoder row, no
    second evaluator, no source/checker/goal change):
    - `ComposeFenceOrder_verbindung`: MFENCE drain-own, SFENCE
      store-only order and LFENCE load-only admission hold jointly on
      any admitted reached drain pair with a foreign entry pending;
      MFENCE refuses the same pre-drain state, so the fence is not
      removable on address separation alone.
    - `ComposeFenceOrder_keinEntfernen_ohne_zaun`: disjoint buffered
      bytes, yet fence removal observably changes a foreign load and
      canonical memory (planted refusal of removal-on-race-freedom).
    - `ComposeFenceOrder_bytes_verweigern`: truncated MFENCE bytes and
      the LFENCE-adjacent shape never run the byte-facing drain step.
    - `ComposeFenceOrder_verbindung_zeuge`: joint non-degenerate
      memory-changing reached witness for every premise.
    NOT proved here, and not claimed:
    - No per-access target-to-W/GX simulation: no run induction into W
      runs, no lowering map, no linearisation of G steps. The shared
      TSO-history projection (connection-wave owner 567) and the
      source-world byte representation (owner 570) are the missing
      producer legs; the W store/read bridges (owners 573-574) build on
      them, never on assumptions made here.
    - No source-to-final-loaded-byte closing theorem (`valX86_sound`
      stays OPEN with the validator owner); no silicon correspondence
      beyond the stated canonical bytes; no timing, fairness, progress
      or cycle-cost claim.
    - No SFENCE over weakly-ordered (WC/NT) stores, no LOCK RMW beyond
      the accepted rows, no dispatch-serializing LFENCE variant, no
      fault beyond explicit refusal; foreign/device discharge stays
      refused by the reused legs.
-/

#print axioms fenceOrdnungGeschlossen
#print axioms ComposeFenceOrder_verbindung
#print axioms ComposeFenceOrder_verbindung_zeuge
#print axioms ComposeFenceOrder_keinEntfernen_ohne_zaun
#print axioms ComposeFenceOrder_bytes_verweigern

end Gabbro.Grammatik.X86
