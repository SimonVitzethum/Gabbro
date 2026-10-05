/-
  File:      Grammatik/X86/HwWordAtomicity.lean
  Subject:   Whole-word atomicity of guarded aligned accesses on the
             coherent machine.

  Lane 1147: connects the ACCEPTED `WordAccessGrouping` family
  (`WortGruppe`, `FremdFrei`, `DrainSpur`, grouped read-back and frame)
  to the coherent `HwMaschine`/`HwSchritt` of `HardwareExecution`,
  reusing the accepted definitions unchanged (lifted, never redefined).
  Per-byte drain facts do not give whole-word atomicity: the silicon
  single-copy claim is stated separately (`HwWortAtomAnnahme`) and
  never discharged by proof. What IS proved: guarded end-state whole
  observation and disjoint-frame preservation on the machine, planted
  refusals, and a reached tearing witness outside the guard.
-/
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.TSO.Kern.WordDrainInterleaving
namespace Gabbro.Grammatik.X86

/-- Word-access family events on the coherent machine: a buffered
    eight-byte store issue, or one oldest-entry drain step. Loads gate
    but change no state, so they are no events here. -/
inductive HwWortZugriff where
  | wortAusgabe : Adresse → Wort → HwWortZugriff
  | wortSpuelung : HwWortZugriff
  deriving DecidableEq, Repr

/-- Family adapter: word stores ride the accepted `hwWortAusgabe`
    (eight buffered byte issues, never the SC word effect); drains
    flush the oldest entry into shared memory. `none` = refused. -/
def adapterWort1147 : HwAdapter HwWortZugriff :=
  ⟨fun m c e =>
    match e with
    | .wortAusgabe a v => hwWortAusgabe m c a v
    | .wortSpuelung =>
      match flushKern (tsoAnsicht m) c with
      | none => none
      | some s' => some (setTso m s')⟩

/-! ## 1. Agreement: the adapter runs the accepted evaluator. -/

/-- A word-store event runs exactly `hwWortAusgabe`. -/
theorem adapterWort1147_ausgabe (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) :
    adapterWort1147.schritt m c (.wortAusgabe a v) =
      hwWortAusgabe m c a v := rfl

/-- A drain event flushes the oldest entry into shared memory. -/
theorem adapterWort1147_spuelung (m : HwMaschine) (c : Nat) :
    adapterWort1147.schritt m c .wortSpuelung =
      match flushKern (tsoAnsicht m) c with
      | none => none
      | some s' => some (setTso m s') := rfl

/-! ## 2. Well-formedness is preserved. -/

/-- Every successful adapter step preserves `HwWf`: both arms only
    touch memory and buffers (`setTso`), never profiles or core data.
    Both premises are used: `h` pins the successor shape, `hwf` the
    profile side. -/
theorem adapterWort1147_wf (m m' : HwMaschine) (c : Nat)
    (e : HwWortZugriff)
    (h : adapterWort1147.schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases e with
  | wortAusgabe a v =>
    rw [adapterWort1147_ausgabe] at h
    unfold hwWortAusgabe at h
    cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
    | none => rw [h1] at h; cases h
    | some s' => rw [h1] at h; cases h; exact setTso_wf _ s' hwf
  | wortSpuelung =>
    rw [adapterWort1147_spuelung] at h
    cases hf : flushKern (tsoAnsicht m) c with
    | none => rw [hf] at h; cases h
    | some s' => rw [hf] at h; cases h; exact setTso_wf _ s' hwf

/-! ## 3. Exact embedding: adapter drains are machine steps. -/

/-- A successful adapter drain is exactly one `HwSchritt.spüle` step
    with the buffer head as its event: both premises are used (`hfl`
    for the flush equation, the head equation for the event side). -/
theorem adapterWort1147_spuelung_einbettung (m : HwMaschine) (c : Nat)
    (s' : TSOZustand)
    (hfl : flushKern (tsoAnsicht m) c = some s') :
    ∃ e : TSOEintrag, (m.puffer c).head? = some e ∧
      HwSchritt m (setTso m s') (.spülung c e) := by
  match hbuf : m.puffer c with
  | [] =>
    have hempty : (tsoAnsicht m).puffer c = [] := by
      rw [tsoAnsicht_puffer]
      exact hbuf
    have hnone : flushKern (tsoAnsicht m) c = none :=
      flush_leer _ c hempty
    rw [hnone] at hfl
    cases hfl
  | x :: _ =>
    exact ⟨x, rfl, .spüle c x s' hfl (by rw [hbuf]; rfl)⟩

/-! ## 4. Machine wrapper and guarded whole-word observation. -/

/-- Canonical machine over a TSO state: shared memory and buffers from
    the state, witness core data, full silicon with OS vector state. -/
def hwWortM (s : TSOZustand) : HwMaschine :=
  ⟨s.mem, hwWitKern, s.puffer, basisHw, fun _ => basisBereit⟩

/-- The wrapper is transparent: the machine view is the state. -/
theorem hwWortM_ansicht (s : TSOZustand) :
    tsoAnsicht (hwWortM s) = s := by
  cases s with
  | mk mem puffer => rfl

/-- The wrapper is well-formed: full silicon admits every feature. -/
theorem hwWortM_wf (s : TSOZustand) : HwWf (hwWortM s) := by
  intro c f _
  cases f <;> rfl

/-- GUARDED END OBSERVATION on the machine: an exclusion-checked drain
    from the exact eight-entry group installs the whole word unsplit
    in shared canonical memory, so EVERY core -- acting and foreign
    alike, they share the one memory -- observes the whole word.
    Lifts `wort_gruppe_liest_zurueck` unchanged; every premise pins one
    of its premises. -/
theorem hw_wort_gruppe_liest_zurueck (m : HwMaschine)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe (tsoAnsicht m) c a v)
    (hles : lesbar8 (tsoAnsicht m).mem a = true)
    (sN : TSOZustand)
    (hspur : DrainSpur c (tsoAnsicht m) sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    read64 (setTso m sN).mem a = some v := by
  show read64 sN.mem a = some v
  exact wort_gruppe_liest_zurueck (tsoAnsicht m) sN t c a v
    hgrp hles hspur hend hleer hstoer

/-- FOREIGN WHOLE OBSERVATION: the guarded word reads back whole
    through EVERY core's projection -- acting and foreign alike --
    because all projections share the one canonical memory (`d` pins
    the observing core). -/
theorem hw_wort_fremd_beobachtet_ganz (m : HwMaschine)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe (tsoAnsicht m) c a v)
    (hles : lesbar8 (tsoAnsicht m).mem a = true)
    (sN : TSOZustand)
    (hspur : DrainSpur c (tsoAnsicht m) sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (d : Nat) :
    read64 (projZustand (setTso m sN) d).speicher a = some v := by
  rw [projZustand_speicher]
  exact hw_wort_gruppe_liest_zurueck m t c a v
    hgrp hles sN hspur hend hleer hstoer

/-- GUARDED FRAME on the machine: a disjoint word observation survives
    the whole grouped drain, so every foreign core observes its own
    whole word at every visited state -- no mixed word on words outside
    the grouped footprint. Lifts `wort_gruppe_rahmen` unchanged. -/
theorem hw_wort_gruppe_rahmen (m : HwMaschine)
    (t : List TSOZustand) (c : Nat) (a b : Adresse) (v old : Wort)
    (hgrp : WortGruppe (tsoAnsicht m) c a v)
    (hdis : Disjunkt a b)
    (hread : read64 (tsoAnsicht m).mem b = some old)
    (sN : TSOZustand)
    (hspur : DrainSpur c (tsoAnsicht m) sN t) (hend : sN ∈ t)
    (hstoerB : ∀ x ∈ t, FremdFrei x c b) :
    read64 (setTso m sN).mem b = some old := by
  show read64 sN.mem b = some old
  exact wort_gruppe_rahmen (tsoAnsicht m) sN t c a b v old
    hgrp hdis hread hspur hend hstoerB

/-- FOREIGN FRAME OBSERVATION: the disjoint word reads back whole
    through EVERY core's projection after the grouped drain. -/
theorem hw_rahmen_fremd_beobachtet_ganz (m : HwMaschine)
    (t : List TSOZustand) (c : Nat) (a b : Adresse) (v old : Wort)
    (hgrp : WortGruppe (tsoAnsicht m) c a v)
    (hdis : Disjunkt a b)
    (hread : read64 (tsoAnsicht m).mem b = some old)
    (sN : TSOZustand)
    (hspur : DrainSpur c (tsoAnsicht m) sN t) (hend : sN ∈ t)
    (hstoerB : ∀ x ∈ t, FremdFrei x c b)
    (d : Nat) :
    read64 (projZustand (setTso m sN) d).speicher b = some old := by
  rw [projZustand_speicher]
  exact hw_wort_gruppe_rahmen m t c a b v old
    hgrp hdis hread sN hspur hend hstoerB

/-! ## 5. The hardware atomicity assumption: stated, never discharged. -/

/-- SILICON ASSUMPTION (named, OPEN): no-mixture observation along a
    grouped drain -- every visited state reads either the whole old
    word or the whole new word. This does NOT follow from the accepted
    per-byte lemmas: the byte drain passes through mixed words (see
    `hw_erster_schritt_reisst` below). For ONE silicon access the
    single-copy guarantee is the textbook x86 rule for aligned ordinary
    accesses; it has no corresponding step in `HwSchritt` (word stores
    are eight `issueByte` events, LOCK stays refused), so this file
    never inhabits, assumes-as-premise, or discharges `HwWortAtomar`.
    Silicon provenance was not re-checked against SDM extracts in this
    lane (no extract present in the clone; see CUTS). -/
def HwWortAtomar (a : Adresse) : Prop :=
  ausgerichtet8 a = true →
    ∀ (s2 sN : TSOZustand) (t : List TSOZustand) (c : Nat)
      (v old : Wort),
      WortGruppe s2 c a v →
      read64 s2.mem a = some old →
      DrainSpur c s2 sN t →
      read64 sN.mem a = some v →
      ∀ x ∈ t, read64 x.mem a = some old ∨ read64 x.mem a = some v

/-- No single-copy bridge is proved here: the type of such a claim is
    empty. The target-side bridge owns it. -/
inductive HwWortBruecke : Prop

/-- Every single-copy bridge claim is void inside this module. -/
theorem kein_hw_wort_bruecke : ¬ HwWortBruecke := by
  intro h
  cases h

/-! ## 6. Refusals: what is NOT admitted. -/

/-- A drain event on an empty buffer is refused. -/
theorem adapterWort1147_spuelung_verweigert_leer (m : HwMaschine)
    (c : Nat)
    (hleer : (tsoAnsicht m).puffer c = []) :
    adapterWort1147.schritt m c .wortSpuelung = none := by
  rw [adapterWort1147_spuelung, flush_leer _ c hleer]

/-- A partial buffer is no group on the machine either: tearing is
    refused structurally. Both premises are used. -/
theorem hw_teilwort_keine_gruppe (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hne : (tsoAnsicht m).puffer c ≠ wortEintraege a v) :
    ¬ WortGruppe (tsoAnsicht m) c a v :=
  hwTeilwort_keine_gruppe _ c a v hne

/-- OVERLAP REFUSED on the machine: the aligned overlapping state
    never groups -- alignment admits what the structural exclusion
    check refuses. -/
theorem hw_overlap_keine_gruppe :
    ¬ WortGruppe (tsoAnsicht (hwWortM wOv)) 0 vA zeugenWort := by
  rw [hwWortM_ansicht]
  exact ausrichtung_allein_verweigert.2

/-- The witness address is aligned: the guard cases below run on an
    aligned word. -/
theorem hw_ausrichtung_vA : ausgerichtet8 vA = true := rfl

/-! ## 7. Tearing: the byte path passes through a mixed word. -/

/-- BYTE-PATH TEARING on the machine: after the first flush of the
    grouped drain, byte 0 is new while byte 1 still reads the old
    byte. Shared memory, so every core observes the mixture. Lifts
    `verflochten_erster_schritt_reisst` unchanged. -/
theorem hw_erster_schritt_reisst :
    (hwWortM wI1).mem.bytes (addrOff vA 0) = wortByte zeugenWort 0 ∧
    (hwWortM wI1).mem.bytes (addrOff vA 1) =
      (hwWortM wI0).mem.bytes (addrOff vA 1) :=
  verflochten_erster_schritt_reisst

/-! ## 8. Joint witness: guarded observation, two cores, forwarding. -/

/-- JOINT WITNESS for `hw_wort_fremd_beobachtet_ganz`: all its premises
    hold jointly on the interleaved machine drain -- core 0 drains the
    exact eight-entry group at aligned `vA` while core 1 issues and
    flushes a disjoint byte between own flushes. Both buffers drain,
    every visited state is foreign-free, the grouped word reads back
    whole through every core projection, both memories observably
    change, and the buffered group byte is visible by forwarding to the
    owner only (core 1 still reads the stale byte). -/
theorem hw_verflochten_zeuge :
    ∃ (m : HwMaschine) (t : List TSOZustand) (sN : TSOZustand),
      WortGruppe (tsoAnsicht m) 0 vA zeugenWort ∧
      lesbar8 (tsoAnsicht m).mem vA = true ∧
      ausgerichtet8 vA = true ∧
      DrainSpur 0 (tsoAnsicht m) sN t ∧ sN ∈ t ∧
      sN.puffer 0 = [] ∧ sN.puffer 1 = [] ∧
      (∀ x ∈ t, FremdFrei x 0 vA) ∧
      TSOErreichbar (tsoAnsicht m) sN ∧
      (∀ d : Nat,
        read64 (projZustand (setTso m sN) d).speicher vA =
          some zeugenWort) ∧
      sN.mem.bytes vB = fByte ∧
      (tsoAnsicht m).mem.bytes vA ≠ sN.mem.bytes vA ∧
      (tsoAnsicht m).mem.bytes vB ≠ sN.mem.bytes vB ∧
      loadByte (tsoAnsicht m) 0 (addrOff vA 0) =
        some (wortByte zeugenWort 0) ∧
      loadByte (tsoAnsicht m) 1 (addrOff vA 0) =
        some ((tsoAnsicht m).mem.bytes (addrOff vA 0)) ∧
      (issueByte wI1 1 vB fByte = some wI2 ∧
        flushKern wI2 1 = some wI3) ∧
      HwWf m := by
  have hg : WortGruppe (tsoAnsicht (hwWortM wI0)) 0 vA zeugenWort := by
    rw [hwWortM_ansicht]
    exact wI_hgrp
  have hl : lesbar8 (tsoAnsicht (hwWortM wI0)).mem vA = true := by
    rw [hwWortM_ansicht]
    exact wI_hles
  have hs : DrainSpur 0 (tsoAnsicht (hwWortM wI0)) wI10 wI_trace := by
    rw [hwWortM_ansicht]
    exact wI_spur
  have herr : TSOErreichbar (tsoAnsicht (hwWortM wI0)) wI10 := by
    rw [hwWortM_ansicht]
    exact wI_erreichbar
  have hbeob : ∀ d : Nat,
      read64 (projZustand (setTso (hwWortM wI0) wI10) d).speicher vA =
        some zeugenWort :=
    hw_wort_fremd_beobachtet_ganz (hwWortM wI0) wI_trace 0 vA zeugenWort
      hg hl wI10 hs wI_hend wI_hempty wI_hstoer
  have hchgA : (tsoAnsicht (hwWortM wI0)).mem.bytes vA ≠
      wI10.mem.bytes vA := by
    rw [hwWortM_ansicht]
    exact wI_grp_aendert
  have hchgB : (tsoAnsicht (hwWortM wI0)).mem.bytes vB ≠
      wI10.mem.bytes vB := by
    rw [hwWortM_ansicht]
    exact wI_fremd_aendert
  have hfwd0 : loadByte (tsoAnsicht (hwWortM wI0)) 0 (addrOff vA 0) =
      some (wortByte zeugenWort 0) := by
    rw [hwWortM_ansicht]
    rfl
  have hfwd1 : loadByte (tsoAnsicht (hwWortM wI0)) 1 (addrOff vA 0) =
      some ((tsoAnsicht (hwWortM wI0)).mem.bytes (addrOff vA 0)) := by
    rw [hwWortM_ansicht]
    rfl
  exact ⟨hwWortM wI0, wI_trace, wI10, hg, hl, hw_ausrichtung_vA,
    hs, wI_hend, wI_hempty, wI_hemptyF, wI_hstoer, herr, hbeob,
    wI_fremd_byte, hchgA, hchgB, hfwd0, hfwd1,
    ⟨wI_issue, wI_fflush⟩, hwWortM_wf wI0⟩

/-! ## 9. Tearing witness: the mixture is reached outside the guard. -/

/-- TEARING WITNESS: the first drain step is a real machine step that
    installs byte 0 while byte 1 still reads the old byte -- a mixed
    word in shared memory, observed by every core. Per-byte facts do
    not give whole-word atomicity; only the guarded END-state and
    frame observations of §4 survive. -/
theorem hw_riss_zeuge :
    ∃ (m m' : HwMaschine) (e : TSOEintrag),
      HwSchritt m m' (.spülung 0 e) ∧
      m'.mem.bytes (addrOff vA 0) = wortByte zeugenWort 0 ∧
      m'.mem.bytes (addrOff vA 1) = m.mem.bytes (addrOff vA 1) ∧
      m.mem.bytes (addrOff vA 0) ≠ m'.mem.bytes (addrOff vA 0) ∧
      HwWf m ∧ HwWf m' := by
  have hfl : flushKern (tsoAnsicht (hwWortM wI0)) 0 = some wI1 := by
    rw [hwWortM_ansicht]
    exact wI_e1
  obtain ⟨e, _, hstep⟩ :=
    adapterWort1147_spuelung_einbettung (hwWortM wI0) 0 wI1 hfl
  refine ⟨hwWortM wI0, setTso (hwWortM wI0) wI1, e, hstep, ?_, ?_, ?_,
    hwWortM_wf _, setTso_wf _ _ (hwWortM_wf _)⟩
  · exact hw_erster_schritt_reisst.1
  · exact hw_erster_schritt_reisst.2
  · show wI0.mem.bytes (addrOff vA 0) ≠ wI1.mem.bytes (addrOff vA 0)
    decide

/- CUTS:
    - Proved here: the ACCEPTED `WordAccessGrouping`/`WordDrainInterleaving`
      family lifted unchanged onto the coherent `HwMaschine`. The adapter
      `adapterWort1147` runs exactly `hwWortAusgabe` (§1 agreement) and
      preserves `HwWf` (§2); adapter drains embed exactly as
      `HwSchritt.spüle` steps (§3). Guarded END-state whole observation
      through every core projection (§4: `hw_wort_fremd_beobachtet_ganz`)
      and guarded disjoint-frame observation (§4:
      `hw_rahmen_fremd_beobachtet_ganz`) lift the accepted read-back and
      frame lemmas; coherence across cores is the accepted single shared
      memory, proved in `HardwareExecution` §1, never assumed here.
    - Per-byte facts do NOT give whole-word atomicity: `HwWortAtomar`
      (§5) names the no-mixture claim and is never inhabited, assumed, or
      discharged in this file; `HwWortBruecke` is empty
      (`kein_hw_wort_bruecke`). The byte path really passes through a
      mixed word (§7 `hw_erster_schritt_reisst`, §9 `hw_riss_zeuge`).
    - Refused here (§6): drain on an empty buffer, partial buffers (no
      group), overlapping foreign entries (alignment admits what the
      exclusion check refuses). LOCK RMW stays refused on the machine
      (`hwLock_verweigert`, `hwGruppe_schliesst_lock_aus`); no LOCK path
      is claimed or needed.
    - Joint inhabitation (§8 `hw_verflochten_zeuge`): the interleaved
      two-core drain joins every premise of the guarded observation --
      group, readability, alignment, trace, end membership, emptiness of
      both buffers, per-state exclusion, reachability, whole read-back
      through every projection, both memory changes, owner-only
      forwarding, the real foreign issue and flush, and well-formedness.
    - NOT proved here, and not claimed:
      - No silicon correspondence: encodings are the accepted canonical
        subsets with self-consistency only. No SDM extract is present in
        this clone, so the textbook single-copy rule for one aligned
        access (Intel SDM Vol. 3A §8.1.1) is cited as the shape of the
        OPEN assumption, not as checked provenance.
      - No mid-trace atomicity: intermediate drain states hold mixed
        words by construction; grouping is a software observation
        discipline for end states and disjoint frames, not a silicon
        guarantee along the trace.
      - No per-access W/GX simulation and no typed-carrier bridge
        (`kein_hw_wort_bruecke` states the gap); no source, checker,
        contract, entry, ABI, loader, relocation, image-layout, budget,
        timing, fairness, progress or liveness claim; no interrupt,
        device, MMIO or DMA model.
      - Axioms stay within the standard goal set
        (propext, Classical.choice, Quot.sound).
-/

#print axioms adapterWort1147
#print axioms adapterWort1147_ausgabe
#print axioms adapterWort1147_spuelung
#print axioms adapterWort1147_wf
#print axioms adapterWort1147_spuelung_einbettung
#print axioms hwWortM
#print axioms hwWortM_ansicht
#print axioms hwWortM_wf
#print axioms hw_wort_gruppe_liest_zurueck
#print axioms hw_wort_fremd_beobachtet_ganz
#print axioms hw_wort_gruppe_rahmen
#print axioms hw_rahmen_fremd_beobachtet_ganz
#print axioms HwWortAtomar
#print axioms kein_hw_wort_bruecke
#print axioms adapterWort1147_spuelung_verweigert_leer
#print axioms hw_teilwort_keine_gruppe
#print axioms hw_overlap_keine_gruppe
#print axioms hw_ausrichtung_vA
#print axioms hw_erster_schritt_reisst
#print axioms hw_verflochten_zeuge
#print axioms hw_riss_zeuge

end Gabbro.Grammatik.X86
