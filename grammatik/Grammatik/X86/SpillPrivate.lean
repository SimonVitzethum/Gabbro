/-
  File:      Grammatik/X86/SpillPrivate.lean
  Subject:   TSO-side private-spill producer half (lane 343, plan B3).

  TSO-side freshness implies per-byte disjointness, which implies
  commutation of a private spill fill/reload with a concurrent disjoint
  access, over the canonical `Speicher`/`TSO`/`Stapel` vocabulary only.
  No second IR, no second evaluator, no SCFG consumer is invented here:
  the SCFG-side application waits for the accepted 287 interface.
  Spills are ordinary permission-checked accesses, never invisible.
  The refusal `Bool` is validator admission, not a hardware fault.
-/
import Grammatik.X86.Stapel
import Grammatik.X86.TSO
import Grammatik.X86.SpeicherKommutation

namespace Gabbro.Grammatik.X86

/-- Spill slot address: the canonical frame slot, no new address model. -/
def spillSlot (r : Rahmen) (idx : Nat) : Adresse := r.schlitzAddr idx

/-- TSO-side freshness: no buffered byte of any core touches the
    eight spill footprint bytes. -/
def SpillFrisch (s : TSOZustand) (r : Rahmen) (idx : Nat) : Prop :=
  ∀ (c : Nat) (e : TSOEintrag), e ∈ s.puffer c →
    ∀ k : Nat, k < 8 → e.addr ≠ addrOff (spillSlot r idx) k

/-- Concurrent separation: the spill slot footprint shares no byte
    with the foreign access footprint. -/
def GetrenntK (r : Rahmen) (idx : Nat) (fremd : Adresse) : Prop :=
  Disjunkt (spillSlot r idx) fremd

/-- Validator admission for a spill slot: refused when the address was
    taken, when the slot is named by an extent, or when it lies outside
    the frame. Plain `Bool`; `false` refuses, it faults no hardware. -/
def spillPrivatOk (adressGenommen perExtentBenannt imRahmen : Bool) : Bool :=
  (!adressGenommen) && (!perExtentBenannt) && imRahmen

/-! ## 1. Validator admission: refusals are `Bool`, not hardware faults -/

/-- An address-taken slot is never admitted, whatever else holds. -/
theorem spillPrivatOk_verweigert_genommen (e imR : Bool) :
    spillPrivatOk true e imR = false := by
  unfold spillPrivatOk
  cases e <;> cases imR <;> rfl

/-- A slot named by an extent is never admitted, whatever else holds. -/
theorem spillPrivatOk_verweigert_extent (g imR : Bool) :
    spillPrivatOk g true imR = false := by
  unfold spillPrivatOk
  cases g <;> cases imR <;> rfl

/-- A slot outside the frame is never admitted. -/
theorem spillPrivatOk_verweigert_aussen (g e : Bool) :
    spillPrivatOk g e false = false := by
  unfold spillPrivatOk
  cases g <;> cases e <;> rfl

/-- Positive probe: a private in-frame slot is admitted. -/
theorem spillPrivatOk_positiv : spillPrivatOk false false true = true := rfl

/-- Joint admission: validator `Bool` with a true in-frame check plus
    TSO-side freshness. Both conjuncts are needed below. -/
def SpillZugelassen (genommen extent : Bool) (s : TSOZustand)
    (r : Rahmen) (idx : Nat) : Prop :=
  spillPrivatOk genommen extent (decide (idx < r.schlitzZahl)) = true ∧
    SpillFrisch s r idx

/-- An address-taken slot is never jointly admitted. -/
theorem spill_zugelassen_verweigert_genommen (extent : Bool)
    (s : TSOZustand) (r : Rahmen) (idx : Nat) :
    ¬ SpillZugelassen true extent s r idx := by
  intro h
  have hok : spillPrivatOk true extent (decide (idx < r.schlitzZahl)) =
      true := h.1
  unfold spillPrivatOk at hok
  cases extent <;> simp at hok

/-- An extent-named slot is never jointly admitted. -/
theorem spill_zugelassen_verweigert_extent (genommen : Bool)
    (s : TSOZustand) (r : Rahmen) (idx : Nat) :
    ¬ SpillZugelassen genommen true s r idx := by
  intro h
  have hok : spillPrivatOk genommen true (decide (idx < r.schlitzZahl)) =
      true := h.1
  unfold spillPrivatOk at hok
  cases genommen <;> simp at hok

/-! ## 2. Spills are ordinary validated accesses, never invisible -/

/-- A spill save IS the permission-checked 64-bit store at the slot
    address: it can be refused, never silently dropped. -/
theorem spill_speichern_ist_write64 (m : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort) :
    sichereWort m r idx v =
      if idx < r.schlitzZahl then write64 m (spillSlot r idx) v else none := by
  unfold sichereWort spillSlot
  rfl

/-- A spill reload IS the permission-checked 64-bit load. -/
theorem spill_laden_ist_read64 (m : Speicher) (r : Rahmen) (idx : Nat) :
    ladeWort m r idx =
      if idx < r.schlitzZahl then read64 m (spillSlot r idx) else none := by
  unfold ladeWort spillSlot
  rfl

/-- An out-of-frame spill slot saves nothing: the refusal is loud. -/
theorem spill_ausserhalb_verweigert (m : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort) (h : r.schlitzZahl ≤ idx) :
    sichereWort m r idx v = none :=
  sichereWort_ausserhalb m r idx v h

/-! ## 3. Freshness gives per-byte disjointness from buffered bytes -/

/-- Freshness unfolded: every buffered byte of every core avoids every
    spill footprint byte. -/
theorem spill_frisch_meidet_puffer (s : TSOZustand) (r : Rahmen)
    (idx : Nat) (hfrisch : SpillFrisch s r idx)
    (c : Nat) (e : TSOEintrag) (hmem : e ∈ s.puffer c)
    (k : Nat) (hk : k < 8) :
    e.addr ≠ addrOff (spillSlot r idx) k :=
  hfrisch c e hmem k hk

/-- Empty buffers are fresh at every slot: the base case every witness
    starts from. -/
theorem spill_frisch_leer (r : Rahmen) (idx : Nat)
    (s : TSOZustand) (hempty : ∀ c, s.puffer c = []) :
    SpillFrisch s r idx := by
  intro c e hmem
  rw [hempty c] at hmem
  cases hmem

/-! ## 4. Disjointness gives commutation of spill fill with foreign stores -/

/-- Witness frame: base `0`, four word slots, so slot 0 sits at
    address `0` and slot 2 at address `16`. -/
def spillRahmenW : Rahmen := { basis := 0, tiefe := 32 }

/-- Slot 0 of the witness frame is address `0`. -/
theorem spillSlot_rW_null : spillSlot spillRahmenW 0 = (0 : Adresse) := by
  decide

/-- Slot 2 of the witness frame is address `16`. -/
theorem spillSlot_rW_sechzehn : spillSlot spillRahmenW 2 = (16 : Adresse) := by
  decide

/-- Witness separation: slot 0 and address `16` share no byte. -/
theorem spill_getrennt_rW : GetrenntK spillRahmenW 0 (16 : Adresse) := by
  unfold GetrenntK
  rw [spillSlot_rW_null]
  exact zweiDisjunkt

/-- A spill fill commutes with a concurrent disjoint store: both orders
    agree on every byte, and neither order widens write permission.
    Every premise is used through `write64_kommutiert`. -/
theorem spill_fill_kommutiert (m m1 m2 m_ab m_ba : Speicher)
    (r : Rahmen) (idx : Nat) (fremd : Adresse) (v w : Wort)
    (hwr1 : write64 m (spillSlot r idx) v = some m1)
    (hwrAB : write64 m1 fremd w = some m_ab)
    (hwr2 : write64 m fremd w = some m2)
    (hwrBA : write64 m2 (spillSlot r idx) v = some m_ba)
    (hdis : GetrenntK r idx fremd) :
    (∀ x, m_ab.bytes x = m_ba.bytes x) ∧
      m_ab.schreibbar = m.schreibbar ∧
      m_ba.schreibbar = m.schreibbar := by
  unfold GetrenntK at hdis
  have h := write64_kommutiert m m1 m2 m_ab m_ba _ _ v w
    hwr1 hwrAB hwr2 hwrBA hdis
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.1⟩

/-- A stable spill footprint survives a disjoint foreign store: the
    reload justification a private slot needs. -/
theorem spill_stabil_bleibt_fremd (m m' : Speicher) (r : Rahmen)
    (idx : Nat) (fremd : Adresse) (w : Wort)
    (snap : Fin 8 → Byte)
    (hwr : write64 m fremd w = some m')
    (hdis : GetrenntK r idx fremd)
    (hstab : StabilFuss m (spillSlot r idx) snap) :
    StabilFuss m' (spillSlot r idx) snap := by
  unfold GetrenntK at hdis
  exact stabilFuss_bleibt m m' fremd _ w snap hwr
    (disjunkt_symm _ _ hdis) hstab

/-- Joint witness for `spill_fill_kommutiert`: all four stores reach in
    both orders at slot 0 vs address `16`, both footprints observably
    change (low bytes `0x00` become `0x08` and `0x18`), and both orders
    agree on every byte. -/
theorem spill_fill_kommutiert_zeuge :
    ∃ (m m1 m2 m_ab m_ba : Speicher) (r : Rahmen) (idx : Nat)
      (fremd : Adresse) (v w : Wort),
      v ≠ w ∧
      write64 m (spillSlot r idx) v = some m1 ∧
      write64 m1 fremd w = some m_ab ∧
      write64 m fremd w = some m2 ∧
      write64 m2 (spillSlot r idx) v = some m_ba ∧
      GetrenntK r idx fremd ∧
      m_ab.bytes (addrOff (spillSlot r idx) 0) ≠
        m.bytes (addrOff (spillSlot r idx) 0) ∧
      m_ab.bytes (addrOff fremd 0) ≠ m.bytes (addrOff fremd 0) ∧
      (∀ x, m_ab.bytes x = m_ba.bytes x) := by
  refine ⟨zweiSpeicher0, zweiNachA, zweiNachB, zweiNachAB, zweiNachBA,
    spillRahmenW, 0, 16, zweiWertV, zweiWertW,
    by decide, ?_, ?_, ?_, ?_, spill_getrennt_rW, ?_, zweiWechseltB, ?_⟩
  · rw [spillSlot_rW_null]
    exact zweiSchrittA
  · exact zweiSchrittAB
  · exact zweiSchrittB
  · rw [spillSlot_rW_null]
    exact zweiSchrittBA
  · rw [spillSlot_rW_null]
    exact zweiWechseltA
  · have h := spill_fill_kommutiert zweiSpeicher0 zweiNachA zweiNachB
      zweiNachAB zweiNachBA spillRahmenW 0 16 zweiWertV zweiWertW
      (by rw [spillSlot_rW_null]; exact zweiSchrittA)
      zweiSchrittAB zweiSchrittB
      (by rw [spillSlot_rW_null]; exact zweiSchrittBA)
      spill_getrennt_rW
    exact h.1

/-! ## 5. TSO-side preservation: freshness and spill bytes survive disjoint accesses -/

/-- A foreign issue outside the spill footprint keeps the slot fresh:
    the issued byte lands in the buffer, canonical spill bytes do not
    move, and no new buffered byte touches the slot. -/
theorem spill_frisch_bleibt_bei_fremd_issue (s s' : TSOZustand) (c : Nat)
    (r : Rahmen) (idx : Nat) (a : Adresse) (v : Byte)
    (h : issueByte s c a v = some s')
    (hfrisch : SpillFrisch s r idx)
    (hmeidet : ∀ k : Nat, k < 8 → a ≠ addrOff (spillSlot r idx) k) :
    SpillFrisch s' r idx := by
  intro d e hmem k hk
  have hbuf : s'.puffer c = s.puffer c ++ [⟨a, v⟩] :=
    issue_haengt_an s s' c a v h
  by_cases hdc : d = c
  · subst hdc
    rw [hbuf, List.mem_append] at hmem
    cases hmem with
    | inl hm => exact hfrisch _ _ hm k hk
    | inr hm =>
      simp at hm
      subst hm
      exact hmeidet k hk
  · have hsame : s'.puffer d = s.puffer d :=
      issue_anderer_kern s s' c a v h hdc
    rw [hsame] at hmem
    exact hfrisch _ _ hmem k hk

/-- A foreign flush leaves every spill footprint byte unchanged, when
    the flushed byte belongs to a footprint the slot is separated from.
    Uses `GetrenntK` through the flushed byte's footprint membership. -/
theorem spill_bleibt_bei_fremd_flush (s s' : TSOZustand) (c : Nat)
    (r : Rahmen) (idx : Nat) (fremd : Adresse)
    (h : flushKern s c = some s')
    (e : TSOEintrag) (rest : List TSOEintrag)
    (he : s.puffer c = e :: rest)
    (hmem : e.addr ∈ Fuss fremd)
    (hgetrennt : GetrenntK r idx fremd) :
    ∀ k : Nat, k < 8 →
      s'.mem.bytes (addrOff (spillSlot r idx) k) =
        s.mem.bytes (addrOff (spillSlot r idx) k) := by
  obtain ⟨j, hj⟩ := (mem_Fuss_iff fremd e.addr).mp hmem
  unfold GetrenntK at hgetrennt
  intro k hk
  have hne : addrOff (spillSlot r idx) k ≠ e.addr := by
    rw [← hj]
    exact hgetrennt k j.val hk j.isLt
  exact flush_rahmen s s' c h e rest he _ hne

/-! ## 6. Reached TSO witness: foreign issue keeps freshness, foreign flush keeps spill bytes -/

/-- Start: zeroed fully-permissive memory, all buffers empty. -/
def spillTSO0 : TSOZustand := ⟨zweiSpeicher0, fun _ => []⟩

/-- After core 1 issues byte `2` at the foreign address `16`. -/
def spillTSO1 : TSOZustand :=
  ⟨zweiSpeicher0, pufferSetze spillTSO0.puffer 1 [⟨(16 : Adresse), 2⟩]⟩

/-- After core 1 flushes its oldest entry into canonical memory. -/
def spillTSO2 : TSOZustand :=
  ⟨{ zweiSpeicher0 with bytes :=
      fun x => if x = (16 : Adresse) then 2 else zweiSpeicher0.bytes x },
    pufferSetze spillTSO1.puffer 1 []⟩

/-- The foreign address avoids every slot-0 footprint byte, through the
    proved `GetrenntK` separation. -/
theorem fremd_meidet_slot0 (k : Nat) (hk : k < 8) :
    (16 : Adresse) ≠ addrOff (spillSlot spillRahmenW 0) k := by
  have h := spill_getrennt_rW k 0 hk (by decide)
  rw [addrOff_null] at h
  exact Ne.symm h

/-- The flushed byte belongs to the foreign footprint. -/
theorem fremd_puffer_mem :
    (⟨(16 : Adresse), 2⟩ : TSOEintrag).addr ∈ Fuss (16 : Adresse) := by
  rw [← leseEreignisse_acht, leseEreignisse_mem]
  exact ⟨0, by decide, addrOff_null _⟩

/-- The foreign issue step computes as claimed. -/
theorem spill_schritt1 :
    issueByte spillTSO0 1 (16 : Adresse) 2 = some spillTSO1 := rfl

/-- The foreign buffer holds exactly the issued entry. -/
theorem spill_puffer1 : spillTSO1.puffer 1 = [⟨(16 : Adresse), 2⟩] := rfl

/-- The foreign flush step computes as claimed. -/
theorem spill_flush_schritt : flushKern spillTSO1 1 = some spillTSO2 := rfl

/-- The foreign flush observably changes its own byte. -/
theorem spill_flush_wechselt :
    spillTSO1.mem.bytes (16 : Adresse) ≠
      spillTSO2.mem.bytes (16 : Adresse) := by
  decide

/-- Freshness at the start: buffers are empty. -/
theorem spill_frisch0 : SpillFrisch spillTSO0 spillRahmenW 0 :=
  spill_frisch_leer _ _ _ (fun _ => rfl)

/-- Freshness survives the disjoint foreign issue. -/
theorem spill_frisch1 : SpillFrisch spillTSO1 spillRahmenW 0 :=
  spill_frisch_bleibt_bei_fremd_issue spillTSO0 spillTSO1 1
    spillRahmenW 0 _ _ spill_schritt1 spill_frisch0 fremd_meidet_slot0

/-- Joint TSO witness: the foreign issue is a reached TSO step that
    keeps the spill slot fresh; the foreign flush keeps every spill
    footprint byte equal to the start while observably changing its own
    byte. Memory changes on the foreign side, never on the spill side. -/
theorem spill_tso_zeuge :
    ∃ (s0 s1 s2 : TSOZustand) (r : Rahmen) (idx : Nat) (fremd : Adresse),
      TSOErreichbar s0 s1 ∧ SpillFrisch s0 r idx ∧ SpillFrisch s1 r idx ∧
      GetrenntK r idx fremd ∧
      flushKern s1 1 = some s2 ∧
      (∀ k : Nat, k < 8 →
        s2.mem.bytes (addrOff (spillSlot r idx) k) =
          s0.mem.bytes (addrOff (spillSlot r idx) k)) ∧
      s1.mem.bytes fremd ≠ s2.mem.bytes fremd := by
  refine ⟨spillTSO0, spillTSO1, spillTSO2, spillRahmenW, 0, 16,
    .schritt .start (.issue _ _ _ _ _ spill_schritt1),
    spill_frisch0, spill_frisch1, spill_getrennt_rW,
    spill_flush_schritt, ?_, spill_flush_wechselt⟩
  intro k hk
  have hflush := spill_bleibt_bei_fremd_flush spillTSO1 spillTSO2 1
    spillRahmenW 0 16 spill_flush_schritt _ [] spill_puffer1
    fremd_puffer_mem spill_getrennt_rW k hk
  have hissue : spillTSO1.mem.bytes (addrOff (spillSlot spillRahmenW 0) k) =
      spillTSO0.mem.bytes (addrOff (spillSlot spillRahmenW 0) k) :=
    issue_kein_speicher spillTSO0 spillTSO1 1 _ _ spill_schritt1 _
  rw [hflush, hissue]

/- CUTS:
    - Done: validator admission (§1) with proved refusals and one positive
      probe; spill visibility (§2); freshness base and unfolding (§3);
      disjointness-to-commutation plus stable-footprint carry (§4) with a
      joint memory-changing witness on both sides; TSO-side preservation
      across foreign issue/flush (§5); reached TSO witness with an
      observably changing foreign byte and untouched spill bytes (§6).
    - OPEN / not claimed: the SCFG-side application waits for the
      accepted 287 interface and is not invented here; no aligned
      multi-byte atomicity beyond byte-extensional commutation; no LOCK
      RMW; no source-to-target simulation (no source carrier is mapped);
      no cost, fairness or timing claim; no new ISA form is added.
    - The refusal `Bool` is validator admission, never a hardware fault.
    - No second IR and no second evaluator: only canonical `Speicher`
      stores/loads, `TSO` issue/flush/load steps and `Stapel` slot
      addresses are reused.
-/

#print axioms spillSlot
#print axioms spillPrivatOk
#print axioms spillPrivatOk_verweigert_genommen
#print axioms spillPrivatOk_verweigert_extent
#print axioms spillPrivatOk_verweigert_aussen
#print axioms spillPrivatOk_positiv
#print axioms SpillZugelassen
#print axioms spill_zugelassen_verweigert_genommen
#print axioms spill_zugelassen_verweigert_extent
#print axioms spill_speichern_ist_write64
#print axioms spill_laden_ist_read64
#print axioms spill_ausserhalb_verweigert
#print axioms spill_frisch_meidet_puffer
#print axioms spill_frisch_leer
#print axioms spillSlot_rW_null
#print axioms spillSlot_rW_sechzehn
#print axioms spill_getrennt_rW
#print axioms spill_fill_kommutiert
#print axioms spill_stabil_bleibt_fremd
#print axioms spill_fill_kommutiert_zeuge
#print axioms spill_frisch_bleibt_bei_fremd_issue
#print axioms spill_bleibt_bei_fremd_flush
#print axioms fremd_meidet_slot0
#print axioms fremd_puffer_mem
#print axioms spill_schritt1
#print axioms spill_puffer1
#print axioms spill_flush_schritt
#print axioms spill_flush_wechselt
#print axioms spill_frisch0
#print axioms spill_frisch1
#print axioms spill_tso_zeuge

end Gabbro.Grammatik.X86
