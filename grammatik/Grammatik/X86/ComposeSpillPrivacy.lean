/-
  File:      Grammatik/X86/ComposeSpillPrivacy.lean
  Subject:   Composition closing: allocation spills to fresh private frame slots (lane 830).

  Producer/consumer interface closed here (all producers already accepted,
  reused by name, never re-proved):
  - Producer `SpillPrivate` (lane 343): `spillSlot`, `SpillFrisch`,
    `GetrenntK`, `spillPrivatOk`, `SpillZugelassen`, checked save/load
    equations, freshness/disjointness/commutation facts.
  - Producer `Stapel` (lane 309): `Rahmen`, `sichereWort`, `ladeWort`,
    `sichere_lade_rundreise`, permission/bound refusals and preservation.
  - Producer `TableLayout` (lane 345): `zeugenU` non-degenerate program
    (table `konto` written by `setze`) for the joint witness.
  Consumer: the token-threaded `spillPrivatSchritt` below threads one
  `Option Speicher` token through checked save then checked reload, so a
  refusal on ANY path yields `none` loudly. The closing theorem joins
  validator admission with TSO freshness (`SpillZugelassen`), checked
  save/restore round-trip (`w = v`), permission preservation and disjoint
  foreign stability. No second IR, no second evaluator, no new ISA form.
-/
import Grammatik.X86.SpillPrivate
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

/-- Token-threaded private spill step: checked save then checked reload.
    Every refusal path yields `none`; success yields the post-save token
    with the reloaded word. -/
def spillPrivatSchritt (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) : Option (Speicher × Wort) :=
  match sichereWort m r idx v with
  | none => none
  | some m1 =>
    match ladeWort m1 r idx with
    | none => none
    | some w => some (m1, w)

/-! ## 1. Token threading: success and refusal paths -/

/-- SUCCESS: a reached save plus a reached reload compute the step.
    Both premises name one threaded token each. -/
theorem spillPrivatSchritt_erfolg (m m1 : Speicher) (r : Rahmen) (idx : Nat)
    (v w : Wort)
    (hwr : sichereWort m r idx v = some m1)
    (hrd : ladeWort m1 r idx = some w) :
    spillPrivatSchritt m r idx v = some (m1, w) := by
  unfold spillPrivatSchritt
  simp [hwr, hrd]

/-- REFUSAL THREADING: a refused save yields `none` loudly, on every path. -/
theorem spillPrivatSchritt_verweigert_speichern (m : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort)
    (hwr : sichereWort m r idx v = none) :
    spillPrivatSchritt m r idx v = none := by
  unfold spillPrivatSchritt
  simp [hwr]

/-! ## 2. Closing: admission, round-trip, permissions, foreign stability -/

/-- CLOSING: validator admission plus TSO freshness give joint admission;
    the checked save reloads its own value through the threaded token;
    permissions are preserved; a disjoint foreign footprint reads back
    unchanged. Every premise is used: `hb`/`hrd`/`hwr` through the
    round-trip and permission preservation, `hok`/`hfrisch` through joint
    admission, `hdis`/`hwr` through foreign stability, `hrd2` by injection
    against the round-trip. -/
theorem ComposeSpillPrivacy_verbindung
    (m m1 : Speicher) (r : Rahmen) (idx : Nat) (v w : Wort)
    (fremd : Adresse) (s : TSOZustand) (genommen extent : Bool)
    (hb : idx < r.schlitzZahl)
    (hok : spillPrivatOk genommen extent (decide (idx < r.schlitzZahl)) = true)
    (hfrisch : SpillFrisch s r idx)
    (hdis : GetrenntK r idx fremd)
    (hrd : lesbar8 m (spillSlot r idx) = true)
    (hwr : sichereWort m r idx v = some m1)
    (hrd2 : ladeWort m1 r idx = some w) :
    w = v ∧
    spillPrivatSchritt m r idx v = some (m1, v) ∧
    SpillZugelassen genommen extent s r idx ∧
    m1.lesbar = m.lesbar ∧ m1.schreibbar = m.schreibbar ∧
    read64 m1 fremd = read64 m fremd ∧
    ladeWort m1 r idx = some v := by
  have hround : ladeWort m1 r idx = some v :=
    sichere_lade_rundreise m m1 r idx v hb hwr hrd
  have hwv : w = v := Option.some_inj.mp (hrd2.symm.trans hround)
  have hstep : spillPrivatSchritt m r idx v = some (m1, v) :=
    spillPrivatSchritt_erfolg m m1 r idx v v hwr hround
  have hperm := sichereWort_erhaelt_berechtigungen m m1 r idx v hb hwr
  have hwr64 : write64 m (spillSlot r idx) v = some m1 := by
    have h := spill_speichern_ist_write64 m r idx v
    rw [h, if_pos hb] at hwr
    exact hwr
  have hfremd : read64 m1 fremd = read64 m fremd :=
    read64_rahmen m m1 (spillSlot r idx) fremd v hwr64 hdis
  exact ⟨hwv, hstep, ⟨hok, hfrisch⟩, hperm.1, hperm.2.1, hfremd, hround⟩

/-! ## 3. Planted refusals: loud on every path -/

/-- TAKEN REFUSAL: an address-taken slot is never jointly admitted.
    Uses the accepted producer refusal through `h`. -/
theorem ComposeSpillPrivacy_verweigert_genommen
    (s : TSOZustand) (r : Rahmen) (idx : Nat) (extent : Bool)
    (h : SpillZugelassen true extent s r idx) : False :=
  absurd h (spill_zugelassen_verweigert_genommen extent s r idx)

/-- OUT-OF-FRAME REFUSAL: a slot past the frame saves nothing, and the
    threaded token carries the refusal: both the raw save and the composed
    step yield `none`. -/
theorem ComposeSpillPrivacy_verweigert_aussen
    (m : Speicher) (r : Rahmen) (idx : Nat) (v : Wort)
    (h : r.schlitzZahl ≤ idx) :
    sichereWort m r idx v = none ∧ spillPrivatSchritt m r idx v = none := by
  have hwr := sichereWort_ausserhalb m r idx v h
  exact ⟨hwr, spillPrivatSchritt_verweigert_speichern m r idx v hwr⟩

/-- GUARD REFUSAL: a write-protected slot saves nothing, and the threaded
    token carries the refusal: both the raw save and the composed step
    yield `none`. -/
theorem ComposeSpillPrivacy_verweigert_schutz
    (m : Speicher) (r : Rahmen) (idx : Nat) (v : Wort)
    (hb : idx < r.schlitzZahl)
    (h : schreibbar8 m (spillSlot r idx) = false) :
    sichereWort m r idx v = none ∧ spillPrivatSchritt m r idx v = none := by
  have hwr := sichereWort_verweigert m r idx v hb h
  exact ⟨hwr, spillPrivatSchritt_verweigert_speichern m r idx v hwr⟩

/-! ## 4. Joint witness: reached memory-changing run on a writer program -/

/-- Witness post-save memory: `speicherZeuge` with word `42` stored at
    spill slot 0 of `spillRahmenW`. -/
def spillZeuM1 : Speicher :=
  { speicherZeuge with
    bytes := writeBytes speicherZeuge (spillSlot spillRahmenW 0) 42 }

/-- Witness slot bound: slot 0 lies inside the four-slot frame. -/
theorem spillZeu_schranke : 0 < spillRahmenW.schlitzZahl := by
  decide

/-- Witness slot readability: eight bytes at slot 0 are readable. -/
theorem spillZeu_lesbar :
    lesbar8 speicherZeuge (spillSlot spillRahmenW 0) = true := by
  rw [spillSlot_rW_null]
  decide

/-- Witness slot writability: eight bytes at slot 0 are writable. -/
theorem spillZeu_schreibbar :
    schreibbar8 speicherZeuge (spillSlot spillRahmenW 0) = true := by
  rw [spillSlot_rW_null]
  decide

/-- REACHED SAVE: the checked spill save computes to the witness memory. -/
theorem spillZeu_speichert :
    sichereWort speicherZeuge spillRahmenW 0 42 = some spillZeuM1 := by
  unfold sichereWort spillZeuM1
  rw [if_pos spillZeu_schranke]
  unfold write64
  have hcond : schreibbar8 speicherZeuge (spillRahmenW.schlitzAddr 0) = true :=
    spillZeu_schreibbar
  rw [if_pos hcond]
  rfl

/-- REACHED RELOAD: the saved word `42` loads back from the witness slot. -/
theorem spillZeu_rundreise :
    ladeWort spillZeuM1 spillRahmenW 0 = some 42 :=
  sichere_lade_rundreise speicherZeuge spillZeuM1 spillRahmenW 0 42
    spillZeu_schranke spillZeu_speichert spillZeu_lesbar

/-- MEMORY CHANGE: the reached save observably changes the slot byte
    (zero becomes the low byte of `42`). -/
theorem spillZeu_wechselt :
    speicherZeuge.bytes (spillSlot spillRahmenW 0) ≠
      spillZeuM1.bytes (spillSlot spillRahmenW 0) := by
  have hhit := writeBytesN_hit speicherZeuge (spillSlot spillRahmenW 0)
    42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show BitVec.ofNat 8 0 ≠
    writeBytes speicherZeuge (spillSlot spillRahmenW 0) 42
      (spillSlot spillRahmenW 0)
  unfold writeBytes
  rw [hhit]
  decide

/-- Witness admission: a private in-frame slot is validator-admitted. -/
theorem spillZeu_ok :
    spillPrivatOk false false (decide (0 < spillRahmenW.schlitzZahl)) =
      true := by
  decide

/-- JOINT WITNESS: every premise of the closing theorem holds jointly on
    concrete values — a reached checked save of `42` into slot 0 that
    observably changes memory and reloads through the threaded token —
    beside the non-degenerate writer program `zeugenU` (table `konto`
    written by `setze`). -/
theorem ComposeSpillPrivacy_verbindung_zeuge :
    ∃ (m m1 : Speicher) (r : Rahmen) (idx : Nat) (v w : Wort)
      (fremd : Adresse) (s : TSOZustand) (genommen extent : Bool),
      idx < r.schlitzZahl ∧
      spillPrivatOk genommen extent (decide (idx < r.schlitzZahl)) = true ∧
      SpillFrisch s r idx ∧
      GetrenntK r idx fremd ∧
      lesbar8 m (spillSlot r idx) = true ∧
      sichereWort m r idx v = some m1 ∧
      ladeWort m1 r idx = some w ∧
      (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
      w = v ∧
      m.bytes (spillSlot r idx) ≠ m1.bytes (spillSlot r idx) ∧
      spillPrivatSchritt m r idx v = some (m1, v) := by
  have hmain := ComposeSpillPrivacy_verbindung speicherZeuge spillZeuM1
    spillRahmenW 0 42 42 16 spillTSO0 false false
    spillZeu_schranke spillZeu_ok spill_frisch0 spill_getrennt_rW
    spillZeu_lesbar spillZeu_speichert spillZeu_rundreise
  refine ⟨speicherZeuge, spillZeuM1, spillRahmenW, 0, 42, 42, 16,
    spillTSO0, false, false,
    spillZeu_schranke, spillZeu_ok, spill_frisch0, spill_getrennt_rW,
    spillZeu_lesbar, spillZeu_speichert, spillZeu_rundreise,
    zeugenU_schreibt, hmain.1, spillZeu_wechselt, hmain.2.1⟩

/- CUTS:
    - Proved here: token-threaded spill step with success/refusal paths
      (`spillPrivatSchritt_erfolg`, `spillPrivatSchritt_verweigert_speichern`);
      the closing composition of validator admission with TSO freshness,
      checked save/restore round-trip, permission preservation and disjoint
      foreign stability (`ComposeSpillPrivacy_verbindung`, reusing the
      accepted `Stapel`/`SpillPrivate` lemmas by name); planted refusals on
      every path (taken slot, out-of-frame slot, write-protected slot);
      reached memory-changing run with reload beside the non-degenerate
      writer program `zeugenU` (`ComposeSpillPrivacy_verbindung_zeuge`).
    - OPEN / not claimed: the SCFG-side application waits for the accepted
      287 interface (owner 287, reviewer 303) and is not invented here; W
      store/read bridges wait for accepted 567/570 interfaces (owners 573,
      574); the extended decoder path is lane 575's, not assumed here; no
      aligned multi-byte atomicity beyond byte-extensional commutation; no
      LOCK RMW; no source-to-target simulation (no source carrier is mapped);
      no validator soundness (`valX86_sound`); no cost, fairness or timing
      claim; no new ISA form is added.
    - The refusal `Bool` is validator admission, never a hardware fault.
    - No second IR and no second evaluator: only canonical `Speicher`
      stores/loads, `Stapel` slot addresses and `TSO` freshness predicates
      are reused.
-/

#print axioms spillPrivatSchritt
#print axioms spillPrivatSchritt_erfolg
#print axioms spillPrivatSchritt_verweigert_speichern
#print axioms ComposeSpillPrivacy_verbindung
#print axioms ComposeSpillPrivacy_verbindung_zeuge
#print axioms ComposeSpillPrivacy_verweigert_genommen
#print axioms ComposeSpillPrivacy_verweigert_aussen
#print axioms ComposeSpillPrivacy_verweigert_schutz
#print axioms spillZeuM1
#print axioms spillZeu_schranke
#print axioms spillZeu_lesbar
#print axioms spillZeu_schreibbar
#print axioms spillZeu_speichert
#print axioms spillZeu_rundreise
#print axioms spillZeu_wechselt
#print axioms spillZeu_ok

end Gabbro.Grammatik.X86
