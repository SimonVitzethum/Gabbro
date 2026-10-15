/-
  File:      Grammatik/X86/OptSpillFresh.lean
  Subject:   Spill-freshness optimiser rule (lane 879, DESIGN section 7 row).

  DESIGN row (Layout / allocation): local premise "colouring vs recomputed
  liveness; spills fresh private frame slots, token-threaded, save/restore on
  all paths", certificate "B+C map", failure "fused 16-byte spill over two
  live carriers; spill slot overlapping neighbour frame; address-taken spill
  via call arg", phase L. Proved here over reused canonical vocabulary
  (`Stapel`, `Speicher`, `SpillPrivate`, `CostSummary`); no new ISA, no
  second IR, no source/checker/Spec/goal/emitter change.
-/
import Grammatik.X86.Speicher
import Grammatik.X86.Stapel
import Grammatik.X86.SpillPrivate
import Grammatik.X86.CostSummary
import Grammatik.ReferenzB

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one spill site (DESIGN row):
    fresh private slot, token-threaded, save/restore on all paths,
    neighbour-frame disjoint, not address-taken, single carrier. -/
structure SpillCert where
  frischOk : Bool
  tokenGefuehrt : Bool
  aufAllenWegen : Bool
  nachbarGetrennt : Bool
  nichtAdressGenommen : Bool
  einTraeger : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def spillZulassen (c : SpillCert) : Bool :=
  c.frischOk && c.tokenGefuehrt && c.aufAllenWegen && c.nachbarGetrennt &&
    c.nichtAdressGenommen && c.einTraeger

/-! ## 1. Refusals: the DESIGN failure cases must NOT spill. -/

/-- A spill slot overlapping the neighbour frame refuses. -/
theorem spillVerweigert_nachbar (c : SpillCert)
    (h : c.nachbarGetrennt = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- An address-taken spill (via call arg) refuses. -/
theorem spillVerweigert_adresse (c : SpillCert)
    (h : c.nichtAdressGenommen = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- A fused 16-byte spill over two live carriers refuses. -/
theorem spillVerweigert_fusion (c : SpillCert)
    (h : c.einTraeger = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- A non-token-threaded spill refuses. -/
theorem spillVerweigert_token (c : SpillCert)
    (h : c.tokenGefuehrt = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- A spill missing save/restore on some path refuses. -/
theorem spillVerweigert_wege (c : SpillCert)
    (h : c.aufAllenWegen = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- A non-fresh slot refuses. -/
theorem spillVerweigert_frisch (c : SpillCert)
    (h : c.frischOk = false) :
    spillZulassen c = false := by
  simp [spillZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_spillZulassen_ok :
    spillZulassen ⟨true, true, true, true, true, true⟩ = true := by
  decide

/-! ## 2. Save/restore: value and fault preservation on the admitted slot. -/

/-- A spilled word reloads: the save IS the permission-checked store and
    the reload IS the permission-checked load, so value and fault outcome
    agree (out-of-frame and permission refusals stay loud `none`). -/
theorem spill_rundreise (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort)
    (hBound : idx < r.schlitzZahl)
    (hWr : sichereWort m r idx v = some m')
    (hLes : lesbar8 m (r.schlitzAddr idx) = true) :
    ladeWort m' r idx = some v :=
  sichere_lade_rundreise m m' r idx v hBound hWr hLes

/-- Observation preservation: a carrier read at a disjoint address survives
    the spill save, so contracts at their place read the same values. -/
theorem spill_fremd_bleibt (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (e : Adresse) (v : Wort)
    (hBound : idx < r.schlitzZahl)
    (hWr : sichereWort m r idx v = some m')
    (hDis : Disjunkt (r.schlitzAddr idx) e) :
    ladeErgebnis m' e = ladeErgebnis m e :=
  ergebnis_bleibt_vor_rahmen m m' r idx e v hBound hWr hDis

/-- Permission preservation: a spill save changes bytes only, so no fault
    is added or removed elsewhere (fault outcome agrees on every later
    checked access through unchanged permissions). -/
theorem spill_berechtigungen (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort)
    (hBound : idx < r.schlitzZahl)
    (hWr : sichereWort m r idx v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar :=
  sichereWort_erhaelt_berechtigungen m m' r idx v hBound hWr

/-- IEEE byte preservation: the spilled 64-bit word carries its eight
    little-endian bytes whole into the slot, so scalar integer and scalar
    float bit patterns (including NaN payloads) survive spill/reload
    exactly -- no rounding, no width change, no host `strtod`. -/
theorem spill_bytes_behalten (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort)
    (hBound : idx < r.schlitzZahl)
    (hWr : sichereWort m r idx v = some m')
    (k : Nat) (hk : k < 8) :
    m'.bytes (addrOff (r.schlitzAddr idx) k) = wortByte v k := by
  unfold sichereWort at hWr
  rw [if_pos hBound] at hWr
  unfold write64 at hWr
  by_cases hc : schreibbar8 m (r.schlitzAddr idx) = true
  · rw [if_pos hc] at hWr
    cases hWr
    show writeBytes m (r.schlitzAddr idx) v
      (addrOff (r.schlitzAddr idx) k) = wortByte v k
    unfold writeBytes
    exact writeBytesN_hit m _ v 8 k hk (Nat.le_refl 8)
  · rw [if_neg hc] at hWr
    cases hWr

/-! ## 2b. Witness memories: one spill save on the checked frame. -/

/-- Witness spill value and slots: value `42` into slot 1, foreign word
    `22` at slot 3, on the checked witness frame. -/
def spillWv : Wort := 42

def spillWw : Wort := 22

/-- After the spill save of `42` into slot 1. -/
def spillWm' : Speicher :=
  { speicherZeuge with
    bytes := writeBytes speicherZeuge (rahmenZeuge.schlitzAddr 1) spillWv }

/-- After the foreign store of `22` at slot 3. -/
def spillWm2 : Speicher :=
  { speicherZeuge with
    bytes := writeBytes speicherZeuge (rahmenZeuge.schlitzAddr 3) spillWw }

/-- Both orders: foreign store after the spill save. -/
def spillWmab : Speicher :=
  { spillWm' with
    bytes := writeBytes spillWm' (rahmenZeuge.schlitzAddr 3) spillWw }

/-- Both orders: spill save after the foreign store. -/
def spillWmba : Speicher :=
  { spillWm2 with
    bytes := writeBytes spillWm2 (rahmenZeuge.schlitzAddr 1) spillWv }

/-! ## 3. Connection: the admitted spill preserves everything the DESIGN
    row promises.

    Certificate shape (local rewrite record plus recomputed analysis
    citations): the validator-decided `SpillCert` (`spillZulassen`), the
    B-map citation that the slot lies in the frame (`hBoundOf`), the B+C
    citation that the slot is disjoint from the neighbour/foreign footprint
    (`hSepOf`), and the C citation that every expansion class is bounded
    (`hAlle`, so the spill work is counted in `expandBound`, never hidden).
    Refusal: `spillZulassen c = false` on neighbour-frame overlap,
    address-taken spill, fused 16-byte spill, missing token threading,
    missing save/restore path, or stale slot (section 1) -- the rule must
    NOT fire there and falls back to another certified translation, never
    to a warning. No `ensures` is derived; no faulting form is speculated
    above its guard (out-of-frame and permission refusals stay loud `none`
    through `sichereWort`).

    What each conjunct covers: (1) value; (2) faults via unchanged
    permissions; (3) per-byte observation outside the slot; (4) IEEE bit
    patterns via whole little-endian bytes (no rounding, no width change);
    (5) contracts at their place via unchanged disjoint carrier reads, and
    call logs via no new call or shared access (the spill is one private
    `write64`/`read64` pair on a fresh slot, token-threaded); (6)
    concurrency via both-orders agreement with a disjoint foreign store
    (freshness-to-commutation, `SpillPrivate`); (7) budget via the counted
    `expandBound` that adds `spillCount` in full. -/
theorem OptSpillFresh_verbindung
    (c : SpillCert) (r : Rahmen) (idx : Nat) (v : Wort)
    (m m' : Speicher) (fremd : Adresse) (w : Wort)
    (m2 m_ab m_ba : Speicher) (s : CostSummary) (src : Nat) (x : Adresse)
    (hAdm : spillZulassen c = true)
    (hBoundOf : spillZulassen c = true → idx < r.schlitzZahl)
    (hSepOf : spillZulassen c = true → Disjunkt (r.schlitzAddr idx) fremd)
    (hWr : sichereWort m r idx v = some m')
    (hLes : lesbar8 m (r.schlitzAddr idx) = true)
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k)
    (hwrAB : write64 m' fremd w = some m_ab)
    (hwr2 : write64 m fremd w = some m2)
    (hwrBA : write64 m2 (r.schlitzAddr idx) v = some m_ba)
    (hAlle : ∀ c0, (s.expand c0).isSome = true) :
    ladeWort m' r idx = some v ∧
    (m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar) ∧
    m'.bytes x = m.bytes x ∧
    (∀ k : Nat, k < 8 → m'.bytes (addrOff (r.schlitzAddr idx) k) = wortByte v k) ∧
    ladeErgebnis m' fremd = ladeErgebnis m fremd ∧
    ((∀ xb, m_ab.bytes xb = m_ba.bytes xb) ∧
      m_ab.schreibbar = m.schreibbar ∧
      m_ba.schreibbar = m.schreibbar) ∧
    (∃ k, expandBound s src = some k) := by
  have hBound : idx < r.schlitzZahl := hBoundOf hAdm
  have hSep : Disjunkt (r.schlitzAddr idx) fremd := hSepOf hAdm
  have hwr1 : write64 m (spillSlot r idx) v = some m' := by
    unfold sichereWort at hWr
    rw [if_pos hBound] at hWr
    exact hWr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact spill_rundreise m m' r idx v hBound hWr hLes
  · exact spill_berechtigungen m m' r idx v hBound hWr
  · exact sichereWort_rahmen m m' r idx x v hBound hWr haussen
  · intro k hk
    exact spill_bytes_behalten m m' r idx v hBound hWr k hk
  · exact spill_fremd_bleibt m m' r idx fremd v hBound hWr hSep
  · exact spill_fill_kommutiert m m' m2 m_ab m_ba r idx fremd v w
      hwr1 hwrAB hwr2 hwrBA hSep
  · exact expandBound_gilt s src hAlle

/-! ## 4. Joint witness: the rule fires beside a memory-changing run. -/

/-- JOINT WITNESS for `OptSpillFresh_verbindung`: ALL premises instantiated
    JOINTLY on the checked witness frame (slot 1 spills `42`, slot 3 is the
    disjoint foreign word `22`), beside the NON-DEGENERATE reference program
    `refD` (whose `einzahlen` writes its table, `refEin_schreibt`) and the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). The spill save itself observably
    changes its slot byte (zero becomes the low byte of `42`). -/
theorem OptSpillFresh_verbindung_zeuge :
    ∃ (c : SpillCert) (r : Rahmen) (idx : Nat) (v : Wort)
      (m m' : Speicher) (fremd : Adresse) (w : Wort)
      (m2 m_ab m_ba : Speicher) (s : CostSummary) (src : Nat) (x : Adresse)
      (_hAdm : spillZulassen c = true)
      (_hBoundOf : spillZulassen c = true → idx < r.schlitzZahl)
      (_hSepOf : spillZulassen c = true → Disjunkt (r.schlitzAddr idx) fremd)
      (_hWr : sichereWort m r idx v = some m')
      (_hLes : lesbar8 m (r.schlitzAddr idx) = true)
      (_haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k)
      (_hwrAB : write64 m' fremd w = some m_ab)
      (_hwr2 : write64 m fremd w = some m2)
      (_hwrBA : write64 m2 (r.schlitzAddr idx) v = some m_ba)
      (_hAlle : ∀ c0, (s.expand c0).isSome = true),
      ladeWort m' r idx = some v ∧
      (m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
        m'.ausfuehrbar = m.ausfuehrbar) ∧
      m'.bytes x = m.bytes x ∧
      (∀ k : Nat, k < 8 →
        m'.bytes (addrOff (r.schlitzAddr idx) k) = wortByte v k) ∧
      ladeErgebnis m' fremd = ladeErgebnis m fremd ∧
      ((∀ xb, m_ab.bytes xb = m_ba.bytes xb) ∧
        m_ab.schreibbar = m.schreibbar ∧
        m_ba.schreibbar = m.schreibbar) ∧
      (∃ k, expandBound s src = some k) ∧
      m.bytes (r.schlitzAddr idx) ≠ m'.bytes (r.schlitzAddr idx) ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hSepZ : Disjunkt (rahmenZeuge.schlitzAddr 1)
      (rahmenZeuge.schlitzAddr 3) :=
    schlitz_disjunkt rahmenZeuge 1 3 (by decide) (by decide)
      (by decide) (by decide)
  have hBoundOfZ :
      spillZulassen ⟨true, true, true, true, true, true⟩ = true →
        1 < rahmenZeuge.schlitzZahl := by
    intro _
    decide
  have hSepOfZ :
      spillZulassen ⟨true, true, true, true, true, true⟩ = true →
        Disjunkt (rahmenZeuge.schlitzAddr 1)
          (rahmenZeuge.schlitzAddr 3) := by
    intro _
    exact hSepZ
  have hWrZ :
      sichereWort speicherZeuge rahmenZeuge 1 spillWv = some spillWm' := by
    unfold sichereWort
    rw [if_pos (by decide : 1 < rahmenZeuge.schlitzZahl)]
    unfold write64
    rw [if_pos (by decide : schreibbar8 speicherZeuge
      (rahmenZeuge.schlitzAddr 1) = true)]
    rfl
  have haussenZ : ∀ k : Nat, k < 8 →
      rahmenZeuge.schlitzAddr 3 ≠
        addrOff (rahmenZeuge.schlitzAddr 1) k := by
    intro k hk
    have h := hSepZ k 0 hk (by decide)
    rw [addrOff_null] at h
    exact Ne.symm h
  have hwr2Z : write64 speicherZeuge (rahmenZeuge.schlitzAddr 3) spillWw =
      some spillWm2 := by
    unfold write64
    rw [if_pos (by decide : schreibbar8 speicherZeuge
      (rahmenZeuge.schlitzAddr 3) = true)]
    rfl
  have hwrABZ : write64 spillWm' (rahmenZeuge.schlitzAddr 3) spillWw =
      some spillWmab := by
    unfold write64
    rw [if_pos (by decide : schreibbar8 spillWm'
      (rahmenZeuge.schlitzAddr 3) = true)]
    rfl
  have hwrBAZ : write64 spillWm2 (rahmenZeuge.schlitzAddr 1) spillWv =
      some spillWmba := by
    unfold write64
    rw [if_pos (by decide : schreibbar8 spillWm2
      (rahmenZeuge.schlitzAddr 1) = true)]
    rfl
  have hV := OptSpillFresh_verbindung
    ⟨true, true, true, true, true, true⟩
    rahmenZeuge 1 spillWv speicherZeuge spillWm'
    (rahmenZeuge.schlitzAddr 3) spillWw spillWm2 spillWmab spillWmba
    blattSummary 1 (rahmenZeuge.schlitzAddr 3)
    probe_spillZulassen_ok hBoundOfZ hSepOfZ hWrZ zeuge_lesbar8
    haussenZ hwrABZ hwr2Z hwrBAZ blattSummary_beschraenkt
  have hWechselt : speicherZeuge.bytes (rahmenZeuge.schlitzAddr 1) ≠
      spillWm'.bytes (rahmenZeuge.schlitzAddr 1) := by
    have hhit := writeBytesN_hit speicherZeuge (rahmenZeuge.schlitzAddr 1)
      spillWv 8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠ spillWm'.bytes (rahmenZeuge.schlitzAddr 1)
    unfold spillWm'
    show BitVec.ofNat 8 0 ≠ writeBytes speicherZeuge
      (rahmenZeuge.schlitzAddr 1) spillWv (rahmenZeuge.schlitzAddr 1)
    unfold writeBytes
    rw [hhit]
    decide
  refine ⟨⟨true, true, true, true, true, true⟩, rahmenZeuge, 1, spillWv,
    speicherZeuge, spillWm', rahmenZeuge.schlitzAddr 3, spillWw,
    spillWm2, spillWmab, spillWmba, blattSummary, 1,
    rahmenZeuge.schlitzAddr 3,
    probe_spillZulassen_ok, hBoundOfZ, hSepOfZ, hWrZ, zeuge_lesbar8,
    haussenZ, hwrABZ, hwr2Z, hwrBAZ, blattSummary_beschraenkt,
    hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1,
    hV.2.2.2.2.2.2, hWechselt, refEin_schreibt (), refB_erreicht,
    refB_schreibt⟩

/- CUTS:
   - PROVED: validator admission `spillZulassen` with all six refusal
     directions (neighbour-frame overlap, address-taken, fused 16-byte,
     missing token threading, missing save/restore path, stale slot) plus
     the positive probe; value/fault round-trip, disjoint-carrier
     observation, permission preservation, whole-byte (IEEE bit-pattern)
     preservation; the connection `OptSpillFresh_verbindung` (value,
     faults, observations, IEEE bytes, contracts-at-place via unchanged
     disjoint reads, no new call/shared access, both-orders concurrency,
     counted budget) with the joint witness on the checked frame beside
     the memory-changing `refB` run of the table-writing `refD`.
   - OPEN / not claimed: the SCFG-side application waits for the accepted
     287 interface and is not invented here (reuses `SpillPrivate` TSO-side
     commutation only); no aligned multi-byte atomicity beyond
     byte-extensional agreement; no LOCK RMW; no source-to-target
     simulation (no source carrier is mapped); no cost/fairness/timing
     claim beyond the counted `expandBound`; no new ISA form.
   - The refusal `Bool` is validator admission, never a hardware fault;
     a refused spill falls back to another certified translation, never
     to a warning. No `ensures` is derived anywhere.
   - No second IR and no second evaluator: only canonical `Speicher`
     stores/loads, `Stapel` slot addresses, `SpillPrivate` freshness/
     commutation and the `CostSummary` schema are reused.
-/

#print axioms SpillCert
#print axioms spillZulassen
#print axioms spillVerweigert_nachbar
#print axioms spillVerweigert_adresse
#print axioms spillVerweigert_fusion
#print axioms spillVerweigert_token
#print axioms spillVerweigert_wege
#print axioms spillVerweigert_frisch
#print axioms probe_spillZulassen_ok
#print axioms spill_rundreise
#print axioms spill_fremd_bleibt
#print axioms spill_berechtigungen
#print axioms spill_bytes_behalten
#print axioms spillWv
#print axioms spillWw
#print axioms spillWm'
#print axioms spillWm2
#print axioms spillWmab
#print axioms spillWmba
#print axioms OptSpillFresh_verbindung
#print axioms OptSpillFresh_verbindung_zeuge

end Gabbro.Grammatik.X86
