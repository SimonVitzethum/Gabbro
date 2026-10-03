/-
  Composition closing: unwind tables to actual frame layouts (lane 849).

  Producer/consumer interface closed here: the unwind-table producer rows
  (`UnwindEintrag`: code range plus described frame depth and saved slot)
  describe, and the checked frame-layout consumer (`Rahmen` extent from
  `Stapel`, `Belegung` callee-save range, actual `Speicher` bytes) admits.
  This file only composes already-accepted definitions and theorems
  (`rahmenOk`, `Belegung.passt`, `sichereWort`/`ladeWort`,
  `sichere_lade_rundreise`, `KetteOk`); it re-proves no frame, layout,
  decoder or step fact and defines no second interpreter or executor.

  A conjunction of checks is not execution: the closing theorem shows the
  composed unwind read going through an actual memory-changing frame save,
  and misdescribing rows (wrong depth, slot outside the frame or the
  callee-save range, program counter outside the row range) loudly refuse
  with `none`.
-/
import Grammatik.X86.Stapel
import Grammatik.X86.StackUnwind

namespace Gabbro.Grammatik.X86

/-- One unwind-table row: the code range it covers plus the frame shape it
    claims (depth in bytes, slot holding the saved word). A producer-side
    description; admission against the actual layout is `unwindPasst`. -/
structure UnwindEintrag where
  start : Nat
  len : Nat
  tiefe : Nat
  slot : Nat
  deriving DecidableEq, Repr

/-! ## 1. Agreement: the row describes this frame and layout. -/

/-- Admission of one unwind row against the actual frame and layout: the
    program counter lies in the row range, the described depth equals the
    actual frame depth, and the saved slot is both a callee-save slot of
    the layout and a slot of the frame. Decided, never assumed. -/
def unwindPasst (e : UnwindEintrag) (rip : Nat) (r : Rahmen)
    (b : Belegung) : Bool :=
  decide (e.start ≤ rip ∧ rip < e.start + e.len ∧ e.tiefe = r.tiefe ∧
    b.spill ≤ e.slot ∧ e.slot < b.spill + b.gerettet ∧
    e.slot < r.schlitzZahl)

/-- A passing row pins the saved slot inside the frame. -/
theorem unwindPasst_schranke (e : UnwindEintrag) (rip : Nat) (r : Rahmen)
    (b : Belegung)
    (h : unwindPasst e rip r b = true) :
    e.slot < r.schlitzZahl := by
  unfold unwindPasst at h
  simp only [decide_eq_true_eq] at h
  exact h.2.2.2.2.2

/-! ## 2. Composed unwind read through the actual frame. -/

/-- The composed unwind read: a passing row reads its saved slot through
    the checked frame load; a misdescribing row loudly refuses with `none`.
    The only consumer step is the accepted `ladeWort`; no second loader. -/
def unwindLese (m : Speicher) (r : Rahmen) (e : UnwindEintrag) (rip : Nat)
    (b : Belegung) : Option Wort :=
  if unwindPasst e rip r b then ladeWort m r e.slot else none

/-- ROW HIT: through an actual memory-changing frame save, the composed
    unwind read of a passing row delivers the saved word. Composes the
    accepted frame round-trip (`sichere_lade_rundreise`); no frame, layout
    or permission fact is re-proved here. Every premise pins one guard of
    the save, the read-back, or the row admission. -/
theorem unwindLese_trifft (m m' : Speicher) (r : Rahmen) (b : Belegung)
    (e : UnwindEintrag) (rip : Nat) (v : Wort)
    (hpass : unwindPasst e rip r b = true)
    (hwr : sichereWort m r e.slot v = some m')
    (hrd : lesbar8 m (r.schlitzAddr e.slot) = true) :
    unwindLese m' r e rip b = some v := by
  have hb : e.slot < r.schlitzZahl := unwindPasst_schranke e rip r b hpass
  unfold unwindLese
  rw [if_pos hpass]
  exact sichere_lade_rundreise m m' r e.slot v hb hwr hrd

/-! ## 3. Refusals: misdescribing rows unwind nothing. -/

/-- DEPTH-REFUSAL: a row whose described depth differs from the actual
    frame depth unwinds nothing. The inequality is used to discharge the
    depth conjunct of the admission. -/
theorem unwindLese_falsch_tiefe (m : Speicher) (r : Rahmen)
    (e : UnwindEintrag) (rip : Nat) (b : Belegung)
    (hne : e.tiefe ≠ r.tiefe) :
    unwindLese m r e rip b = none := by
  have h : unwindPasst e rip r b = false := by
    unfold unwindPasst
    rw [decide_eq_false]
    intro hcon
    exact hne hcon.2.2.1
  unfold unwindLese
  simp [h]

/-- SLOT-REFUSAL: a row naming a slot outside the actual frame unwinds
    nothing. The bound is used to discharge the frame-slot conjunct. -/
theorem unwindLese_falsch_slot (m : Speicher) (r : Rahmen)
    (e : UnwindEintrag) (rip : Nat) (b : Belegung)
    (hob : r.schlitzZahl ≤ e.slot) :
    unwindLese m r e rip b = none := by
  have h : unwindPasst e rip r b = false := by
    unfold unwindPasst
    rw [decide_eq_false]
    intro hcon
    exact absurd hcon.2.2.2.2.2 (Nat.not_lt.mpr hob)
  unfold unwindLese
  simp [h]

/-- RANGE-REFUSAL: a row that does not cover the program counter unwinds
    nothing. Both sides of the disjunction are used, one per branch. -/
theorem unwindLese_falsch_rip (m : Speicher) (r : Rahmen)
    (e : UnwindEintrag) (rip : Nat) (b : Belegung)
    (haus : rip < e.start ∨ e.start + e.len ≤ rip) :
    unwindLese m r e rip b = none := by
  have h : unwindPasst e rip r b = false := by
    unfold unwindPasst
    rw [decide_eq_false]
    intro hcon
    rcases haus with hklein | hgross
    · omega
    · omega
  unfold unwindLese
  simp [h]

/-! ## 4. Closing: hit through the composed step, refusal on misdescription. -/

/-- UNWIND-TABLE CLOSING through the composed read, generic over arbitrary
    admitted inputs: a passing row delivers the actually saved word through
    the memory-changing frame save, and the same row with a misdescribed
    depth (off by one full slot pair, so provably unequal) loudly refuses.
    Composes `unwindLese_trifft` and `unwindLese_falsch_tiefe`; no frame,
    layout or permission fact is re-proved here. -/
theorem ComposeUnwindTable_verbindung (m m' : Speicher) (r : Rahmen)
    (b : Belegung) (e : UnwindEintrag) (rip : Nat) (v : Wort)
    (hpass : unwindPasst e rip r b = true)
    (hwr : sichereWort m r e.slot v = some m')
    (hrd : lesbar8 m (r.schlitzAddr e.slot) = true) :
    unwindLese m' r e rip b = some v ∧
      unwindLese m r { e with tiefe := r.tiefe + 16 } rip b = none := by
  refine ⟨unwindLese_trifft m m' r b e rip v hpass hwr hrd, ?_⟩
  apply unwindLese_falsch_tiefe
  simp only
  omega

/-! ## 5. Joint witness: memory-changing run plus planted refusal. -/

/-- Witness layout: one spill slot, two callee-save slots, no stack args. -/
def zeugenBelegung849 : Belegung := { spill := 1, gerettet := 2, stapelArgs := 0 }

/-- Witness row: covers `[0x1000, 0x1010)`, describes depth 32 and slot 1. -/
def zeugenEintrag849 : UnwindEintrag :=
  { start := 0x1000, len := 16, tiefe := 32, slot := 1 }

/-- Witness program counter inside the row range. -/
def zeugenRip849 : Nat := 0x1005

/-- Witness memory after saving 42 into frame slot 1. -/
def zeugenM849 : Speicher := { speicherZeuge with
  bytes := writeBytes speicherZeuge (rahmenZeuge.schlitzAddr 1) 42 }

/-- The witness row passes against the witness frame and layout. -/
theorem zeugenPasst849 :
    unwindPasst zeugenEintrag849 zeugenRip849 rahmenZeuge zeugenBelegung849 =
      true := by
  decide

/-- The witness save installs 42 into frame slot 1. -/
theorem zeugenSchreibt849 :
    sichereWort speicherZeuge rahmenZeuge 1 42 = some zeugenM849 := by
  unfold sichereWort zeugenM849
  rw [if_pos (by decide : 1 < rahmenZeuge.schlitzZahl)]
  unfold write64
  rw [if_pos zeuge_schreibbar8]

/-- JOINT WITNESS: every premise of the closing holds jointly on a
    non-degenerate run -- the layout keeps two callee-save words some
    function saves, the save observably changes memory (zero becomes 42
    at the described slot) -- and the closing delivers both the composed
    hit and the planted depth-misdescription refusal. -/
theorem ComposeUnwindTable_verbindung_zeuge :
    ∃ (m m' : Speicher) (r : Rahmen) (b : Belegung) (e : UnwindEintrag)
      (rip : Nat) (v : Wort),
      (unwindPasst e rip r b = true) ∧
      (sichereWort m r e.slot v = some m') ∧
      (lesbar8 m (r.schlitzAddr e.slot) = true) ∧
      (v ≠ 0) ∧
      (m.bytes (r.schlitzAddr e.slot) ≠ m'.bytes (r.schlitzAddr e.slot)) ∧
      (unwindLese m' r e rip b = some v) ∧
      (unwindLese m r { e with tiefe := r.tiefe + 16 } rip b = none) := by
  have hmem : speicherZeuge.bytes (rahmenZeuge.schlitzAddr 1) ≠
      zeugenM849.bytes (rahmenZeuge.schlitzAddr 1) := by
    have hhit := writeBytesN_hit speicherZeuge (rahmenZeuge.schlitzAddr 1)
      42 8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes speicherZeuge (rahmenZeuge.schlitzAddr 1) 42
        (rahmenZeuge.schlitzAddr 1)
    unfold writeBytes
    rw [hhit]
    decide
  obtain ⟨hhit, hweig⟩ := ComposeUnwindTable_verbindung speicherZeuge
    zeugenM849 rahmenZeuge zeugenBelegung849 zeugenEintrag849 zeugenRip849 42
    zeugenPasst849 zeugenSchreibt849 zeuge_lesbar8
  exact ⟨speicherZeuge, zeugenM849, rahmenZeuge, zeugenBelegung849,
    zeugenEintrag849, zeugenRip849, 42,
    zeugenPasst849, zeugenSchreibt849, zeuge_lesbar8, by decide, hmem,
    hhit, hweig⟩

/-! ## 6. Planted refusal probes on the witness shape. -/

/-- PLANTED REFUSAL (range): the witness row does not cover `0x2000`,
    so unwinding there refuses. -/
theorem sonde_reichweite_verweigert849 :
    unwindLese speicherZeuge rahmenZeuge zeugenEintrag849 0x2000
      zeugenBelegung849 = none :=
  unwindLese_falsch_rip _ _ _ _ _ (Or.inr (by decide))

/-- PLANTED REFUSAL (slot): a row naming slot 9 of the four-slot witness
    frame unwinds nothing. -/
theorem sonde_slot_verweigert849 :
    unwindLese speicherZeuge rahmenZeuge
      { zeugenEintrag849 with slot := 9 } zeugenRip849
      zeugenBelegung849 = none := by
  apply unwindLese_falsch_slot
  decide

/- CUTS:
   Proved here: the unwind-table-to-frame-layout closing
   (`ComposeUnwindTable_verbindung`): a passing row delivers the actually
   saved word through the memory-changing frame save (`unwindLese_trifft`
   over the accepted `sichere_lade_rundreise`), and a depth-misdescribing
   row loudly refuses (`unwindLese_falsch_tiefe`), with the joint witness
   (non-degenerate run: two callee-save words, 42 observably stored) and
   planted range/slot refusals (`sonde_reichweite_verweigert849`,
   `sonde_slot_verweigert849`).
   NOT proved here, and not claimed:
   - No decoder, fetch, TSO/W/GX bridge, source/IR correspondence,
     ABI/loader/entry/budget connection, or whole-image coverage: rows are
     producer descriptions checked against the accepted frame vocabulary,
     never decoded bytes or executed transitions. Owning lanes: the codec,
     execution, bridge and validator-skeleton lanes behind `decodeExt`,
     `schritt`/`extByteschritt`, the TSO bridge and `valX86`.
   - No canonical `.eh_frame`/`.debug_frame` byte correspondence: the row
     shape (`start`/`len`/`tiefe`/`slot`) is the checked interface, not a
     parsed object-file encoding; augmentation, CIE/FDE parsing and LSDA
     stay OPEN.
   - No multi-frame cascade: one row unwinds one frame; chained
     caller/callee restoration reuses the accepted `StackUnwind` nested
     proof and is not re-proved here.
   - `none` is the absence of an unwind transition, never a termination
     claim; asynchronous unwinding (signals, interrupts) and concurrency
     stay OPEN.
-/

#print axioms UnwindEintrag
#print axioms unwindPasst
#print axioms unwindPasst_schranke
#print axioms unwindLese
#print axioms unwindLese_trifft
#print axioms unwindLese_falsch_tiefe
#print axioms unwindLese_falsch_slot
#print axioms unwindLese_falsch_rip
#print axioms ComposeUnwindTable_verbindung
#print axioms ComposeUnwindTable_verbindung_zeuge
#print axioms zeugenPasst849
#print axioms zeugenSchreibt849
#print axioms sonde_reichweite_verweigert849
#print axioms sonde_slot_verweigert849

end Gabbro.Grammatik.X86
