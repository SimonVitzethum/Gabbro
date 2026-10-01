/-
  Checked stack frames and ABI memory obligations (lane 309).

  Frame extents, 16-byte call-boundary alignment, spill/callee-save/stack-arg
  layout and argument/result carriage over the canonical `Speicher` of
  `Grammatik.X86.Typen`/`Speicher`, using the shared `write64`/`read64`.
  No second register, instruction or memory model is created here; `schritt`
  semantics is never duplicated. Callee-save/entry contracts and external
  ABI byte correspondence stay OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A checked stack frame: byte base plus depth, over canonical addresses. -/
structure Rahmen where
  basis : Nat
  tiefe : Nat
  deriving DecidableEq, Repr

/-- Top (post-frame) address as a natural number. -/
def Rahmen.spitzeNat (r : Rahmen) : Nat := r.basis + r.tiefe

/-- Word-slot count of a frame. -/
def Rahmen.schlitzZahl (r : Rahmen) : Nat := r.tiefe / 8

/-- Byte address of word slot `idx`, as a natural number. -/
def Rahmen.schlitzNat (r : Rahmen) (idx : Nat) : Nat := r.basis + idx * 8

/-- Byte address of word slot `idx` as a machine address. -/
def Rahmen.schlitzAddr (r : Rahmen) (idx : Nat) : Adresse :=
  BitVec.ofNat 64 (r.schlitzNat idx)

/-- Frame top as a machine word (the call-boundary stack pointer). -/
def Rahmen.spitzeWort (r : Rahmen) : Wort :=
  BitVec.ofNat 64 r.spitzeNat

/-- 16-byte call-boundary alignment of a machine address. -/
def ausgerichtet16 (a : Adresse) : Bool := decide (a.toNat % 16 = 0)

/-! ## 1. Checked extents and call-boundary alignment. -/

/-- Checked frame extent: nonzero depth, a multiple of 16 (alignment is
    preserved), the whole frame inside 64 bits, and a 16-aligned base. -/
def rahmenOk (r : Rahmen) : Bool :=
  decide (0 < r.tiefe ∧ r.tiefe % 16 = 0 ∧ r.spitzeNat ≤ 2 ^ 64 ∧
    r.basis % 16 = 0)

/-- An in-bounds slot ends at or before the frame top. -/
theorem schlitzNat_schranke (r : Rahmen) (idx : Nat)
    (hi : idx < r.schlitzZahl) :
    r.schlitzNat idx + 8 ≤ r.spitzeNat := by
  unfold Rahmen.schlitzZahl at hi
  unfold Rahmen.schlitzNat Rahmen.spitzeNat
  omega

/-- An in-bounds slot address reads back as its natural number. -/
theorem schlitz_toNat (r : Rahmen) (idx : Nat)
    (hle : r.spitzeNat ≤ 2 ^ 64) (hi : idx < r.schlitzZahl) :
    (r.schlitzAddr idx).toNat = r.schlitzNat idx := by
  have hsch := schlitzNat_schranke r idx hi
  unfold Rahmen.schlitzAddr Rahmen.schlitzNat Rahmen.spitzeNat at *
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

/-- ALIGNMENT: a 16-aligned base with a multiple-of-16 depth gives a
    16-aligned call-boundary top. Uses the depth and the base. -/
theorem spitze_ausgerichtet (r : Rahmen)
    (h16 : r.tiefe % 16 = 0) (hb : r.basis % 16 = 0) :
    ausgerichtet16 r.spitzeWort = true := by
  unfold ausgerichtet16 Rahmen.spitzeWort Rahmen.spitzeNat
  simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
  have hN : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  rw [hN]
  omega

/-! ## 2. Checked frame save/restore over the shared byte memory. -/

/-- Checked word save into frame slot `idx`: refused outside the frame. -/
def sichereWort (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) : Option Speicher :=
  if idx < r.schlitzZahl then write64 m (r.schlitzAddr idx) v else none

/-- Checked word load from frame slot `idx`: refused outside the frame. -/
def ladeWort (m : Speicher) (r : Rahmen) (idx : Nat) : Option Wort :=
  if idx < r.schlitzZahl then read64 m (r.schlitzAddr idx) else none

/-- ROUND-TRIP: a saved word loads back through a readable slot. Needs
    readability besides writability, since the permissions are independent. -/
theorem sichere_lade_rundreise (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (hrd : lesbar8 m (r.schlitzAddr idx) = true) :
    ladeWort m' r idx = some v := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  unfold ladeWort
  rw [if_pos hb]
  exact read64_nach_write64 m m' (r.schlitzAddr idx) v hwr hrd

/-- BOUNDS REFUSAL: a slot past the frame saves nothing. -/
theorem sichereWort_ausserhalb (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (h : r.schlitzZahl ≤ idx) :
    sichereWort m r idx v = none := by
  unfold sichereWort
  rw [if_neg (Nat.not_lt.mpr h)]

/-- PERMISSION REFUSAL: a write-protected slot saves nothing. -/
theorem sichereWort_verweigert (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl)
    (h : schreibbar8 m (r.schlitzAddr idx) = false) :
    sichereWort m r idx v = none := by
  unfold sichereWort
  rw [if_pos hb]
  exact write64_verweigert m (r.schlitzAddr idx) v h

/-- A save preserves every permission: only bytes change. -/
theorem sichereWort_erhaelt_berechtigungen (m m' : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  exact write64_erhaelt_berechtigungen m (r.schlitzAddr idx) v m' hwr

/-- A save changes nothing outside its eight slot bytes. -/
theorem sichereWort_rahmen (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (x : Adresse) (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k) :
    m'.bytes x = m.bytes x := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  exact write64_rahmen m m' (r.schlitzAddr idx) x v hwr haussen

/-- A load from a disjoint slot survives a save elsewhere. -/
theorem ladeWort_rahmen (m m' : Speicher) (r : Rahmen) (idx j : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl) (hbj : j < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (hdis : Disjunkt (r.schlitzAddr idx) (r.schlitzAddr j)) :
    ladeWort m' r j = ladeWort m r j := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  unfold ladeWort
  rw [if_pos hbj, if_pos hbj]
  exact read64_rahmen m m' (r.schlitzAddr idx) (r.schlitzAddr j) v
    hwr hdis

/-! ## 3. Fresh and disjoint slots: no slot shares a byte with another. -/

/-- Two slots of one frame are footprint-disjoint. Needs both bounds, the
    inequality and the frame bound. -/
theorem schlitz_disjunkt (r : Rahmen) (i j : Nat)
    (hi : i < r.schlitzZahl) (hj : j < r.schlitzZahl)
    (hne : i ≠ j) (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr j) := by
  have hsi := schlitzNat_schranke r i hi
  have hsj := schlitzNat_schranke r j hj
  have hti := schlitz_toNat r i hle hi
  have htj := schlitz_toNat r j hle hj
  have hOi : OhneUmbruch (r.schlitzAddr i) := by
    unfold OhneUmbruch
    omega
  have hOj : OhneUmbruch (r.schlitzAddr j) := by
    unfold OhneUmbruch
    omega
  have hord : (r.schlitzAddr i).toNat + 8 ≤ (r.schlitzAddr j).toNat ∨
      (r.schlitzAddr j).toNat + 8 ≤ (r.schlitzAddr i).toNat := by
    rw [hti, htj]
    unfold Rahmen.schlitzNat
    by_cases hlt : i < j
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact disjunkt_von_intervallen _ _ hOi hOj hord

/-- Two frames are separate: every slot pair is footprint-disjoint. -/
def RahmenGetrennt (r₁ r₂ : Rahmen) : Prop :=
  ∀ i j : Nat, i < r₁.schlitzZahl → j < r₂.schlitzZahl →
    Disjunkt (r₁.schlitzAddr i) (r₂.schlitzAddr j)

/-- Nat-interval separation gives frame separation: caller and callee
    frames share no byte. Uses both bounds and the interval order. -/
theorem rahmen_getrennt_von_intervallen (r₁ r₂ : Rahmen)
    (hle₁ : r₁.spitzeNat ≤ 2 ^ 64) (hle₂ : r₂.spitzeNat ≤ 2 ^ 64)
    (h : r₁.spitzeNat ≤ r₂.basis ∨ r₂.spitzeNat ≤ r₁.basis) :
    RahmenGetrennt r₁ r₂ := by
  intro i j hi hj
  have hti := schlitz_toNat r₁ i hle₁ hi
  have htj := schlitz_toNat r₂ j hle₂ hj
  have hsi := schlitzNat_schranke r₁ i hi
  have hsj := schlitzNat_schranke r₂ j hj
  have hOi : OhneUmbruch (r₁.schlitzAddr i) := by
    unfold OhneUmbruch
    omega
  have hOj : OhneUmbruch (r₂.schlitzAddr j) := by
    unfold OhneUmbruch
    omega
  have hord : (r₁.schlitzAddr i).toNat + 8 ≤ (r₂.schlitzAddr j).toNat ∨
      (r₂.schlitzAddr j).toNat + 8 ≤ (r₁.schlitzAddr i).toNat := by
    rw [hti, htj]
    unfold Rahmen.schlitzNat at hsi hsj ⊢
    unfold Rahmen.spitzeNat at hsi hsj h
    omega
  exact disjunkt_von_intervallen _ _ hOi hOj hord

/-! ## 4. Frame layout: spills, callee-save words, stack arguments. -/

/-- Frame layout: spill slots, callee-save slots, stack-passed argument words,
    laid out back to back from the frame base. -/
structure Belegung where
  spill : Nat
  gerettet : Nat
  stapelArgs : Nat
  deriving DecidableEq, Repr

/-- Words the layout needs. -/
def Belegung.braucht (b : Belegung) : Nat :=
  b.spill + b.gerettet + b.stapelArgs

/-- The layout fits the frame. -/
def Belegung.passt (b : Belegung) (r : Rahmen) : Bool :=
  decide (b.braucht * 8 ≤ r.tiefe)

/-- Slot index of the `i`-th callee-save word. Spill words live at the
    bare indices `i` below `b.spill`, so they need no offset function. -/
def Belegung.gerettetIdx (b : Belegung) (i : Nat) : Nat := b.spill + i

/-- Slot index of the `i`-th stack-passed argument word. -/
def Belegung.stapelArgIdx (b : Belegung) (i : Nat) : Nat :=
  b.spill + b.gerettet + i

/-- Two index ranges that do not overlap name disjoint slots. The generic
    shape behind spill/callee-save/argument separation. -/
theorem bereich_getrennt (r : Rahmen) (a₁ e₁ a₂ e₂ i j : Nat)
    (h₁ : a₁ ≤ i) (h₁' : i < e₁) (h₂ : a₂ ≤ j) (h₂' : j < e₂)
    (hsep : e₁ ≤ a₂ ∨ e₂ ≤ a₁)
    (hb₁ : e₁ ≤ r.schlitzZahl) (hb₂ : e₂ ≤ r.schlitzZahl)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr j) := by
  have hbi : i < r.schlitzZahl := by omega
  have hbj : j < r.schlitzZahl := by omega
  have hne : i ≠ j := by omega
  exact schlitz_disjunkt r i j hbi hbj hne hle

/-- A spill slot shares no byte with a callee-save slot. -/
theorem spill_gerettet_getrennt (b : Belegung) (r : Rahmen) (i j : Nat)
    (hi : i < b.spill) (hj : j < b.gerettet)
    (hpasst : b.braucht * 8 ≤ r.tiefe)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr (b.gerettetIdx j)) := by
  unfold Belegung.gerettetIdx Belegung.braucht at *
  have hb : b.spill + b.gerettet ≤ r.schlitzZahl := by
    unfold Rahmen.schlitzZahl
    omega
  exact bereich_getrennt r 0 b.spill b.spill (b.spill + b.gerettet) i
    (b.spill + j) (by omega) hi (by omega) (by omega) (Or.inl (by omega))
    (by omega) hb hle

/-- A callee-save slot shares no byte with a stack-argument slot. -/
theorem gerettet_stapel_getrennt (b : Belegung) (r : Rahmen) (i j : Nat)
    (hi : i < b.gerettet) (hj : j < b.stapelArgs)
    (hpasst : b.braucht * 8 ≤ r.tiefe)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr (b.gerettetIdx i))
      (r.schlitzAddr (b.stapelArgIdx j)) := by
  unfold Belegung.gerettetIdx Belegung.stapelArgIdx Belegung.braucht at *
  have hb : b.spill + b.gerettet + b.stapelArgs ≤ r.schlitzZahl := by
    unfold Rahmen.schlitzZahl
    omega
  exact bereich_getrennt r b.spill (b.spill + b.gerettet)
    (b.spill + b.gerettet) (b.spill + b.gerettet + b.stapelArgs)
    (b.spill + i) (b.spill + b.gerettet + j)
    (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (by omega) hb hle

/- CUTS:
    - No instruction semantics, decoder, image mapping, TSO bridge, source
      correspondence, cost transfer or final-image acceptance is proved here.
    - Callee-save/entry contracts and external ABI byte correspondence are
      OPEN: this file states checked memory obligations only.
    - No Linux-specific mechanism: no stack sizes, guard pages, clone flags
      or syscall numbers appear here.
-/

end Gabbro.Grammatik.X86
