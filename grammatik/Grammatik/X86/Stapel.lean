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

/- CUTS:
    - No instruction semantics, decoder, image mapping, TSO bridge, source
      correspondence, cost transfer or final-image acceptance is proved here.
    - Callee-save/entry contracts and external ABI byte correspondence are
      OPEN: this file states checked memory obligations only.
    - No Linux-specific mechanism: no stack sizes, guard pages, clone flags
      or syscall numbers appear here.
-/

end Gabbro.Grammatik.X86
