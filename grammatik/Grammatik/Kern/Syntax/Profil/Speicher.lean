/- C13: the checked layout derivation of the source objects `sizeof` and `aligned` talk about (lane C13,
   `IR-COMPILATION-LANES.md`, "Layout sugar").

   The size of a source object is the size of its DECLARED storage, derived here from the storage type the declaration
   chose (`u8 .. u64`, `bool`, `[T; N]`): never `8 * count` of a runner's column representation
   (`stage0/Stage0/Senke/Welt/Lay`), and never the width the range of a type happens to fit. `SpTy.passt` is the
   check that a storage type carries a checked source type (`Ty`): the declared range lies in the storage word, the
   array has the declared length. `sizeof` lowers to `Expr.lit (SpTy.bytes t)` only for a resolved, valid storage
   type; every unsized or unresolved case is refused by the exporter.

   `ausrichtung_dvd_bytes` and `spalte_ausgerichtet` are the facts a layout correspondence consumes: the address of
   element `k` of a column of storage type `t` at an `ausrichtung`-aligned base is `ausrichtung`-aligned, so the
   numeric `aligned(x, N)` of an element (`x mod N = 0`, `N` dividing the alignment) is decided by the base alone.
   Capability alignment is NOT derived here: `Ty.ptr` is a capability, not an integer address. -/

module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-- The declared storage type of a source object: a word of `w` bits (`8`, `16`, `32`, `64`), a truth value (one
    byte) or a fixed array of `n` elements of a storage type. -/
inductive SpTy where
  | wort (w : Nat)
  | wahr
  | feld (t : SpTy) (n : Nat)

/-- The declared size in bytes. -/
def SpTy.bytes : SpTy → Nat
  | .wort w => w / 8
  | .wahr => 1
  | .feld t n => n * t.bytes

/-- The alignment in bytes: the natural alignment of the element word. -/
def SpTy.ausrichtung : SpTy → Nat
  | .wort w => w / 8
  | .wahr => 1
  | .feld t _ => t.ausrichtung

/-- A valid storage type: the words are the standard widths. -/
def SpTy.gueltig : SpTy → Bool
  | .wort w => w == 8 || w == 16 || w == 32 || w == 64
  | .wahr => true
  | .feld t _ => t.gueltig

/-- The storage type carries the checked source type: a word holds the whole range (unsigned or two's-complement
    signed), a truth value is a `bool`, an array has its declared length and a carrying element. -/
def SpTy.passt : SpTy → Ty → Bool
  | .wort w, .int lo hi =>
    (decide (0 ≤ lo) && decide (hi < (2 : Int) ^ w)) ||
      (decide (-((2 : Int) ^ (w - 1)) ≤ lo) && decide (hi < (2 : Int) ^ (w - 1)))
  | .wahr, .bool => true
  | .feld t n, .arr τ m => n == m && t.passt τ
  | _, _ => false

/-- The size of an array is the number of elements times the element size. -/
theorem SpTy.feld_bytes (t : SpTy) (n : Nat) : (SpTy.feld t n).bytes = n * t.bytes := rfl

/-- The alignment divides the size, so the elements of an array stay aligned. -/
theorem SpTy.ausrichtung_dvd_bytes : ∀ t : SpTy, t.ausrichtung ∣ t.bytes
  | .wort _ => Nat.dvd_refl _
  | .wahr => Nat.dvd_refl _
  | .feld t n => Nat.dvd_trans (SpTy.ausrichtung_dvd_bytes t) (Nat.dvd_mul_left _ _)

/-- The offset of element `k` of a column (or of an array) of storage type `t` is a multiple of its alignment. -/
theorem SpTy.elem_ausgerichtet (t : SpTy) (k : Nat) : t.ausrichtung ∣ k * t.bytes :=
  Nat.dvd_trans (SpTy.ausrichtung_dvd_bytes t) (Nat.dvd_mul_left _ _)

/-- At an aligned base every element of a column is aligned: the layout fact `aligned(x, N)` of an element rests on
    (a divisor `N` of the alignment divides the address too). -/
theorem SpTy.spalte_ausgerichtet (t : SpTy) (base k N : Nat) (hb : t.ausrichtung ∣ base) (hN : N ∣ t.ausrichtung) :
    N ∣ base + k * t.bytes :=
  Nat.dvd_add (Nat.dvd_trans hN hb) (Nat.dvd_trans hN (SpTy.elem_ausgerichtet t k))

/-- A valid word has a positive size. -/
theorem SpTy.wort_bytes_pos (w : Nat) (h : (SpTy.wort w).gueltig = true) : 0 < (SpTy.wort w).bytes := by
  simp only [SpTy.gueltig, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h <;> decide

/-- Witnesses: `u32` is four bytes, `[u16; 5]` ten, an array of `[u8; 4]` four-byte rows 12 bytes. -/
theorem SpTy.bytes_zeuge :
    (SpTy.wort 32).bytes = 4 ∧ (SpTy.feld (.wort 16) 5).bytes = 10 ∧
    (SpTy.feld (.feld (.wort 8) 4) 3).bytes = 12 := ⟨rfl, rfl, rfl⟩

/-- Witnesses of the check: `u8 in 0 .. 15` is carried by one byte, `i16 in -3 .. 3` by two, `u8 in 0 .. 300` by no
    byte, a four-element array by `[u8; 4]` and not by `[u8; 3]`. -/
theorem SpTy.passt_zeuge :
    (SpTy.wort 8).passt (.int 0 15) = true ∧ (SpTy.wort 16).passt (.int (-3) 3) = true ∧
    (SpTy.wort 8).passt (.int 0 300) = false ∧
    (SpTy.feld (.wort 8) 4).passt (.arr (.int 0 255) 4) = true ∧
    (SpTy.feld (.wort 8) 4).passt (.arr (.int 0 255) 3) = false := by decide

end Gabbro.Grammatik
