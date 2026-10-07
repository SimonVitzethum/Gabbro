/-
  Darstellung -- the MINIMAL-WIDTH / PACKED data layout of a ranged value, as semantics
  (SPRACHE-EFFIZIENZ, Sonnet agent E, 2026-10-07).

  Why this file exists.  `messung/SPRACHE-EFFIZIENZ.md` measured that the language stores a
  `u32 in 0 .. 3`, a `bool`, an `index into T` or a string length word at the width of the
  declared word, not of the range (C backend: 4, 1, 4 and 4 bytes where 2 bits, 1 bit, 1 byte
  and 1 byte carry the same facts).  The checker already proves every value lies in its range
  (M1), so the range -- not the word -- is what a representation must hold.  The direct
  AArch64 compiler (planned path; the C backend is LEGACY) needs this as a THEOREM before it
  chooses a layout: this file is that theorem, over every range, with no program named.

  Contents (all over `Int` ranges, nothing but `Init`):
  * `Bereich.bits`      the number of bits `ceil(log2 (hi - lo + 1))` a range needs;
  * `enc` / `dec`       offset encoding `v - lo`; `dec_enc` round trip; `enc_lt` fits `bits`;
  * `bits_minimal`      one bit fewer cannot hold the range (the layout is not wasteful);
  * `Zelle.bytes`       the narrowest of 1/2/4/8 bytes; `bytes_fits`, `bytes_minimal`;
  * `packWort`/`feld`   a packed word of fields: reading a field returns exactly what was
                        written, other fields are untouched (`feld_pack`, `feld_pack_andere`);
  * `packBytes`         `n` cells of `b` bits occupy `ceil(n*b/8)` bytes, never more than the
                        byte-per-cell layout (`packBytes_le_zellen`).
  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Grammatik.Speichermodell.Darstellung

/-- Number of values of the range `lo .. hi` (`0` when empty). -/
def anzahl (lo hi : Int) : Nat := (hi - lo + 1).toNat

/-- Bits of the offset encoding: the least `b` with `hi - lo + 1 <= 2^b`
    (`0` for a one-point range: the value is a constant and needs no storage). -/
def bits (lo hi : Int) : Nat := Nat.log2 (anzahl lo hi - 1) + (if anzahl lo hi ≤ 1 then 0 else 1)

/-- Offset encoding of a value of the range. -/
def enc (lo v : Int) : Nat := (v - lo).toNat

/-- Decoding. -/
def dec (lo : Int) (n : Nat) : Int := (n : Int) + lo

theorem dec_enc (lo hi v : Int) (h1 : lo ≤ v) (_h2 : v ≤ hi) : dec lo (enc lo v) = v := by
  unfold dec enc; omega

theorem enc_dec (lo : Int) (n : Nat) : enc lo (dec lo n) = n := by
  unfold dec enc; omega

theorem enc_lt_anzahl (lo hi v : Int) (h1 : lo ≤ v) (h2 : v ≤ hi) : enc lo v < anzahl lo hi := by
  unfold enc anzahl; omega

theorem anzahl_le_two_pow_bits (lo hi : Int) : anzahl lo hi ≤ 2 ^ bits lo hi := by
  unfold bits
  by_cases h : anzahl lo hi ≤ 1
  · simp only [h, if_true, Nat.add_zero]
    have : 0 < 2 ^ Nat.log2 (anzahl lo hi - 1) := Nat.two_pow_pos _
    omega
  · simp only [h, if_false]
    have h' : anzahl lo hi - 1 ≠ 0 := by omega
    have := Nat.lt_log2_self (n := anzahl lo hi - 1)
    rw [Nat.pow_succ]
    omega

/-- **The encoding of every value in the range fits in `bits lo hi` bits.** -/
theorem enc_lt_two_pow (lo hi v : Int) (h1 : lo ≤ v) (h2 : v ≤ hi) :
    enc lo v < 2 ^ bits lo hi :=
  Nat.lt_of_lt_of_le (enc_lt_anzahl lo hi v h1 h2) (anzahl_le_two_pow_bits lo hi)

/-- **Minimality: no width below `bits lo hi` holds the range.**  Any `b` with
    `2^b >= number of values` is at least `bits lo hi`; the layout wastes nothing below the
    bit. -/
theorem bits_minimal (lo hi : Int) (b : Nat) (hb : anzahl lo hi ≤ 2 ^ b) :
    bits lo hi ≤ b := by
  unfold bits
  by_cases h1 : anzahl lo hi ≤ 1
  · simp only [h1, if_true]; have : Nat.log2 (anzahl lo hi - 1) = 0 := by
      have : anzahl lo hi - 1 = 0 := by omega
      rw [this]; rfl
    omega
  · simp only [h1, if_false]
    have hne : anzahl lo hi - 1 ≠ 0 := by omega
    have : Nat.log2 (anzahl lo hi - 1) < b := by
      rw [Nat.log2_lt hne]
      omega
    omega

/-! ### Whole bytes: the narrowest standard cell -/

/-- Bytes of the narrowest standard cell (1, 2, 4, 8) that holds `bits` bits. -/
def zellBytes (b : Nat) : Nat := if b ≤ 8 then 1 else if b ≤ 16 then 2 else if b ≤ 32 then 4 else 8

theorem zellBytes_fits (b : Nat) (h : b ≤ 64) : b ≤ 8 * zellBytes b := by
  unfold zellBytes; split <;> try omega
  split <;> try omega
  split <;> omega

theorem zellBytes_minimal (b : Nat) : zellBytes b ≤ 1 ∨ 8 * (zellBytes b / 2) < b := by
  unfold zellBytes
  by_cases h1 : b ≤ 8
  · simp [h1]
  · right
    by_cases h2 : b ≤ 16
    · simp [h1, h2]; omega
    · by_cases h3 : b ≤ 32
      · simp [h1, h2, h3]; omega
      · simp [h1, h2, h3]; omega

/-- Narrow storage of a ranged value, in bytes. -/
def schmalBytes (lo hi : Int) : Nat := zellBytes (bits lo hi)

/-- The C/legacy rule "the declared word" for comparison: a value of `u32 in lo .. hi`
    stores 4 bytes whatever the range. -/
def wortBytes (w : Nat) : Nat := w

/-- **The narrow cell never costs more than the declared word it replaces**, whenever the
    range lies in that word (`w` bytes, unsigned). -/
theorem schmal_le_wort (lo hi : Int) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (h0 : 0 ≤ lo) (hh : hi < 2 ^ (8 * w)) :
    schmalBytes lo hi ≤ wortBytes w := by
  unfold schmalBytes wortBytes
  have hz : anzahl lo hi ≤ 2 ^ (8 * w) := by
    unfold anzahl
    have : ((2 ^ (8 * w) : Nat) : Int) = (2 : Int) ^ (8 * w) := by simp
    have hp : (0 : Int) < (2 : Int) ^ (8 * w) := by exact_mod_cast Nat.two_pow_pos (8 * w)
    omega
  have hb := bits_minimal lo hi (8 * w) hz
  unfold zellBytes
  rcases hw with rfl | rfl | rfl | rfl <;> split <;> try omega
  all_goals (split <;> try omega)
  all_goals (split <;> omega)

/-! ### Packed fields in one word -/

/-- Read the `b`-bit field at bit offset `k` of word `w`. -/
def feld (w k b : Nat) : Nat := (w / 2 ^ k) % 2 ^ b

/-- Write `v` into the `b`-bit field at offset `k` (low `k` bits and bits above `k+b` are kept). -/
def setze (w k b v : Nat) : Nat :=
  w % 2 ^ k + 2 ^ k * (v % 2 ^ b + 2 ^ b * (w / 2 ^ (k + b)))

/-- A word built from a low part `r`, a field `v` and a high part `h`. -/
def pack (r k v b h : Nat) : Nat := r + 2 ^ k * (v + 2 ^ b * h)

theorem feld_pack (r k v b h : Nat) (hr : r < 2 ^ k) (hv : v < 2 ^ b) :
    feld (pack r k v b h) k b = v := by
  unfold feld pack
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have h1 : (r + 2 ^ k * (v + 2 ^ b * h)) / 2 ^ k = v + 2 ^ b * h := by
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- **Writing then reading a packed field returns exactly the value written** (for a value in
    the field's width), whatever the word held before. -/
theorem feld_setze (w k b v : Nat) (hv : v < 2 ^ b) : feld (setze w k b v) k b = v := by
  unfold setze
  have hr : w % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have := feld_pack (w % 2 ^ k) k (v % 2 ^ b) b (w / 2 ^ (k + b)) hr (Nat.mod_lt _ (Nat.two_pow_pos b))
  unfold pack at this
  rw [this, Nat.mod_eq_of_lt hv]

/-- The bits below the field are untouched by a write. -/
theorem setze_niedrig (w k b v : Nat) : setze w k b v % 2 ^ k = w % 2 ^ k := by
  unfold setze
  rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- The bits above the field are untouched by a write. -/
theorem setze_hoch (w k b v : Nat) :
    setze w k b v / 2 ^ (k + b) = w / 2 ^ (k + b) := by
  unfold setze
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hr : w % 2 ^ k < 2 ^ k := Nat.mod_lt _ hk
  have e : 2 ^ (k + b) = 2 ^ k * 2 ^ b := Nat.pow_add 2 k b
  have h2 : 2 ^ k * (v % 2 ^ b + 1) ≤ 2 ^ k * 2 ^ b :=
    Nat.mul_le_mul_left _ (Nat.mod_lt v (Nat.two_pow_pos b))
  rw [Nat.mul_add, Nat.mul_one] at h2
  have hm : 0 < 2 ^ k * 2 ^ b := by rw [← e]; exact Nat.two_pow_pos _
  have hform : w % 2 ^ k + 2 ^ k * (v % 2 ^ b + 2 ^ b * (w / 2 ^ (k + b)))
      = (w % 2 ^ k + 2 ^ k * (v % 2 ^ b)) + 2 ^ (k + b) * (w / 2 ^ (k + b)) := by
    rw [e, Nat.mul_add, Nat.mul_assoc]; omega
  rw [hform]
  have ha : w % 2 ^ k + 2 ^ k * (v % 2 ^ b) < 2 ^ (k + b) := by rw [e]; omega
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt ha, Nat.zero_add]

/-! ### Arrays of packed cells -/

/-- Bytes of `n` cells of `b` bits each, packed without padding between cells. -/
def packBytes (n b : Nat) : Nat := (n * b + 7) / 8

/-- Bytes of `n` cells of whole-byte width `c`. -/
def zellenBytes (n c : Nat) : Nat := n * c

/-- **A packed array never occupies more than the cell-per-element layout**, as soon as
    the cell is at least as wide as the packed width. -/
theorem packBytes_le_zellen (n b c : Nat) (h : b ≤ 8 * c) :
    packBytes n b ≤ zellenBytes n c := by
  unfold packBytes zellenBytes
  have : n * b ≤ n * (8 * c) := Nat.mul_le_mul_left _ h
  have h8 : n * (8 * c) = 8 * (n * c) := by rw [← Nat.mul_assoc, Nat.mul_comm n 8, Nat.mul_assoc]
  omega

/-- Sanity numbers from the audit (`messung/SPRACHE-EFFIZIENZ.md`): a `[u2; 1000]`, a
    `[bool; 4096]` and a `[[u32 in 0 .. 1; 64]; 64]`. -/
example : packBytes 1000 2 = 250 := by decide
example : packBytes 4096 1 = 512 := by decide
example : packBytes (64 * 64) (bits 0 1) = 512 := by decide
example : schmalBytes 0 3 = 1 := by decide
example : schmalBytes 0 100 = 1 := by decide
example : schmalBytes 0 65535 = 2 := by decide
example : schmalBytes 0 65536 = 4 := by decide
example : bits 0 3 = 2 := by decide
example : bits 0 1 = 1 := by decide
example : bits 5 5 = 0 := by decide
example : bits (-4) 3 = 3 := by decide

end Grammatik.Speichermodell.Darstellung
