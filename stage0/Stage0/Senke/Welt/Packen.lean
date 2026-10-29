/-
  File:      stage0/Stage0/Senke/Welt/Packen.lean
  Subject:   A gate's buffer as words: element `8 i + j` in byte `j` of word `i` (`packV`, as the code packs it), read
             back as the code unpacks it (`byteOf`). `byteOf_packV`: with every element below 256, unpacking a packed
             word gives the element back -- the words are the elements' bytes, little-endian.
-/
import Runner.Basis.MemLemma

namespace Gabbro.Stage0.Senke

open Runner.Mem

/-- Word `i` of a buffer of `c` elements whose words are `ws`, as the code packs it: element `8 i + j` shifted into
    byte `j`. With every element below 256 these are the elements as bytes, little-endian. -/
def packV (ws : Nat → Runner.W) (c i : Nat) : Nat → Runner.W
  | 0 => 0
  | j + 1 => if 8 * i + j < c then packV ws c i j + (ws (8 * i + j) <<< (8 * j)) else packV ws c i j

/-- Element `k` of a buffer at `pa`, as the code unpacks it: byte `k % 8` of word `k / 8`. -/
def byteOf (m : Runner.Mem) (pa : Runner.W) (k : Nat) : Runner.W :=
  (((m.rd64 (pa + BitVec.ofNat 64 (8 * (k / 8)))).getD 0) >>> (8 * (k % 8))) &&& 255

/-- The word at an address, zero where none is read. -/
def wAt (m : Runner.Mem) (a : Nat) : Runner.W := (m.rd64 (BitVec.ofNat 64 a)).getD 0

/-- The value of the bytes `j < J` of word `i`. -/
def packN (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => packN a j + a j * 256 ^ j

theorem packN_lt (a : Nat → Nat) (ha : ∀ j, a j < 256) : (J : Nat) → packN a J < 256 ^ J
  | 0 => by simp [packN]
  | J + 1 => by
    have := packN_lt a ha J
    have := ha J
    simp only [packN, Nat.pow_succ]
    have : a J * 256 ^ J + 256 ^ J ≤ 256 ^ J * 256 := by
      have := Nat.mul_le_mul_right (256 ^ J) (Nat.succ_le_of_lt (ha J))
      rw [Nat.succ_mul] at this; omega
    omega

theorem packV_toNat (ws : Nat → Runner.W) (c i : Nat) (hws : ∀ k, (ws k).toNat < 256) :
    (J : Nat) → J ≤ 8 → (packV ws c i J).toNat =
      packN (fun j => if 8 * i + j < c then (ws (8 * i + j)).toNat else 0) J
  | 0, _ => rfl
  | J + 1, hJ => by
    have ih := packV_toNat ws c i hws J (by omega)
    have hb := packN_lt (fun j => if 8 * i + j < c then (ws (8 * i + j)).toNat else 0)
      (fun j => by by_cases h : 8 * i + j < c <;> simp [h, hws]) J
    have hp : 256 ^ J ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [packV, packN]
    split
    · next hc =>
      have hw := hws (8 * i + J)
      have hsh : (ws (8 * i + J) <<< (8 * J)).toNat = (ws (8 * i + J)).toNat * 256 ^ J := by
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ (8 * J) = 256 ^ J by rw [Nat.pow_mul]]
        apply Nat.mod_eq_of_lt
        have : (ws (8 * i + J)).toNat * 256 ^ J < 256 * 256 ^ 7 :=
          Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hw (Nat.pow_pos (by decide)))
            (Nat.mul_le_mul_left _ hp)
        have : 256 * 256 ^ 7 = 2 ^ 64 := by decide
        omega
      rw [BitVec.toNat_add, ih, hsh]
      try dsimp only
      try rw [if_pos hc]
      apply Nat.mod_eq_of_lt
      have : (ws (8 * i + J)).toNat * 256 ^ J + 256 ^ J ≤ 256 * 256 ^ J := by
        have := Nat.mul_le_mul_right (256 ^ J) (Nat.succ_le_of_lt hw)
        rw [Nat.succ_mul] at this; omega
      have : 256 * 256 ^ J ≤ 256 * 256 ^ 7 := Nat.mul_le_mul_left _ hp
      have : 256 * 256 ^ 7 = 2 ^ 64 := by decide
      omega
    · next hc => rw [ih]; try dsimp only
                 try rw [if_neg hc]
                 simp

theorem packN8_digit (a : Nat → Nat) (ha : ∀ j, a j < 256) (j : Nat) (hj : j < 8) :
    packN a 8 / 2 ^ (8 * j) % 256 = a j := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3
  have h4 := ha 4; have h5 := ha 5; have h6 := ha 6; have h7 := ha 7
  simp only [packN]
  match j, hj with
  | 0, _ => simp; omega
  | 1, _ => simp; omega
  | 2, _ => simp; omega
  | 3, _ => simp; omega
  | 4, _ => simp; omega
  | 5, _ => simp; omega
  | 6, _ => simp; omega
  | 7, _ => simp; omega

/-- **Unpacking a packed word**: element `8 i + j` comes back. -/
theorem byte_packV (ws : Nat → Runner.W) (c i j : Nat) (hj : j < 8) (hws : ∀ k, (ws k).toNat < 256) :
    ((packV ws c i 8) >>> (8 * j)) &&& 255 = if 8 * i + j < c then ws (8 * i + j) else 0 := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (255 : Runner.W) = BitVec.ofNat 64 (2 ^ 8 - 1) := rfl
  rw [h255, BitVec.toNat_and, BitVec.toNat_ushiftRight, packV_toNat ws c i hws 8 (Nat.le_refl _),
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 ^ 8 - 1) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    packN8_digit _ (fun j => by by_cases h : 8 * i + j < c <;> simp [h, hws]) j hj]
  by_cases h : 8 * i + j < c <;> simp [h]

end Gabbro.Stage0.Senke
