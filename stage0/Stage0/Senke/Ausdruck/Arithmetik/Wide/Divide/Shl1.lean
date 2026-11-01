/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Shl1.lean
  Subject:   Shift a multiword register left by one bit with a carry-in, in place.

  `V*2 + c` for `c < 2`: limb `j` is `(L_j << 1) | (L_(j-1) >> 63)` (written as a double shift by
  `1` and `62`), limb zero takes the carry word. This is the register step of restoring division,
  for the remainder register and for the dividend/quotient register alike.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Shr

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem shl1P_length (p O W TB TA TB2 j : Nat) :
    (shl1P p O W TB TA TB2 j).length = if j = 0 then 2 else 4 := by
  unfold shl1P; split <;> rfl

/-- The limbs of `2 V + c`. -/
theorem shl1_word (V c j : Nat) (hc : c < 2) (o w tb : Runner.W) (ho : o.toNat = 1) (hw : w.toNat = 62)
    (htb : tb = BitVec.ofNat 64 c) :
    lmb ((V * 2 + c : Nat) : Int) j =
      if j = 0 then (lmb (V : Int) 0 <<< (o.toNat % 64)) ||| tb
      else (lmb (V : Int) j <<< (o.toNat % 64)) ||| ((lmb (V : Int) (j - 1) >>> (o.toNat % 64)) >>> (w.toNat % 64)) := by
  have e : V * 2 + c = (V * 2) ||| c := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 1) (by omega : c < 2 ^ 1) V
    simpa [Nat.mul_comm] using this
  have e1 : V * 2 = V * 2 ^ 1 := by simp
  rw [e, e1]
  have hor : lmb (((V * 2 ^ 1 ||| c) : Nat) : Int) j = lmb ((V * 2 ^ 1 : Nat) : Int) j ||| lmb (c : Int) j :=
    lmb_or (V * 2 ^ 1) c j
  rw [hor]
  by_cases hj : j = 0
  · subst hj
    have h1 := shlBit_word V 1 0 (by omega) o o w 0 ho ho hw (by simp)
    simp only [ite_true]
    have hl : lmb (c : Int) 0 = tb := by
      rw [htb]
      apply BitVec.eq_of_toNat_eq
      rw [lmb_natCast_toNat, BitVec.toNat_ofNat]
      simp
    rw [h1, hl]
    simp [ho]
  · simp only [hj, ite_false]
    have h1 := shlBit_word V 1 j (by omega) o o w (lmb (V : Int) (j - 1)) ho ho hw (by simp [hj])
    have hl : lmb (c : Int) j = 0 := lmb_high c 1 j (by omega) (by omega)
    rw [h1, hl]
    simp [ho]

def shl1F (p O W TB j : Nat) (s : Nat → Runner.W) : Runner.W :=
  if j = 0 then (s p <<< ((s O).toNat % 64)) ||| s TB
  else (s (p + j) <<< ((s O).toNat % 64)) ||| (((s (p + (j - 1))) >>> ((s O).toNat % 64)) >>> ((s W).toNat % 64))

theorem shl1P_run (p O W TB TA TB2 j : Nat) (hT1 : TA ≠ p + j) (hT2 : TB2 ≠ p + j) (hTT : TA ≠ TB2)
    (hs : TA ≠ p + (j - 1) ∧ TB2 ≠ p + (j - 1)) (ho : TA ≠ O ∧ TB2 ≠ O) (hw : TA ≠ W ∧ TB2 ≠ W)
    (htb : TA ≠ TB) (s : Nat → Runner.W) :
    aluRun (shl1P p O W TB TA TB2 j) s (p + j) = shl1F p O W TB j s ∧
    ∀ i, i ≠ p + j → i ≠ TA → i ≠ TB2 → aluRun (shl1P p O W TB TA TB2 j) s i = s i := by
  by_cases hj : j = 0
  · subst hj
    have e : aluRun (shl1P p O W TB TA TB2 0) s =
        slotUpd (slotUpd s TA (s p <<< ((s O).toNat % 64))) p
          ((s p <<< ((s O).toNat % 64)) ||| s TB) := by
      funext i
      simp only [shl1P, ite_true, aluRun_cons, aluRun_nil, aluStep_shl, aluStep_or, slotUpd]
      have hT1' : TA ≠ p := by simpa using hT1
      by_cases h1 : i = p <;> by_cases h2 : i = TA <;>
        simp [h1, h2, hT1', Ne.symm htb]
    rw [e]
    refine ⟨?_, fun i h1 h2 h3 => ?_⟩
    · simp [slotUpd, shl1F]
    · simp only [slotUpd]
      have : i ≠ p := by simpa using h1
      simp [this, h2]
  · simp only [shl1P, hj, ite_false]
    obtain ⟨r1, r2⟩ := bitP_run 11 12 (fun a b => a <<< (b.toNat % 64)) (fun a b => a >>> (b.toNat % 64)) rfl rfl
      (by decide) (by decide) (by decide) (by decide) (p + (j - 1)) O O W TA TB2 p j hT1 hT2 hTT hs
      ho ho hw s
    exact ⟨by rw [r1]; simp [shl1F, hj], r2⟩

theorem shl1C_value (p n O W TB TA TB2 : Nat)
    (hd : p + n ≤ O ∧ p + n ≤ W ∧ p + n ≤ TB ∧ p + n ≤ TA ∧ p + n ≤ TB2 ∧ TA ≠ TB2 ∧ TA ≠ O ∧
      TA ≠ W ∧ TA ≠ TB ∧ TB2 ≠ O ∧ TB2 ≠ W ∧ TB2 ≠ TB)
    (s : Nat → Runner.W) :
    (∀ j, j < n → aluRun (shl1C p n O W TB TA TB2) s (p + j) = shl1F p O W TB j s) ∧
    (∀ i, i ≠ TA → i ≠ TB2 → (i < p ∨ p + n ≤ i) → aluRun (shl1C p n O W TB TA TB2) s i = s i) := by
  have hpw : (List.range n).reverse.Pairwise (fun j' j => ¬ (p + j' = p + j ∨ p + j' = p + (j - 1) ∨
      p + j' = O ∨ p + j' = W ∨ p + j' = TB)) := by
    rw [List.pairwise_reverse]
    refine (List.pairwise_lt_range (n := n)).imp_of_mem (fun {x y} hx hy h => ?_)
    have hy' := List.mem_range.mp hy
    omega
  have hnd : (List.range n).reverse.Nodup := hpw.imp (fun {j' j} h e => h (Or.inl (by rw [e])))
  obtain ⟨v1, v2⟩ := seqC_value (shl1P p O W TB TA TB2) (fun j s => shl1F p O W TB j s)
    (fun j i => i = p + j ∨ i = p + (j - 1) ∨ i = O ∨ i = W ∨ i = TB) (fun i => i = TA ∨ i = TB2)
    (fun j => j < n) p
    (fun j hj s => (shl1P_run p O W TB TA TB2 j (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) s).1)
    (fun j hj s i h1 h2 => (shl1P_run p O W TB TA TB2 j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) s).2 i h1 (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr h)))
    (fun j hj s s' h => by
      have h' : ∀ i, (i = p + j ∨ i = p + (j - 1) ∨ i = O ∨ i = W ∨ i = TB) → s i = s' i := h
      simp only [shl1F]
      by_cases hj0 : j = 0
      · simp only [hj0, ite_true]
        rw [h' p (by omega), h' O (by omega), h' TB (by omega)]
      · simp only [hj0, ite_false]
        rw [h' (p + j) (by omega), h' (p + (j - 1)) (by omega), h' O (by omega), h' W (by omega)])
    (fun j hj i h => by omega) (fun j hj => by omega) (List.range n).reverse
    (fun j hj => by simpa using hj) hnd hpw s
  refine ⟨fun j hj => v1 j (by simpa using hj), fun i h1 h2 h3 => v2 i (by omega) (fun j hj => ?_)⟩
  have := List.mem_range.mp (List.mem_reverse.mp hj)
  omega

/-- The register step on canonical limbs: `2 V + c` for a carry word of `0` or `1`. -/
theorem shl1C_limbs (p n O W TB TA TB2 : Nat)
    (hd : p + n ≤ O ∧ p + n ≤ W ∧ p + n ≤ TB ∧ p + n ≤ TA ∧ p + n ≤ TB2 ∧ TA ≠ TB2 ∧ TA ≠ O ∧
      TA ≠ W ∧ TA ≠ TB ∧ TB2 ≠ O ∧ TB2 ≠ W ∧ TB2 ≠ TB)
    (V c : Nat) (hc : c < 2) (s : Nat → Runner.W) (hl : ∀ j, j < n → s (p + j) = lmb (V : Int) j)
    (hO : (s O).toNat = 1) (hW : (s W).toNat = 62) (hTB : s TB = BitVec.ofNat 64 c) :
    (∀ j, j < n → aluRun (shl1C p n O W TB TA TB2) s (p + j) = lmb ((V * 2 + c : Nat) : Int) j) ∧
    (∀ i, i ≠ TA → i ≠ TB2 → (i < p ∨ p + n ≤ i) → aluRun (shl1C p n O W TB TA TB2) s i = s i) := by
  obtain ⟨v1, v2⟩ := shl1C_value p n O W TB TA TB2 hd s
  refine ⟨fun j hj => ?_, v2⟩
  rw [v1 j hj, shl1_word V c j hc (s O) (s W) (s TB) hO hW hTB]
  simp only [shl1F]
  by_cases hj0 : j = 0
  · simp only [hj0, ite_true]
    rw [show p = p + 0 from rfl, hl 0 (by omega)]
  · simp only [hj0, ite_false]
    rw [hl j hj, hl (j - 1) (by omega)]

end Gabbro.Stage0.Senke
