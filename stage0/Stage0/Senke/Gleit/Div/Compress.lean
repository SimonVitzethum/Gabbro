/- Prepare the exact 109-bit numerator for the shared restoring divider. -/
module
public import Stage0.Senke.Gleit.Div.Code
public import Stage0.Senke.Gleit.Mul.Normalize
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Retain the shifted low limb, the shifted high limb, and the divisor.
    The two source producers are pure and may be reread before the loop.
    The 26-word suffix ceiling is the shared two-limb divider's exact
    reservation, including its comparison and carry temporaries. -/
def softDivQuotientL (d : Nat) (a b : Nat → Option (List II × Nat)) (k : Nat) :
    Option (List II × Nat) := do
  let low ← wordK 11 d (a d) (Int.ofNat k)
  let high ← wordK 12 (d + 1) (a (d + 1)) (Int.ofNat (64 - k))
  let divisor ← b (d + 2)
  pure (low.1 ++ (high.1 ++ (divisor.1 ++ softDivQuotientC d)),
    max low.2 (max high.2 (max divisor.2 (d + 26))))

/-- Exact low and high words of the left-shifted significand. -/
theorem softDivQuotient_limbs (a k : Nat) (ab : a < 2 ^ 64) (kb : k ≤ 64) :
    (BitVec.ofNat 64 a <<< k) = BitVec.ofNat 64 (a * 2 ^ k) ∧
      (BitVec.ofNat 64 a >>> (64 - k)) = BitVec.ofNat 64 (a * 2 ^ k / 2 ^ 64) := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ab,
      Nat.shiftLeft_eq]
  · have power : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have cancel : a * 2 ^ k / 2 ^ 64 = a / 2 ^ (64 - k) := by
      rw [power, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ab,
      Nat.shiftRight_eq_div_pow, cancel]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ab)).symm

/-- Simulation of the prepared numerator and restoring loop. The theorem
    needs only integer bounds, and does not assume an IEEE result class. -/
theorem softDivQuotientL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {an bn k : Nat}
    (ha : WordCode (L := L) ρ W a (BitVec.ofNat 64 an))
    (hb : WordCode (L := L) ρ W b (BitVec.ofNat 64 bn))
    (ab : an < 2 ^ 64) (bp : 0 < bn) (bb : bn < 2 ^ 64)
    (count : k = 55 ∨ k = 56) (nb : an * 2 ^ k < 2 ^ 128) :
    WordCode (L := L) ρ W (fun d => softDivQuotientL d a b k)
      (BitVec.ofNat 64 (softDivJam (an * 2 ^ k) bn)) := by
  have literal : lit32 (Int.ofNat k) = true := by rcases count with rfl | rfl <;> decide
  have highLiteral : lit32 (Int.ofNat (64 - k)) = true := by rcases count with rfl | rfl <;> decide
  have shift : (BitVec.ofInt 64 (Int.ofNat k)).toNat % 64 = k := by
    rcases count with rfl | rfl <;> decide
  have highShift : (BitVec.ofInt 64 (Int.ofNat (64 - k))).toNat % 64 = 64 - k := by
    rcases count with rfl | rfl <;> decide
  have limbs := softDivQuotient_limbs an k ab (by rcases count with rfl | rfl <;> decide)
  have lowCode := WordCode.bin ha (WordCode.const _ literal)
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  rw [shift, limbs.1] at lowCode
  have highCode := WordCode.bin ha (WordCode.const _ highLiteral)
    (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
  rw [highShift, limbs.2] at highCode
  intro fp K d code top hc ht m pc hp
  simp only [softDivQuotientL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
  obtain ⟨⟨cl, tl⟩, hl, ⟨ch, th⟩, hh, ⟨cb, tb⟩, hd, hc⟩ := hc
  cases hc
  obtain ⟨m1, s1, a1, wl, rl, el⟩ := lowCode hl (by omega) m pc hp.left
  subst wl
  have pre1 := hp.next a1 (show d ≤ d + 1 by omega) (by omega)
  obtain ⟨m2, s2, a2, wh, rh, eh⟩ := highCode hh (by omega) m1 _ pre1.left
  subst wh
  have pre2 := pre1.next a2 (show d + 1 ≤ d + 2 by omega) (by omega)
  have low2 := slotRead_agree pre1.frame a2 (show d < d + 1 by omega) (by omega) rl
  obtain ⟨m3, s3, a3, wb, rb, eb⟩ := hb hd (by omega) m2 _ pre2.left
  subst wb
  have pre3 := pre2.next a3 (Nat.le_refl _) (by omega)
  have low3 := slotRead_agree pre2.frame a3 (show d < d + 2 by omega) (by omega) low2
  have high3 := slotRead_agree pre2.frame a3 (show d + 1 < d + 2 by omega) (by omega) rh
  have suffix : Pre L m3 _ fp K d (softDivQuotientC d) ρ W :=
    ⟨hp.ctx, pre3.small, pre3.frame, pre3.code, pre3.far, pre3.env, pre3.welt, pre3.wstab⟩
  obtain ⟨m4, s4, a4, w, rw, ew⟩ := softDivQuotientC_ok suffix (by omega)
    (an * 2 ^ k) bn bp bb nb low3 high3 rb
  refine ⟨m4, ?_, ((a1.trans (a2.mono (show d ≤ d + 1 by omega))).trans
    (a3.mono (show d ≤ d + 2 by omega))).trans a4, w, rw, ew⟩
  simpa only [List.length_append, pc_add] using ((s1.trans s2).trans s3).trans s4

/-- The actual quotient generator accepts both normalization directions. -/
theorem softDivQuotientL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => softDivQuotientL d
      (fun j => some (konstWL 4 (2 ^ 52) j))
      (fun j => some (konstWL 4 (3 * 2 ^ 51) j)) 56)
      (BitVec.ofNat 64 (softDivJam (2 ^ 108) (3 * 2 ^ 51))) := by
  exact softDivQuotientL_ok (WordCode.konst _ (by decide)) (WordCode.konst _ (by decide))
    (by decide) (by decide) (by decide) (Or.inr rfl) (by decide)

#print axioms softDivQuotient_limbs
#print axioms softDivQuotientL_ok
#print axioms softDivQuotientL_ok_zeuge
end Gabbro.Stage0.Senke
