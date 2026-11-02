/- The full-limb mask computes the exact declared-width modulus. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Saturation
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem mask_modulus (w : Nat) (n : Int) (nonnegative : 0 ≤ n) :
    ((n.toNat &&& (2 ^ (w + 1) - 1) : Nat) : Int) = n % (2 : Int) ^ (w + 1) := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod,
    Int.toNat_of_nonneg nonnegative]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]

theorem wrapL_ok {lo hi : Int} (w : Nat) (x : Zahl lo hi)
    (nonnegative : 0 ≤ x.n) (result : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (value : result.n = x.n % (2 : Int) ^ (w + 1))
    {fe : Nat → Option (List II × Nat)} {fp : Runner.W} {K d top : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ ce te, fe d = some (ce, te) → te ≤ K → ∀ m pc,
      Pre L m pc fp K d ce ρ W reserved → ValueOk L m pc fp K d ce (.int lo hi) x)
    (h : wrapL w lo hi d fe = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 ((2 : Int) ^ (w + 1) - 1)) result := by
  let u := (2 : Int) ^ (w + 1) - 1
  have positive := zweiPow_pos w
  let mask : Zahl 0 u := ⟨u, by dsimp [u]; omega, by omega⟩
  have maskNatural : mask.n.toNat = 2 ^ (w + 1) - 1 := by
    have cast : ((2 ^ (w + 1) - 1 : Nat) : Int) = u := by
      have positiveNatural : (0 : Nat) < 2 ^ (w + 1) := Nat.pow_pos (by decide)
      rw [Int.ofNat_sub (by omega)]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int, u]
    rw [show mask.n = u from rfl, ← cast, Int.toNat_natCast]
  unfold wrapL wideBitL at h
  have run := wideBinary_ok x mask (arithWords_left _ _ _ _ _ _) (arithWords_right _ _ _ _ _ _)
    ih (fun cc tt hc ht m pc hp => intConstL_ok mask hc ht hp) h hK hp
    (R := fun m' => WordsAt m' fp d
      (integerEncoding (arithWords lo hi 0 u 0 u) ((x.n.toNat &&& mask.n.toNat : Nat) : Int)))
    (fun m pc pre hd hx hy => by
      rw [← Int.toNat_of_nonneg nonnegative] at hx
      rw [← Int.toNat_of_nonneg mask.lo_le] at hy
      obtain ⟨m', steps, changed, words, _⟩ := wideAnd_run pre.frame pre.small (by omega)
        pre.code pre.far x.n.toNat mask.n.toNat hx hy
      exact ⟨m', steps, changed, words⟩)
  exact run.mono fun _ words => valueAt_int_of_wide result (arithWords_result _ _ _ _ _ _)
    (by rw [value, ← mask_modulus w x.n nonnegative, ← maskNatural]; exact words)

end Gabbro.Stage0.Senke
