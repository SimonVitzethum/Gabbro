/- Backward branches used by the actual ticket retry loops. -/
module
public import Stage0.Senke.Sperre.Schritt
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern]

/-- Subtracting a code distance returns to the earlier instruction, including
    modular program-counter arithmetic. -/
theorem pc_back (pc : W) (i k : Nat) :
    pc + BitVec.ofNat 64 (16 * (i + k)) + BitVec.ofInt 64 (-((16 * k : Nat) : Int)) =
      pc + BitVec.ofNat 64 (16 * i) := by
  rw [show 16 * (i + k) = 16 * i + 16 * k by omega, BitVec.ofNat_add,
    BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [← BitVec.add_assoc, ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel]

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {n u w : W}

theorem ls_brz_back (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w)
    {i k e : Nat} {A Lb : Int}
    (hi : code[i + k]? = some (ci 19 A Lb 0))
    (hA : A = ((s + e : Nat) : Int)) (hL : Lb = -((16 * k : Nat) : Int))
    (he : e < 18) (hk : lit32 (-((16 * k : Nat) : Int)) = true) (hz : f e = 0) :
    Star ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m := by
  subst hA hL
  have ins := E.ins h.ag hi
  simp only [ci] at ins
  have hs := E.small
  refine ls_star ins (by decide) ?_
  have read := h.sl e he
  rw [← sx_nat (d := s + e) (by omega), hz] at read
  have run := run_brz_zero (t := ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩) ins read
  rwa [sx_lit hk, pc_back] at run

theorem ls_jmp_back (E : LE m0 pc fp s a code) (h : AgreeK fp s a m0 m)
    {i k : Nat} {Lb : Int} (hi : code[i + k]? = some (ci 18 Lb 0 0))
    (hL : Lb = -((16 * k : Nat) : Int)) (hk : lit32 (-((16 * k : Nat) : Int)) = true) :
    Star ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m := by
  subst hL
  have ins := E.ins h hi
  simp only [ci] at ins
  refine ls_star ins (by decide) ?_
  have run := run_jmp (t := ⟨pc + BitVec.ofNat 64 (16 * (i + k)), fp⟩) ins
  rwa [sx_lit hk, pc_back] at run

end
end Gabbro.Stage0.Senke
