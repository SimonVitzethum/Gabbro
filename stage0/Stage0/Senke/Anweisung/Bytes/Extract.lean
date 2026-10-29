/- Subject: Extract bytes with unsigned shifts, including the top bit of a full word. -/
import Stage0.Senke.Anweisung.Bytes.Code
import Stage0.Senke.Ausdruck.Lesen
import Stage0.Senke.Umgebung
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

theorem byte_word {z : Int} (hz0 : 0 ≤ z) (hz : z < 2 ^ 64) (j : Nat) (hj : j < 8) :
    ((BitVec.ofInt 64 z >>> (8 * j)) &&& 255) = BitVec.ofInt 64 (dropBytes j z % 256) := by
  have he0 := Int.emod_nonneg (dropBytes j z) (show (256 : Int) ≠ 0 by decide)
  have he1 := Int.emod_lt_of_pos (dropBytes j z) (show (0 : Int) < 256 by decide)
  apply BitVec.eq_of_toNat_eq
  have h255 : (255 : Runner.W) = BitVec.ofNat 64 (2 ^ 8 - 1) := rfl
  rw [h255, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    show (2 ^ 8 - 1) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofInt, show z % ((2 ^ 64 : Nat) : Int) = z from Int.emod_eq_of_lt hz0 (by omega),
    ofInt_nat he0 (by omega)]
  match j, hj with
  | 0, _ => simp only [dropBytes]; omega
  | 1, _ => simp only [dropBytes]; omega
  | 2, _ => simp only [dropBytes]; omega
  | 3, _ => simp only [dropBytes]; omega
  | 4, _ => simp only [dropBytes]; omega
  | 5, _ => simp only [dropBytes]; omega
  | 6, _ => simp only [dropBytes]; omega
  | 7, _ => simp only [dropBytes]; omega


variable [Kern] {D : Deklaration} {L : Lay D}

theorem bytePartC_ok {Γ : Ctx} {a b H : Int} {z : Zahl 0 H} {k : Zahl a b} {ρ : Env D Γ}
    {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {W : Runner.Mem → Prop}
    (hz : z.n < 2 ^ 64) (hj : j < 8) (hK : frei Γ + 4 ≤ K)
    (hp : Pre L m pc fp K (frei Γ + 2) (bytePartC (frei Γ) (frei Γ + 2) j)
      (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) W) :
    Ok m pc fp K (frei Γ + 2) (bytePartC (frei Γ) (frei Γ + 2) j)
      (fun w => w = BitVec.ofInt 64 (dropBytes j z.n % 256)) := by
  have hs : (BitVec.ofInt 64 ((8 * j : Nat) : Int)).toNat % 64 = 8 * j := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega
  have hp' : Pre L m pc fp K (frei Γ + 2)
      (([ci 2 (frei Γ + 2) (frei Γ) 0] ++ [ci 1 (frei Γ + 3) (8 * j) 0] ++
        [ci 12 (frei Γ + 2) (frei Γ + 2) (frei Γ + 3)]) ++
        [ci 1 (frei Γ + 3) 255 0] ++ [ci 8 (frei Γ + 2) (frei Γ + 2) (frei Γ + 3)])
      (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) W := by
    simpa [bytePartC, Int.add_assoc] using hp
  have hh := bin_ok (P := fun w => w = BitVec.ofInt 64 (dropBytes j z.n % 256)) (Pa := fun w => w = BitVec.ofInt 64 z.n >>> (8 * j))
    (fun m pc hp => bin_ok (Pa := fun w => w = BitVec.ofInt 64 z.n) (fun m pc hp => by
      obtain ⟨v, hr, hv⟩ := hp.env (.int 0 H) (.there .here)
      have hrd : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofInt 64 z.n) := by
        simp only [vslot_there, vslot_here] at hr
        exact hv ▸ hr
      exact mov_ok hp (by omega) (by omega) hrd)
      (fun m pc hp => const_ok hp (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega) (by omega))
      (g := fun x y => some (x >>> (y.toNat % 64)))
      (fun wa wb pa pb => ⟨_, rfl, by rw [pa, pb]; simpa only [Int.natCast_mul, show ((8 : Nat) : Int) = 8 by rfl] using congrArg (fun q => BitVec.ofInt 64 z.n >>> q) hs⟩) rfl (by decide) (by omega) hp)
    (fun m pc hp => const_ok hp (by decide) (by omega))
    (g := fun x y => some (x &&& y))
    (fun wa wb pa pb => ⟨_, rfl, by rw [pa, pb]; exact byte_word z.lo_le hz j hj⟩)
    rfl (by decide) (by omega) hp'
  simpa [bytePartC, Int.add_assoc] using hh

end Gabbro.Stage0.Senke
