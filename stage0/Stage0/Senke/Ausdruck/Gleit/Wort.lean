/- Binary64 words and arbitrary-word constants in the integer-only IR. -/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem konstWL_top (k n d : Nat) : d < (konstWL k n d).2 ∧ (konstWL k n d).2 ≤ d + 2 := by
  induction k generalizing n with
  | zero => simp only [konstWL]; omega
  | succ k ih =>
    have := ih (n / 65536)
    simp only [konstWL, bin2, Nat.max_le] at *
    omega

/-- Every 64-bit pattern is materialised with integer instructions only. -/
theorem konstWL_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (k n : Nat)
    (hn : n < 65536 ^ k) (hK : d + 2 ≤ K)
    (hp : Pre L m pc fp K d (konstWL k n d).1 ρ W reserved) :
    Ok m pc fp K d (konstWL k n d).1 (· = BitVec.ofNat 64 n) := by
  induction k generalizing n m pc with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    exact (const_ok hp (by decide) (by omega)).mono fun _ h => h
  | succ k ih =>
    have hq : n / 65536 < 65536 ^ k := by rw [Nat.pow_succ] at hn; omega
    have hlow : lit32 (n % 65536 : Nat) = true := lit32_nat (by omega)
    apply bin_ok (Pb := fun w => w = BitVec.ofInt 64 (n % 65536 : Nat))
      (Pa := fun w => w = BitVec.ofNat 64 (n / 65536) * BitVec.ofInt 64 65536)
      (g := fun x y => some (x + y)) ?_ ?_ ?_ rfl (by decide) (by omega) hp
    · intro m pc hp
      exact bin_ok (fun m pc hp => ih _ hq hp)
        (fun m pc hp => const_ok hp (by decide) (by omega))
        (fun a b ha hb => ⟨_, rfl, by rw [ha, hb]⟩) rfl (by decide) (by omega) hp
    · intro m pc hp
      exact const_ok hp hlow (by omega)
    · intro a b ha hb
      refine ⟨_, rfl, ?_⟩
      rw [ha, hb, BitVec.ofInt_natCast, show BitVec.ofInt 64 65536 = BitVec.ofNat 64 65536 from rfl,
        ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)

/-- Packing does not identify distinct well-formed binary64 values. -/
theorem float_word_injective {a b : GFloat}
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (hb : Gleitkomma.wf Gleitkomma.f64 b)
    (h : BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a) =
      BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 b)) : a = b := by
  have al := Gleitkomma.zuBits_lt _ Gleitkomma.f64_dicht a ha
  have bl := Gleitkomma.zuBits_lt _ Gleitkomma.f64_dicht b hb
  have e : Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits + 1 = 64 := by decide
  rw [e] at al bl
  have h := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt al, Nat.mod_eq_of_lt bl] at h
  have := congrArg (Gleitkomma.ausBits Gleitkomma.f64) h
  simpa only [Gleitkomma.ausBits_zuBits _ Gleitkomma.f64_dicht _ ha,
    Gleitkomma.ausBits_zuBits _ Gleitkomma.f64_dicht _ hb] using this

theorem wordConstant_length (d : Nat) (n : Int) :
    (wordConstant d n).1.length = if lit32 n then 1 else 17 := by
  unfold wordConstant
  split <;> simp [konstWL, bin2]

theorem wordConstant_top (d : Nat) (n : Int) :
    d < (wordConstant d n).2 ∧ (wordConstant d n).2 ≤ d + 2 := by
  unfold wordConstant
  split
  · simp
  · exact konstWL_top 4 _ d

/-- The shared materializer runs on the actual memory and preserves the frame
    prefix. Two words suffice for either immediate or digit materialization. -/
theorem wordConstant_ok {reserved : Nat} {m : Runner.Mem} {pc fp : Runner.W}
    {K d : Nat} {n : Int} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (room : d + 2 ≤ K)
    (pre : Pre L m pc fp K d (wordConstant d n).1 ρ W reserved) :
    Ok m pc fp K d (wordConstant d n).1 (· = BitVec.ofInt 64 n) := by
  by_cases small : lit32 n = true
  · have hp : Pre L m pc fp K d [ci 1 d n 0] ρ W reserved := by
      simpa [wordConstant, small] using pre
    simpa [wordConstant, small] using const_ok hp small (by omega)
  · have hp : Pre L m pc fp K d (konstWL 4 (BitVec.ofInt 64 n).toNat d).1 ρ W reserved := by
      simpa [wordConstant, small] using pre
    have run := (konstWL_ok 4 (BitVec.ofInt 64 n).toNat (BitVec.isLt _) room hp).mono
      (fun w hw => by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw)
    simpa [wordConstant, small] using run


end Gabbro.Stage0.Senke
