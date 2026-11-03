/- Rounding for software binary64 addition (`Block.float`, `op = .add`).

    The round step decides the exact magnitude sum with the existing
    nearest-even machinery, nothing new: `softRoundMag` is `rundeInt` on the
    routine's (quotient, remainder, denominator), `softRoundMag_model` replays
    the `floatRoundUp` bridge, and `softRoundL`/`softRoundL_ok` reuse the
    `floatRoundL` fragment and its lemma directly (same opcodes, same bounds:
    remainder below denominator, denominator below `2^63`). Forming
    (quotient, remainder, denominator) from the exact sum — shifting down to
    53 bits — belongs to normalization and lands with pack; this piece only
    pins the decision itself to the kernel. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Gleit.Runden
public import Stage0.Senke.Ausdruck.Gleit.RundCode
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Round the exact magnitude sum: the kernel `rundeInt` decision over the
    routine's (quotient, remainder, denominator). -/
def softRoundMag (q r den : Nat) : Nat := Gleitkomma.rundeInt q r den

/-- The decision is exactly the kernel's: round up past half, or on a tie
    with odd quotient. Reuses `floatRoundUp_model`. -/
theorem softRoundMag_model (q r den : Nat) (hr : r < den) :
    softRoundMag q r den = q + (if floatRoundUp q r den then 1 else 0) :=
  floatRoundUp_model q r den hr

/-- The round fragment, reusing `floatRoundL` unchanged. -/
def softRoundL (d : Nat) (q r den : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  floatRoundL d q r den

/-- Correctness of the round fragment against the kernel decision, reusing
    `floatRoundL_ok` directly. -/
theorem softRoundL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {q r den : Nat → Option (List II × Nat)} {qn rn dn : Nat}
    (hr : rn < dn) (hd : dn < 2 ^ 63)
    (hq : WordCode (L := L) (reserved := reserved) ρ W q (BitVec.ofNat 64 qn))
    (hrc : WordCode (L := L) (reserved := reserved) ρ W r (BitVec.ofNat 64 rn))
    (hdc : WordCode (L := L) (reserved := reserved) ρ W den (BitVec.ofNat 64 dn))
    {fp : Runner.W} {K d top : Nat} {c : List II}
    (h : softRoundL d q r den = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (softRoundMag qn rn dn)) :=
  floatRoundL_ok qn rn dn hr hd hq hrc hdc h hK hp

/-- Joint fixtures: round down, round up past half, and both tie directions
    (even stays, odd carries into `2^53`). -/
theorem round_zeuge :
    softRoundMag 4 1 2 = 4 ∧
    softRoundMag 5 1 2 = 6 ∧
    softRoundMag (2 ^ 53 - 1) 3 4 = 2 ^ 53 := by
  decide +kernel

/-- The reused fragment computes on closed inputs and emits. -/
theorem softRoundL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop)
    {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (h : softRoundL d (fun j => some (konstWL 4 13 j))
      (fun j => some (konstWL 4 6 j)) (fun j => some (konstWL 4 8 j)) =
      some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 14) := by
  have hr : 6 < 8 := by decide
  have hd : 8 < 2 ^ 63 := by decide
  have result := softRoundL_ok hr hd (WordCode.konst 13 (by decide))
    (WordCode.konst 6 (by decide)) (WordCode.konst 8 (by decide)) h hK hp
  have hx : softRoundMag 13 6 8 = 14 := by decide +kernel
  rw [hx] at result
  exact result

#print axioms softRoundMag_model
#print axioms softRoundL_ok
#print axioms round_zeuge
#print axioms softRoundL_ok_zeuge

end Gabbro.Stage0.Senke
