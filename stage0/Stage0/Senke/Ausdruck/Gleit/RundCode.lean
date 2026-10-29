/- A compositional proof of the integer-only nearest-even software fragment.
   Inputs are pure code generators; their existing expression proofs are reused. -/
import Stage0.Senke.Ausdruck.Gleit.Runden

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Round a quotient and remainder, using only add/sub/and/or/slt/eq.
    Inputs can be reread, and must therefore be pure. All scratch slots are
    accounted for by wordL; no new opcode or unchecked helper call is needed. -/
def floatRoundL (d : Nat) (q r den : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let gap := fun d => wordL 4 d (den d) (r (d + 1))
  let above := fun d => wordL 13 d (gap d) (r (d + 1))
  let tie := fun d => wordL 14 d (r d) (gap (d + 1))
  let odd := fun d => wordK 8 d (q d) 1
  wordL 3 d (q d) (wordL 9 (d + 1) (above (d + 1))
    (wordL 8 (d + 2) (tie (d + 2)) (odd (d + 3))))

/-- The low bit of an arbitrary word is its unsigned remainder modulo two. -/
theorem float_low_bit (q : Runner.W) : q &&& 1 = q % 2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_umod]
  change q.toNat &&& 1 = q.toNat % 2
  exact Nat.and_one_is_mod _

/-- Modulo two is a Boolean word, including when the input's sign bit is set. -/
theorem float_parity_word (q : Runner.W) :
    q &&& 1 = Runner.IR.bool (q % 2 == 1) := by
  rw [float_low_bit]
  have h : (q % 2).toNat < 2 := by
    rw [BitVec.toNat_umod]
    exact Nat.mod_lt _ (by decide)
  have hz : q % 2 = 0 ∨ q % 2 = 1 := by
    have hz : (q % 2).toNat = 0 ∨ (q % 2).toNat = 1 := by omega
    exact hz.elim (fun h => Or.inl (BitVec.eq_of_toNat_eq h))
      (fun h => Or.inr (BitVec.eq_of_toNat_eq h))
  rcases hz with hz | hz <;> rw [hz] <;> decide

private abbrev WordCode (ρ : Env D Γ) (W : Runner.Mem → Prop)
    (a : Nat → Option (List II × Nat)) (v : Runner.W) : Prop :=
  ∀ {fp K d c top}, a d = some (c, top) → top ≤ K → ∀ m pc,
    Pre L m pc fp K d c ρ W → Ok m pc fp K d c (· = v)

private theorem code_bin {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {va vb v : Runner.W} {o : Nat}
    {g : Runner.W → Runner.W → Option Runner.W}
    (ha : WordCode (L := L) ρ W a va) (hb : WordCode (L := L) ρ W b vb)
    (hg : g va vb = some v) (hop : op o = bin g) (ho : o < 256) :
    WordCode (L := L) ρ W (fun d => wordL o d (a d) (b (d + 1))) v := by
  intro fp K d c top h hK m pc hp
  exact wordL_ok h hK (fun _ _ he ht => ha he ht) (fun _ _ he ht => hb he ht)
    (fun x y hx hy => ⟨v, by simpa only [hx, hy] using hg, rfl⟩) hop ho hp

private theorem code_one {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} :
    WordCode (L := L) ρ W (fun d => some ([ci 1 d 1 0], d + 1)) 1 := by
  intro fp K d c top h hK m pc hp
  cases h
  exact const_ok hp (by decide) (by omega)

/-- Every execution of the fragment agrees with G's rounding kernel.
    The assumptions are precisely the input-code proofs and arithmetic bounds;
    in particular no correctness premise about a float routine is assumed. -/
theorem floatRoundL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {q r den : Nat → Option (List II × Nat)} (qn rn dn : Nat)
    (hr : rn < dn) (hd : dn < 2 ^ 63)
    (hq : ∀ {fp K d c top}, q d = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W → Ok m pc fp K d c (· = BitVec.ofNat 64 qn))
    (hrc : ∀ {fp K d c top}, r d = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W → Ok m pc fp K d c (· = BitVec.ofNat 64 rn))
    (hdc : ∀ {fp K d c top}, den d = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W → Ok m pc fp K d c (· = BitVec.ofNat 64 dn))
    {fp : Runner.W} {K d top : Nat} {c : List II}
    (h : floatRoundL d q r den = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (Gleitkomma.rundeInt qn rn dn)) := by
  have gap : WordCode (L := L) ρ W _ _ := code_bin hdc hrc (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have above : WordCode (L := L) ρ W _ _ := code_bin gap hrc (g := fun a b => some (Runner.IR.bool (a.slt b)))
    rfl rfl (by decide : 13 < 256)
  have tie : WordCode (L := L) ρ W _ _ := code_bin hrc gap (g := fun a b => some (Runner.IR.bool (a == b)))
    rfl rfl (by decide : 14 < 256)
  have odd : WordCode (L := L) ρ W _ _ := code_bin hq code_one (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
  have both : WordCode (L := L) ρ W _ _ := code_bin tie odd (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
  have bump : WordCode (L := L) ρ W _ _ := code_bin above both (g := fun a b => some (a ||| b)) rfl rfl (by decide : 9 < 256)
  have result : WordCode (L := L) ρ W _ _ := code_bin hq bump (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)
  have res := result (fp := fp) (K := K) (d := d) (c := c) (top := top)
    (by simpa [floatRoundL, wordK, Nat.add_assoc, Int.add_assoc] using h) hK m pc
    (by simpa [floatRoundL, wordK, Nat.add_assoc, Int.add_assoc] using hp)
  exact res.mono fun w hw => by
    rw [float_parity_word] at hw
    exact hw.trans (floatRoundWord_model qn rn dn hr hd)

end Gabbro.Stage0.Senke
