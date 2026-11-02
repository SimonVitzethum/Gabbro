/- Quotient/remainder scaling followed by G's nearest-even rounding. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil1a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag

@[expose] public section



namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Renormalize a rounded significand at the carry boundary using integer IR.
    Equality produces the shift count and the exponent increment. -/
def floatPackCarryL (d : Nat) (s e q : Nat → Option (List II × Nat))
    (unit : Nat) : Option (List II × Nat) :=
  let limit := fun j => some (konstWL 4 (2 * unit) j)
  let carry := fun j => wordL 14 j (q j) (limit (j + 1))
  let exponent := fun j => wordL 3 j (e j) (carry (j + 1))
  let significand := fun j => wordL 12 j (q j) (carry (j + 1))
  floatPackNormalL d s exponent significand unit

theorem floatPackCarryL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s e q : Nat → Option (List II × Nat)} {sv ev qv : Runner.W}
    (hs : WordCode (L := L) ρ W s sv) (he : WordCode (L := L) ρ W e ev)
    (hq : WordCode (L := L) ρ W q qv) (unit : Nat) (hu : 2 * unit < 2^64) :
    let carry := Runner.IR.bool (qv == BitVec.ofNat 64 (2 * unit))
    WordCode (L := L) ρ W (fun d => floatPackCarryL d s e q unit)
      (sv + (ev + carry) * BitVec.ofNat 64 unit +
        ((qv >>> (carry.toNat % 64)) - BitVec.ofNat 64 unit)) := by
  have hc : WordCode (L := L) ρ W _ _ := WordCode.bin hq
    (WordCode.konst (2 * unit) hu)
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have hx : WordCode (L := L) ρ W _ _ := WordCode.bin he hc
    (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)
  have hq' : WordCode (L := L) ρ W _ _ := WordCode.bin hq hc
    (g := fun a b => some (a >>> (b.toNat % 64))) rfl rfl (by decide : 12 < 256)
  dsimp only
  intro fp K d c top h hK m pc hp
  exact floatPackNormalL_ok hs hx hq' unit (by omega) h hK m pc hp

/-- Transfer the actual carry comparison and shift to natural fields. -/
theorem floatPackCarry_nat (q u : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    c.toNat = (if q = 2*u then 1 else 0) ∧
    (BitVec.ofNat 64 q >>> (c.toNat % 64)).toNat =
      (if q = 2*u then u else q) := by
  have hq64 : q < 2^64 := by omega
  have eqv : (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u)) = decide (q = 2*u) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hq64, Nat.mod_eq_of_lt hu]
  dsimp only
  rw [eqv]
  by_cases h : q = 2*u
  · subst q
    simp [Runner.IR.bool, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hu, Nat.mul_div_cancel_left]
    omega
  · simp [h, Runner.IR.bool, BitVec.toNat_ushiftRight,
      Nat.mod_eq_of_lt hq64]
    omega

/-- The packing expression uses the natural renormalized significand. -/
theorem floatPackCarry_word (q u : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    (BitVec.ofNat 64 q >>> (c.toNat % 64)) - BitVec.ofNat 64 u =
      BitVec.ofNat 64 (if q = 2*u then u else q) - BitVec.ofNat 64 u := by
  have bridge := (floatPackCarry_nat q u hu hq).2
  have hb : (if q = 2*u then u else q) < 2^64 := by split <;> omega
  have hw : (BitVec.ofNat 64 q >>>
      ((Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))).toNat % 64)) =
      BitVec.ofNat 64 (if q = 2*u then u else q) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    exact bridge
  dsimp only
  rw [hw]

/-- Renormalization preserves the normal field interval, including carry. -/
theorem floatPackCarry_bounds (q u e max : Nat) (hu : 0 < u)
    (hq : u ≤ q ∧ q ≤ 2*u) (he : 0 < e ∧ e + 1 < max) :
    (0 < e + (if q = 2*u then 1 else 0) ∧
      e + (if q = 2*u then 1 else 0) < max) ∧
    (u ≤ (if q = 2*u then u else q) ∧
      (if q = 2*u then u else q) < 2*u) := by
  split <;> omega

/-- Real exponent bounds exclude machine-word wrap after carry addition. -/
theorem floatPackCarry_exponent (q u e max : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) (he : e + 1 < max) (hm : max ≤ 2^64) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    (BitVec.ofNat 64 e + c).toNat = e + (if q = 2*u then 1 else 0) := by
  have hc := (floatPackCarry_nat q u hu hq).1
  have he64 : e < 2^64 := by omega
  have hn : e + (if q = 2*u then 1 else 0) < 2^64 := by split <;> omega
  dsimp only at hc ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hc,
    Nat.mod_eq_of_lt hn]

/-- The actual carry packing expression equals canonical normalized fields. -/
theorem floatPackCarry_canonical (F : Gleitkomma.Format) (sign : Bool) (e q : Nat)
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < e ∧ e + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ q ∧ q ≤ 2 * 2^F.fracBits) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^F.fracBits))
    BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0) +
      (BitVec.ofNat 64 e + c) * BitVec.ofNat 64 (2^F.fracBits) +
      ((BitVec.ofNat 64 q >>> (c.toNat % 64)) - BitVec.ofNat 64 (2^F.fracBits)) =
    BitVec.ofNat 64 (Gleitkomma.zuBits F
      ⟨sign, e + (if q = 2 * 2^F.fracBits then 1 else 0),
        (if q = 2 * 2^F.fracBits then 2^F.fracBits else q) - 2^F.fracBits⟩) := by
  have hb := floatPackCarry_bounds q (2^F.fracBits) e F.bexpMax
    (Nat.pow_pos (by decide)) hq he
  have hx : BitVec.ofNat 64 e +
      Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^F.fracBits)) =
      BitVec.ofNat 64 (e + (if q = 2 * 2^F.fracBits then 1 else 0)) := by
    apply BitVec.eq_of_toNat_eq
    rw [floatPackCarry_exponent q _ e F.bexpMax hu hq he.2 hm,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [hx, floatPackCarry_word q _ hu hq]
  apply floatPackNormal_canonical F sign _ _ (by omega) hb.1
  simpa [Nat.pow_succ, Nat.mul_comm] using hb.2

/-- The normal branch of the actual rounding kernel, before field packing. -/
theorem floatPackCarry_rundeBruchKern (F : Gleitkomma.Format) (sign : Bool)
    (n d : Nat) (E : Int) (hp : 1 ≤ F.p)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int)) :
    Gleitkomma.rundeBruchKern F sign n d E =
      if Gleitkomma.normQ F.p E n d < 2^F.p then
        ⟨sign, (E - F.emin + 1).toNat,
          Gleitkomma.normQ F.p E n d - 2^(F.p - 1)⟩
      else ⟨sign, (E - F.emin + 2).toNat, 0⟩ := by
  have hn : ¬ E < F.emin - (F.p : Int) := by omega
  unfold Gleitkomma.rundeBruchKern
  rw [if_neg (by omega), if_neg hn, if_pos hlo]
  split
  · rfl
  · rfl

/-- Actual emitted carry IR simulates canonical normalized G fields. -/
theorem floatPackCarryL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s ex qcode : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (sign : Bool) (e q : Nat)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (hecode : WordCode (L := L) ρ W ex (BitVec.ofNat 64 e))
    (hqcode : WordCode (L := L) ρ W qcode (BitVec.ofNat 64 q))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < e ∧ e + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ q ∧ q ≤ 2 * 2^F.fracBits) :
    WordCode (L := L) ρ W (fun d => floatPackCarryL d s ex qcode (2^F.fracBits))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F
        ⟨sign, e + (if q = 2 * 2^F.fracBits then 1 else 0),
          (if q = 2 * 2^F.fracBits then 2^F.fracBits else q) - 2^F.fracBits⟩)) := by
  rw [← floatPackCarry_canonical F sign e q hu hm he hq]
  intro fp K d c top h hK m pc hp
  exact floatPackCarryL_ok hs hecode hqcode (2^F.fracBits) hu h hK m pc hp

/-- Actual normal rounding outputs are exactly the carry packer's fields. -/
theorem floatPackCarry_fields (F : Gleitkomma.Format) (sign : Bool)
    (n d : Nat) (E : Int) (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hq : Gleitkomma.normQ F.p E n d ≤ 2 * 2^F.fracBits) :
    Gleitkomma.rundeBruchKern F sign n d E =
      ⟨sign, (E - F.emin + 1).toNat +
          (if Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits then 1 else 0),
        (if Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits
          then 2^F.fracBits else Gleitkomma.normQ F.p E n d) - 2^F.fracBits⟩ := by
  have hpow : 2^F.p = 2 * 2^F.fracBits := by
    have he : F.p = F.fracBits + 1 := by omega
    rw [he, Nat.pow_succ]
    omega
  rw [floatPackCarry_rundeBruchKern F sign n d E hp hlo hhi, hpow]
  by_cases hc : Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits
  · simp only [hc, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
    congr 1
    omega
  · have hl : Gleitkomma.normQ F.p E n d < 2 * 2^F.fracBits := by omega
    simp only [hl, hc, ↓reduceIte, Nat.add_zero]
    rw [hf]


/-- The emitted carry fragment returns the actual canonical rounding-kernel bits. -/
theorem floatPackCarryL_rundeBruchKern {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {s ex qcode : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (sign : Bool) (n d : Nat) (E : Int)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (hecode : WordCode (L := L) ρ W ex (BitVec.ofNat 64 (E - F.emin + 1).toNat))
    (hqcode : WordCode (L := L) ρ W qcode
      (BitVec.ofNat 64 (Gleitkomma.normQ F.p E n d)))
    (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ Gleitkomma.normQ F.p E n d ∧
      Gleitkomma.normQ F.p E n d ≤ 2 * 2^F.fracBits) :
    WordCode (L := L) ρ W (fun dst => floatPackCarryL dst s ex qcode (2^F.fracBits))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.rundeBruchKern F sign n d E))) := by
  rw [floatPackCarry_fields F sign n d E hp hf hlo hhi hq.2]
  exact floatPackCarryL_canonical F sign _ _ hs hecode hqcode hu hm he hq


end Gabbro.Stage0.Senke
