/- Emitted post-cancellation nearest-even rounding and field packing. -/
import Stage0.Senke.Ausdruck.Arithmetik.Distanz
import Stage0.Senke.Ausdruck.Gleit.SlotContext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem Gleitkomma
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The normal output continuation consumes the final magnitude's quotient,
    guard and exact-tail indicator, rather than a jammed signed operand. -/
def floatAddNormalOutputL (dst : Nat)
    (sign exponent quotient guard sticky : Nat → Option (List II × Nat))
    (unit : Nat) : Option (List II × Nat) :=
  floatPackCarryL dst sign exponent
    (fun j => floatGuardRoundL j quotient guard sticky) unit

/-- Round and pack in one emitted fragment, for arbitrary pure producers.
    The arithmetic decomposition relates the final magnitude to normQD;
    no premise assumes correctness of a floating-point routine. -/
theorem floatAddNormalOutputL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s ex q g t : Nat → Option (List II × Nat)}
    (F : Format) (sign : Bool) (n d qn gn rest den : Nat) (E : Int)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (he : WordCode (L := L) ρ W ex (BitVec.ofNat 64 (E - F.emin + 1).toNat))
    (hq : WordCode (L := L) ρ W q (BitVec.ofNat 64 qn))
    (hg : WordCode (L := L) ρ W g (BitVec.ofNat 64 gn))
    (ht : WordCode (L := L) ρ W t (BitVec.ofNat 64 (if rest = 0 then 0 else 1)))
    (hd : 0 < den) (hr : rest < den) (hguard : gn < 8)
    (hquot : (normQD F.p E n d).1 / (normQD F.p E n d).2 = qn)
    (hrem : (normQD F.p E n d).1 % (normQD F.p E n d).2 = gn * den + rest)
    (hden : (normQD F.p E n d).2 = 8 * den)
    (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (hex : 0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax)
    (hb : 2^F.fracBits ≤ normQ F.p E n d ∧
      normQ F.p E n d ≤ 2 * 2^F.fracBits) :
    WordCode (L := L) ρ W
      (fun dst => floatAddNormalOutputL dst s ex q g t (2^F.fracBits))
      (BitVec.ofNat 64 (zuBits F (rundeBruchKern F sign n d E))) := by
  have hnorm : normQ F.p E n d = rundeInt qn (gn * den + rest) (8 * den) := by
    unfold normQ
    rw [hquot, hrem, hden]
  have rounded : WordCode (L := L) ρ W (fun j => floatGuardRoundL j q g t)
      (BitVec.ofNat 64 (rundeInt qn (gn * den + rest) (8 * den))) := floatGuardRoundL_ok qn gn rest den hd hr hguard hq hg ht
  rw [← hnorm] at rounded
  intro fp K dst code top hc hK m pc hpre
  exact floatPackCarryL_rundeBruchKern F sign n d E hs he rounded
    hp hf hlo hhi hu hm hex hb hc hK m pc hpre

/-- Execute normal rounding and packing from five actual retained frame reads.
    All loads, their alias bounds and their temporary frame are derived here.
    The caller's reserved prefix is arbitrary. -/
theorem floatAddNormalOutputL_slots {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (F : Format) (sign : Bool) (n d qn gn rest den : Nat) (E : Int)
    (hd : 0 < den) (hr : rest < den) (hguard : gn < 8)
    (hquot : (normQD F.p E n d).1 / (normQD F.p E n d).2 = qn)
    (hrem : (normQD F.p E n d).1 % (normQD F.p E n d).2 = gn * den + rest)
    (hden : (normQD F.p E n d).2 = 8 * den)
    (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (hex : 0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax)
    (hb : 2^F.fracBits ≤ normQ F.p E n d ∧
      normQ F.p E n d ≤ 2 * 2^F.fracBits)
    {m : Runner.Mem} {pc fp : Runner.W} {K base dst top reserved : Nat}
    {code : List II}
    (inputs : FB ≤ base) (retained : base+5 ≤ dst) (room : top ≤ K)
    (compiled : floatAddNormalOutputL dst
      (fun j => some ([ci 2 j base 0], j+1))
      (fun j => some ([ci 2 j (base+1) 0], j+1))
      (fun j => some ([ci 2 j (base+2) 0], j+1))
      (fun j => some ([ci 2 j (base+3) 0], j+1))
      (fun j => some ([ci 2 j (base+4) 0], j+1)) (2^F.fracBits) = some (code,top))
    (pre : Pre L m pc fp K dst code ρ W reserved)
    (dstRoom : dst ≤ K)
    (reads : ∀ (i : Nat), (hi : i < 5) → m.rd64 (slot fp (BitVec.ofNat 64 (base+i))) =
      some (([BitVec.ofNat 64 (if sign then 2^(F.ebits+F.fracBits) else 0),
        BitVec.ofNat 64 (E-F.emin+1).toNat, BitVec.ofNat 64 qn,
        BitVec.ofNat 64 gn, BitVec.ofNat 64 (if rest = 0 then 0 else 1)] : List Runner.W)[i]'(by simpa only [List.length_cons, List.length_nil] using hi))) :
    Ok m pc fp K dst code
      (· = BitVec.ofNat 64 (zuBits F (rundeBruchKern F sign n d E))) := by
  obtain ⟨env, envAt⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  have hp' : Pre L m pc fp K dst code env (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame, pre.code,
      pre.far, envAt, trivial, wstab_true _ _⟩
  have loads : ∀ (i : Nat), (hi : i < 5) → WordCode (L := L) env (fun _ => True)
      (fun j => some ([ci 2 j (base+i) 0], j+1))
      (([BitVec.ofNat 64 (if sign then 2^(F.ebits+F.fracBits) else 0),
        BitVec.ofNat 64 (E-F.emin+1).toNat, BitVec.ofNat 64 qn,
        BitVec.ofNat 64 gn, BitVec.ofNat 64 (if rest = 0 then 0 else 1)] : List Runner.W)[i]'(by simpa only [List.length_cons, List.length_nil] using hi)) := by
    intro i hi
    have idx : base+i-FB < dst-FB := by omega
    have slotEq : FB + (base+i-FB) = base+i := by omega
    obtain ⟨w, hr, he⟩ := envAt _ (frameWordVar (dst-FB) (base+i-FB) idx)
    rw [frameWordVar_slot, slotEq, reads i hi] at hr
    cases hr
    change _ = BitVec.ofInt 64 (env.get (frameWordVar (dst-FB) (base+i-FB) idx)).n at he
    rw [he]
    have slotEqInt : (FB : Int) + ((base+i-FB : Nat) : Int) = (base : Int) + i := by omega
    intro fp' K' j c t hc ht mm pp hpre
    apply frameWordLoad (L := L) (dst-FB) (base+i-FB) idx env
      (by simpa only [slotEqInt] using hc) ht mm pp hpre
  exact floatAddNormalOutputL_ok F sign n d qn gn rest den E
    (by
      intro fp' K' j c t hc ht mm pp hpre
      exact loads 0 (by omega) hc ht mm pp hpre) (by
      intro fp' K' j c t hc ht mm pp hpre
      exact loads 1 (by omega) hc ht mm pp hpre)
    (by
      intro fp' K' j c t hc ht mm pp hpre
      exact loads 2 (by omega) hc ht mm pp hpre) (by
      intro fp' K' j c t hc ht mm pp hpre
      exact loads 3 (by omega) hc ht mm pp hpre)
    (by
      intro fp' K' j c t hc ht mm pp hpre
      exact loads 4 (by omega) hc ht mm pp hpre) hd hr hguard hquot hrem hden hp hf hlo hhi hu hm hex hb
    compiled room m pc hp'

#print axioms floatAddNormalOutputL_slots

/-- At the largest finite exponent, carry produces infinity. The emitted
    exponent addition and zero fraction already give its canonical encoding. -/
theorem floatPackCarry_top_f64 (sign : Bool) (q : Nat)
    (hq : 2^52 ≤ q ∧ q ≤ 2^53) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^52))
    BitVec.ofNat 64 (if sign then 2^63 else 0) +
      (BitVec.ofNat 64 2046 + c) * BitVec.ofNat 64 (2^52) +
      ((BitVec.ofNat 64 q >>> (c.toNat % 64)) - BitVec.ofNat 64 (2^52)) =
      BitVec.ofNat 64 (zuBits f64
        (if q < 2^53 then ⟨sign, 2046, q - 2^52⟩ else ⟨sign, 2047, 0⟩)) := by
  dsimp only
  by_cases h : q = 2^53
  · subst q
    cases sign <;> decide +kernel
  · have hl : q < 2^53 := by omega
    have heq : (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^52)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show q < 2^64 by omega)]
      change q ≠ 9007199254740992
      omega
    rw [heq]
    simp only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte,
      BitVec.add_zero, BitVec.toNat_zero, Nat.zero_mod, BitVec.ushiftRight_zero, hl]
    exact floatPackNormal_canonical f64 sign 2046 q (by decide) (by decide)
      ⟨hq.1, hl⟩

/-- The same emitted output fragment covers the IEEE overflow boundary.
    This theorem starts at the canonical scaled quotient and remainder. -/
theorem floatAddNormalOutputL_top_f64 {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s ex q g t : Nat → Option (List II × Nat)}
    (sign : Bool) (qn gn rest den : Nat)
    (hs : WordCode (L := L) ρ W s (BitVec.ofNat 64 (if sign then 2^63 else 0)))
    (he : WordCode (L := L) ρ W ex (BitVec.ofNat 64 2046))
    (hq : WordCode (L := L) ρ W q (BitVec.ofNat 64 qn))
    (hg : WordCode (L := L) ρ W g (BitVec.ofNat 64 gn))
    (ht : WordCode (L := L) ρ W t (BitVec.ofNat 64 (if rest = 0 then 0 else 1)))
    (hd : 0 < den) (hr : rest < den) (hguard : gn < 8)
    (hb : 2^52 ≤ rundeInt qn (gn * den + rest) (8 * den) ∧
      rundeInt qn (gn * den + rest) (8 * den) ≤ 2^53) :
    let rounded := rundeInt qn (gn * den + rest) (8 * den)
    WordCode (L := L) ρ W
      (fun dst => floatAddNormalOutputL dst s ex q g t (2^52))
      (BitVec.ofNat 64 (zuBits f64
        (if rounded < 2^53 then ⟨sign, 2046, rounded - 2^52⟩ else ⟨sign, 2047, 0⟩))) := by
  dsimp only
  rw [← floatPackCarry_top_f64 sign _ hb]
  exact floatPackCarryL_ok hs he
    (floatGuardRoundL_ok qn gn rest den hd hr hguard hq hg ht) (2^52) (by decide)

/-- Subnormal rounding needs no hidden leading-bit subtraction. The integer
    rounded field itself encodes zero, a subnormal, or the minimum normal. -/
def floatAddSubnormalOutputL (dst : Nat)
    (sign quotient guard sticky : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 3 dst (sign dst) (floatGuardRoundL (dst + 1) quotient guard sticky)

/-- Canonical subnormal field selection, including the carry to exponent one. -/
theorem floatAddSubnormal_fields (F : Format) (sign : Bool) (n d : Nat) (E : Int)
    (hlo : F.emin - (F.p : Int) ≤ E) (hhi : E < F.emin)
    (hem : E ≤ (F.emax : Int)) (hq : subQ F n d ≤ 2^F.fracBits)
    (hf : F.fracBits = F.p - 1) :
    zuBits F (rundeBruchKern F sign n d E) =
      (if sign then 2^(F.ebits + F.fracBits) else 0) + subQ F n d := by
  unfold rundeBruchKern
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases h : subQ F n d < 2^(F.p - 1)
  · simp [h, zuBits]
  · have heq : subQ F n d = 2^F.fracBits := by rw [← hf] at h; omega
    simp [zuBits, heq, hf]

/-- Actual subnormal output with an arbitrary-denominator final remainder.
    Zero and the subnormal-to-normal carry use the very same instructions. -/
theorem floatAddSubnormalOutputL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s q g t : Nat → Option (List II × Nat)}
    (F : Format) (sign : Bool) (n d qn gn rest den : Nat) (E : Int)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (hq : WordCode (L := L) ρ W q (BitVec.ofNat 64 qn))
    (hg : WordCode (L := L) ρ W g (BitVec.ofNat 64 gn))
    (ht : WordCode (L := L) ρ W t (BitVec.ofNat 64 (if rest = 0 then 0 else 1)))
    (hd : 0 < den) (hr : rest < den) (hguard : gn < 8)
    (hquot : (n * 2^((F.p : Int) - 1 - F.emin).toNat) / d = qn)
    (hrem : (n * 2^((F.p : Int) - 1 - F.emin).toNat) % d = gn * den + rest)
    (hden : d = 8 * den)
    (hlo : F.emin - (F.p : Int) ≤ E) (hhi : E < F.emin)
    (hem : E ≤ (F.emax : Int)) (hb : subQ F n d ≤ 2^F.fracBits)
    (hf : F.fracBits = F.p - 1) :
    WordCode (L := L) ρ W (fun dst => floatAddSubnormalOutputL dst s q g t)
      (BitVec.ofNat 64 (zuBits F (rundeBruchKern F sign n d E))) := by
  have hsub : subQ F n d = rundeInt qn (gn * den + rest) (8 * den) := by
    dsimp only [subQ]
    rw [hquot, hrem, hden]
  have rounded : WordCode (L := L) ρ W (fun j => floatGuardRoundL j q g t)
      (BitVec.ofNat 64 (rundeInt qn (gn * den + rest) (8 * den))) := floatGuardRoundL_ok qn gn rest den hd hr hguard hq hg ht
  rw [← hsub] at rounded
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hs rounded (g := fun a b => some (a + b))
    rfl rfl (by decide : 3 < 256)
  rw [floatAddSubnormal_fields F sign n d E hlo hhi hem hb hf, BitVec.ofNat_add]
  intro fp K dst code top hc hK m pc hpre
  exact result hc hK m pc hpre

#print axioms floatAddNormalOutputL_ok
#print axioms floatAddSubnormal_fields
#print axioms floatAddSubnormalOutputL_ok
end Gabbro.Stage0.Senke
