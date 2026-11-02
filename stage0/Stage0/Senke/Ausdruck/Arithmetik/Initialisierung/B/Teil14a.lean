module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil13

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

#print axioms floatFiniteAddL_left_body_exact

/-- Nonzero magnitude, positive exponent and a negative exact correction
    jointly exercise the actual body and its reconstruction equation. -/
theorem floatFiniteAddL_left_body_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (tail : List II) (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    (∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 26 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 3 ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved) ∧
    (205 : Int)*2 = 26*16 + 2*(-3) := by
  constructor
  · simpa using floatFiniteAddL_left_body tail room rq re pre
  · decide

#print axioms floatFiniteAddL_left_body_zeuge

/-- Exact reconstruction at the actual left-loop head. The signed jam
    correction scales with the emitted doubling; the exponent records that scale. -/
structure FiniteLeftInvariant (numerator den correction initialExponent : Int)
    (steps : Nat) (q ex : Int) : Prop where
  positive : 0 < q
  bounded : q < 2^57
  exponent : 1 ≤ ex
  exponentBound : ex < 2^63
  scale : ex + steps = initialExponent
  exactValue : numerator * 2^steps = q*den + correction * 2^steps

/-- Preservation uses the actual body arithmetic, including its correction.
    The left condition supplies the tighter bound before doubling. -/
theorem FiniteLeftInvariant.step
    {n d c e q ex : Int} {steps : Nat}
    (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex) :
    FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  constructor
  · refine ⟨by have := inv.positive; omega, by omega, by omega,
      by have := inv.exponentBound; omega, ?_, ?_⟩
    · push_cast
      have := inv.scale
      omega
    · rw [pow_succ]
      have h := congrArg (fun x : Int => x*2) inv.exactValue
      nlinarith
  · omega

/-- One reached Runner state carries execution, frame, both updated reads,
    exact reconstruction and the decreasing loop measure together. This is
    the literal left body, without asserting execution of its back edge. -/
theorem floatFiniteAddL_left_body_invariant {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved steps : Nat} {n d c e q ex : Int} (tail : List II)
    (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 q))
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 ex))
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 (2*q)) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 (ex-1)) ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved ∧
      FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  obtain ⟨out,run,agree,readQ,readE,next⟩ :=
    floatFiniteAddL_left_body tail room rq re pre
  have arithmetic := floatFiniteAddL_left_body_exact q ex d 0 (q*d)
    (by have := inv.positive; omega) guard running inv.exponentBound (by ring)
  have eqQ : BitVec.ofInt 64 q * 2 = BitVec.ofInt 64 (2*q) := by
    rw [← arithmetic.1, BitVec.ofInt_toInt]
  have eqE : BitVec.ofInt 64 ex - 1 = BitVec.ofInt 64 (ex-1) := by
    rw [← arithmetic.2.1, BitVec.ofInt_toInt]
  rw [eqQ] at readQ
  rw [eqE] at readE
  exact ⟨out,run,agree,readQ,readE,next,inv.step guard running⟩

/-- A negative jam correction and a nonzero mantissa satisfy all invariant
    fields jointly, and remain so after an actual body's arithmetic. -/
theorem finiteLeftInvariant_zeuge :
    FiniteLeftInvariant 205 16 (-3) 4 0 13 4 ∧
    FiniteLeftInvariant 205 16 (-3) 4 1 26 3 ∧
    (3 : Int).toNat < (4 : Int).toNat := by
  have initial : FiniteLeftInvariant 205 16 (-3) 4 0 13 4 := by
    constructor <;> norm_num
  exact ⟨initial, initial.step (by norm_num) (by norm_num)⟩

#print axioms FiniteLeftInvariant.step
#print axioms floatFiniteAddL_left_body_invariant
#print axioms finiteLeftInvariant_zeuge

/-- The execution witness shares its reads, frame and exact invariant;
    the correction is negative and the significand is nonzero. -/
theorem floatFiniteAddL_left_body_invariant_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (tail : List II) (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 13)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 4)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some 26 ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some 3 ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved ∧
      FiniteLeftInvariant 205 16 (-3) 4 1 26 3 ∧
      (3 : Int).toNat < (4 : Int).toNat := by
  exact floatFiniteAddL_left_body_invariant tail finiteLeftInvariant_zeuge.1
    (by norm_num) (by norm_num) room rq re pre

#print axioms floatFiniteAddL_left_body_invariant_zeuge

/-- Initialize the scaled invariant from the retained exact ADD/SUB equation.
    Positivity is deliberately explicit: NONZERO alone does not imply it. -/
theorem FiniteLeftInvariant.of_retained
    {n d c q ex : Int} (positive : 0 < q) (bound : q < 2^57)
    (exponent : 1 ≤ ex) (exponentBound : ex < 2^63)
    (exactValue : n = q*d+c) :
    FiniteLeftInvariant n d c ex 0 q ex := by
  refine ⟨positive,bound,exponent,exponentBound,by simp,?_⟩
  simpa using exactValue

/-- The actual BRZ after the left condition enters the literal body on a
    nonzero flag. Execution of the condition itself is a separate obligation. -/
theorem floatFiniteAddL_left_test_enter {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (body tail : List II)
    (room : dst+9 < K)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some 1)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 19 (dst+9) 96 0] ++ body ++ tail) ρ W reserved) :
    Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m ∧
    Pre L m (pc+16) fp K (dst+5) (body++tail) ρ W reserved := by
  have hp : Pre L m pc fp K (dst+5)
      ([ci 19 (dst+9) 96 0] ++ (body++tail)) ρ W reserved := by
    simpa only [List.append_assoc] using pre
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int))
      (II.f 96) (II.f 0) := by
    simpa [ci] using hp.code 0 (by simp)
  have rd : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some 1 := by
    rw [sx_nat (by have := hp.small; omega)]
    exact flag
  constructor
  · exact Star.one (by simpa [nxt] using
      (run_step (t := ⟨pc,fp⟩) ins (by decide)
        (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins rd (by decide))))
  · simpa using hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)

/-- Connect the literal left body to its actual backedge. The offset is
    determined by the condition length, as in floatFiniteAddL. -/
theorem floatFiniteAddL_left_body_backedge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {head fp : Runner.W}
    {K dst reserved steps conditionLength : Nat} {n d c e q ex : Int}
    (tail : List II) (inv : FiniteLeftInvariant n d c e steps q ex)
    (guard : q < 2^56) (running : 1 < ex)
    (offsetRange : lit32 (-(16*((conditionLength+5 : Nat) : Int))) = true)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 q))
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 ex))
    (pre : Pre L m (head+BitVec.ofNat 64 (16*(conditionLength+1))) fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++
       [ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨head+BitVec.ofNat 64 (16*(conditionLength+1)),fp⟩ m ⟨head,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (BitVec.ofInt 64 (2*q)) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (BitVec.ofInt 64 (ex-1)) ∧
      FiniteLeftInvariant n d c e (steps+1) (2*q) (ex-1) ∧
      (ex-1).toNat < ex.toNat := by
  obtain ⟨out,run,agree,readQ,readE,next,updated,decreasing⟩ :=
    floatFiniteAddL_left_body_invariant
      ([ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0] ++ tail)
      inv guard running room rq re (by simpa only [List.append_assoc] using pre)
  have ins := next.code 0 (by simp)
  simp only [List.getElem_append_left (by simp : 0 < [ci 18 (-(16*((conditionLength+5 : Nat) : Int))) 0 0].length),
    List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  simp only [ci] at ins
  have jump := run_step (t := ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) ins (by decide) (run_jmp (t := ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) ins)
  have off : sx (II.f (-(16*((conditionLength+5 : Nat) : Int)))) =
      -BitVec.ofNat 64 (16*(conditionLength+5)) := by
    rw [sx_lit offsetRange, BitVec.ofInt_neg]
    congr 1
  have pcEq : head+BitVec.ofNat 64 (16*(conditionLength+1))+64 =
      head+BitVec.ofNat 64 (16*(conditionLength+5)) := by
    change head+BitVec.ofNat 64 (16*(conditionLength+1))+BitVec.ofNat 64 64 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2 <;> omega
  have finish : Star ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩ out
      ⟨head,fp⟩ out := by
    apply Star.one
    change Run (step ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64,fp⟩) out
      ⟨head+BitVec.ofNat 64 (16*(conditionLength+1))+64+sx (II.f (-(16*((conditionLength+5 : Nat) : Int)))),fp⟩ out at jump
    rw [off,pcEq] at jump
    simpa only [pcEq,← BitVec.sub_eq_add_neg,BitVec.add_sub_cancel] using jump
  exact ⟨out,run.trans finish,agree,readQ,readE,updated,decreasing⟩

#print axioms FiniteLeftInvariant.of_retained
#print axioms floatFiniteAddL_left_test_enter
#print axioms floatFiniteAddL_left_body_backedge


end Gabbro.Stage0.Senke
