module
public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil13a

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil12

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Execute the rounding expression used literally by the finite candidate.
    This rounds the retained normalized word, not an independently supplied
    quotient/guard/tail triple. Relating that word to the original exact
    numerator remains the normalization continuation's obligation. -/
theorem floatFiniteAddL_round_retained {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst input top reserved : Nat} {code : List II} (q : Int)
    (range : 0 ≤ q ∧ q < 2^63)
    (compiled : floatGuardRoundL dst
      (fun j => wordK 6 j (some ([ci 2 j input 0],j+1)) 8)
      (fun j => wordK 8 j (some ([ci 2 j input 0],j+1)) 7)
      (fun j => some ([ci 1 j 0 0],j+1)) = some (code,top))
    (room : top ≤ K) (dstRoom : dst ≤ K)
    (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 q))
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code
      (· = BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat (q%8).toNat 8)) := by
  apply retainedWordCode_ok (BitVec.ofInt 64 q) _
    (fun load j => floatGuardRoundL j
      (fun k => wordK 6 k (load k) 8)
      (fun k => wordK 8 k (load k) 7)
      (fun k => some ([ci 1 k 0 0],k+1))) ?_ compiled room dstRoom lower retained read pre
  intro Δ η load
  have div := sdiv_w (a := q) (b := 8)
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
  rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg range.1] at div
  have quotient : WordCode (L := L) η (fun _ => True)
      (fun j => wordK 6 j (some ([ci 2 j input 0],j+1)) 8)
      (BitVec.ofNat 64 (q/8).toNat) := by
    have h : WordCode (L := L) η (fun _ => True) _ (BitVec.ofInt 64 (q/8)) := WordCode.bin load (WordCode.const 8 (by decide)) div
      (rfl : op 6 = bin sdiv) (by decide : 6 < 256)
    have eq : BitVec.ofInt 64 (q/8) = BitVec.ofNat 64 (q/8).toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg (Int.ediv_nonneg range.1 (by decide))]
    rw [eq] at h
    intro fp K j c t hc ht mm pp hp
    exact h (by simpa [wordK, Nat.add_assoc] using hc) ht mm pp
      (by simpa [wordK, Nat.add_assoc] using hp)
  have guard : WordCode (L := L) η (fun _ => True)
      (fun j => wordK 8 j (some ([ci 2 j input 0],j+1)) 7)
      (BitVec.ofNat 64 (q%8).toNat) := by
    have h : WordCode (L := L) η (fun _ => True) _ (BitVec.ofInt 64 q &&& 7) := WordCode.bin load (WordCode.const 7 (by decide))
      (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
    have eq : BitVec.ofInt 64 q &&& 7 = BitVec.ofNat 64 (q%8).toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [show (7 : Runner.W) = BitVec.ofNat 64 (2^3-1) from rfl,
        BitVec.toNat_and, BitVec.toNat_ofNat]
      simp only [show (2^3-1) % 2^64 = 7 from rfl]
      rw [show 7 = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt range.1 (by omega)]
      rw [BitVec.toNat_ofNat, Int.toNat_emod range.1 (by decide)]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [eq] at h
    intro fp K j c t hc ht mm pp hp
    exact h (by simpa [wordK, Nat.add_assoc] using hc) ht mm pp
      (by simpa [wordK, Nat.add_assoc] using hp)
  have rounded : WordCode (L := L) η (fun _ => True) _
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat ((q%8).toNat * 1 + 0) (8*1))) := floatGuardRoundL_ok (q/8).toNat (q%8).toNat 0 1
    (by decide) (by decide) (by omega) quotient guard
    (WordCode.const 0 (by decide))
  intro fp K j c t hc ht mm pp hp
  simpa using rounded hc ht mm pp hp

#print axioms floatFiniteAddL_round_retained

/-- An odd halfway significand is incremented by the actual retained-load
    expression, with all execution premises shared in one frame. -/
theorem floatFiniteAddL_round_retained_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K reserved : Nat}
    (read : m.rd64 (slot fp 23) = some 44)
    (room : 40 ≤ K)
    (pre : Pre L m pc fp K 32
      ((floatGuardRoundL 32
        (fun j => wordK 6 j (some ([ci 2 j 23 0],j+1)) 8)
        (fun j => wordK 8 j (some ([ci 2 j 23 0],j+1)) 7)
        (fun j => some ([ci 1 j 0 0],j+1))).getD ([],0)).1 ρ W reserved) :
    Ok m pc fp K 32
      ((floatGuardRoundL 32
        (fun j => wordK 6 j (some ([ci 2 j 23 0],j+1)) 8)
        (fun j => wordK 8 j (some ([ci 2 j 23 0],j+1)) 7)
        (fun j => some ([ci 1 j 0 0],j+1))).getD ([],0)).1
      (· = 6) := by
  exact floatFiniteAddL_round_retained 44 (by decide) rfl
    (by change 38 ≤ K; omega)
    (by omega) (by decide) (by decide) read pre

#print axioms floatFiniteAddL_round_retained_zeuge

set_option maxHeartbeats 1200000 in
/-- Execute the four literal instructions in the candidate's left-normalization
    body. Both retained fields are updated in one run; the exponent lives below
    the quotient, so the agreement boundary is the exponent slot. -/
theorem floatFiniteAddL_left_body {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex : Runner.W} (tail : List II)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (pre : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0, ci 5 (dst+7) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0, ci 4 (dst+5) (dst+5) (dst+10)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+5) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (q*2) ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some (ex-1) ∧
      Pre L out (pc+64) fp K (dst+5) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+5)
      ([ci 1 (dst+10) 2 0] ++ ([ci 5 (dst+7) (dst+7) (dst+10)] ++
        ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+5) (dst+5) (dst+10)] ++ tail)))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,rfl⟩ := const_ok (d := dst+10)
    {hp.left with ctx := by have := hp.ctx; omega} (by decide) (by omega)
  have h1 := hp.next (a1.mono (by omega : dst+5 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rq1 := slotRead_agree hp.frame a1 (by omega) (by omega) rq
  obtain ⟨m2,s2,a2,w2,r2,rfl⟩ := eng_bin_ok (d := dst+7) (a := dst+7) (b := dst+10)
    {h1.left with ctx := by have := hp.ctx; omega} (by omega) (by omega) (by omega)
    rq1 r1 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h2 := h1.next (a2.mono (by omega : dst+5 ≤ dst+7)) (Nat.le_refl _) (by omega)
  obtain ⟨m3,s3,a3,w3,r3,rfl⟩ := const_ok (d := dst+10)
    {h2.left with ctx := by have := hp.ctx; omega} (by decide) (by omega)
  have h3 := h2.next (a3.mono (by omega : dst+5 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have re3 := slotRead_agree hp.frame
    ((a1.mono (by omega : dst+7 ≤ dst+10)).trans
      (a2.trans (a3.mono (by omega : dst+7 ≤ dst+10)))) (by omega) (by omega) re
  let out := write m3 (slot fp (BitVec.ofNat 64 (dst+5))) 8 (ex-1).toNat
  obtain ⟨wr4,r4,a4⟩ := wr_slot h3.frame (by omega : dst+5 < K) (ex-1)
  have s4 : Star ⟨pc+16+16+16,fp⟩ m3 ⟨pc+16+16+16+16,fp⟩ out := by
    apply star_ins h3.left.code (by simp [ci])
    have ins := h3.left.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
    simp only [ci, op]
    have sx5 : sx (II.f ((dst : Int)+5)) = BitVec.ofNat 64 (dst+5) := by
      exact_mod_cast (sx_nat (d := dst+5) (by have := h3.small; omega))
    have sx10 : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := h3.small; omega))
    apply run_bin (g := fun x y => some (x-y)) (va := ex) (vb := 1) (r := ex-1) ins
    · simpa only [sx5] using re3
    · simpa [sx10] using r3
    · rfl
    · simpa only [sx5] using wr4
  have done := h3.next a4 (Nat.le_refl _) (by omega)
  have rq3 := slotRead_agree h2.frame a3 (by omega) (by omega) r2
  have rq4 : out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (q*2) := by
    change (write m3 _ 8 _).rd64 _ = _
    rw [rd64_write_far]
    · exact rq3
    · unfold Far
      rw [slot_toNat h3.frame.room (by omega : dst+5 < K),
        slot_toNat h3.frame.room (by omega : dst+7 < K)]
      have := h3.frame.lt
      omega
  refine ⟨out,?_,(a1.mono (by omega)).trans ((a2.mono (by omega)).trans
    ((a3.mono (by omega)).trans a4)),rq4,r4,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans s4))
  · simpa [out, BitVec.add_assoc] using done


#print axioms floatFiniteAddL_left_body

/-- The actual left body doubles the jammed word, rather than transferring an
    exact remainder bit. Carry the signed correction explicitly: it doubles too.
    This states the invariant needed by this candidate, without identifying it
    with the separate adaptive normalization routine. -/
theorem floatFiniteAddL_left_body_exact (q ex den correction numerator : Int)
    (hq : 0 ≤ q) (small : q < 2^56) (he : 1 < ex) (expBound : ex < 2^63)
    (exactRest : numerator = q*den+correction) :
    (BitVec.ofInt 64 q * 2).toInt = 2*q ∧
    (BitVec.ofInt 64 ex - 1).toInt = ex-1 ∧
    0 ≤ 2*q ∧ 2*q < 2^57 ∧ 1 ≤ ex-1 ∧
    numerator*2 = (2*q)*den + 2*correction := by
  have iq : (BitVec.ofInt 64 q).toInt = q :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  have ie : (BitVec.ofInt 64 ex).toInt = ex :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  refine ⟨?_,?_,by omega,by omega,by omega,?_⟩
  · rw [BitVec.toInt_mul, iq]
    change (q*2).bmod (2^64) = 2*q
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  · rw [BitVec.toInt_sub, ie]
    change (ex-1).bmod (2^64) = ex-1
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
  · rw [exactRest]
    ring

end Gabbro.Stage0.Senke
