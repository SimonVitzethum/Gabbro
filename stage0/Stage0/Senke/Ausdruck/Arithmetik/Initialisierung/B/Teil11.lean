module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil10

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxHeartbeats 6000000 in
theorem floatFiniteAddL_read_fields_align_bounds {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : ℕ) (a b : ℕ → Option (List II × ℕ)) (wa wb : Runner.W) {top K reserved : ℕ} {fp pc : Runner.W} {m : Runner.Mem} (width : F.fracBits + F.ebits < 64) (lower : FB ≤ dst + 1) (frac : F.fracBits < 64) (mask : 2 ^ F.ebits - 1 < 2 ^ 64) (fracMask : 2 ^ F.fracBits - 1 < 2 ^ 64) (hiddenBound : 2 ^ F.fracBits < 2 ^ 64) (room : top ≤ K) (sortRoom : dst + 11 < K) (alignRoom : dst + 17 ≤ K) (executed : List II) (before : Runner.Mem) (it : ℕ) (hi : floatStateSlotsL (dst + 1)
        ([a, b, fun j =>
            floatFieldL (F.fracBits + F.ebits) 1 j fun k => some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 1) 0], k + 1), fun j =>
            floatFieldL (F.fracBits + F.ebits) 1 j fun k => some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 2) 0], k + 1)] ++
          finiteAddRemaining F dst) =
      some (executed, it)) :
    @floatFiniteAddL_read_fields_align_boundsCase _ D L Γ ρ W F dst a b wa wb top K reserved fp pc m width lower frac mask fracMask hiddenBound room sortRoom alignRoom executed before it hi := by
  delta floatFiniteAddL_read_fields_align_boundsCase
  intro values out sorted fieldValues aligned shift hs rounded hr continuation ex ey q r rx ry rq rr dominance final jammed finalPre keep vs vreads signedOut signedRun signedAgree wholeRun wholeAgree normalization zeroMem zeroRun zeroAgree cmpPre qr tested testRun testAgree testedPre
  intro bounds
  have hfield (i : Nat) (hi : i < 4) :
      values (dst+5+i) = finiteAddRemainingValue F wa wb i := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fieldValues (i+4) (by omega)
  have h5 := hfield 0 (by omega)
  have h6 := hfield 1 (by omega)
  have h7 := hfield 2 (by omega)
  have h8 := hfield 3 (by omega)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h5 h6 h7 h8
  have b0 := bounds 0 (by omega)
  have b1 := bounds 1 (by omega)
  have b2 := bounds 2 (by omega)
  have b3 := bounds 3 (by omega)
  simp only [Nat.reduceLT, ↓reduceIte] at b0 b1 b2 b3
  have orderedBounds (i : Nat) (hi : i = dst+5 ∨ i = dst+6 ∨ i = dst+7 ∨ i = dst+8) :
      if i < dst+7 then 1 ≤ (vs i).toNat ∧ (vs i).toNat < F.bexpMax
      else (vs i).toNat < 2^56 := by
    have rd := (keep i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).trans
      (sorted i (by rcases hi with rfl | rfl | rfl | rfl <;> omega))
    have eq := Option.some.inj ((vreads i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).symm.trans rd)
    rw [eq]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [h5,h6,h7,h8] <;> split <;> assumption
  have bx := orderedBounds (dst+5) (by omega)
  have byy := orderedBounds (dst+6) (by omega)
  have bq := orderedBounds (dst+7) (by omega)
  have br := orderedBounds (dst+8) (by omega)
  simp only [show dst+5 < dst+7 by omega, show dst+6 < dst+7 by omega,
    show ¬dst+8 < dst+7 by omega, Nat.lt_irrefl, ↓reduceIte] at bx byy bq br
  have req : vs (dst+8) = r := Option.some.inj
    ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rr))
  have jeq : vs (dst+16) = floatShiftJamWord r (ex-ey) :=
    Option.some.inj ((vreads _ (by omega)).symm.trans jammed)
  have bj : (vs (dst+16)).toNat < 2^56 := by
    rw [jeq, floatShiftJamWord, BitVec.toNat_or]
    apply Nat.or_lt_two_pow
    · rw [BitVec.toNat_ushiftRight]
      exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (req ▸ br)
    · unfold Runner.IR.bool
      split <;> decide
  have iq : (vs (dst+7)).toInt = ((vs (dst+7)).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have ij : (vs (dst+16)).toInt = ((vs (dst+16)).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have resultBounds :
      -2^57 < (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt ∧
      (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt < 2^57 := by
    split
    · rw [BitVec.toInt_add, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
      omega
    · rw [BitVec.toInt_sub, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
      omega
  have exactResult :
      (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt =
      (if vs (dst+3) == vs (dst+4) then
        ((vs (dst+7)).toNat : Int)+(vs (dst+16)).toNat else
        ((vs (dst+7)).toNat : Int)-(vs (dst+16)).toNat) := by
    split
    · rw [BitVec.toInt_add, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
    · rw [BitVec.toInt_sub, iq, ij, Int.bmod_eq_of_le (by omega) (by omega)]
  -- Equal signs and equal exponents use only the retained word bounds.
  -- Canonical decoded inputs below also discharge unequal-exponent subtraction.
  have positiveResult : (vs (dst+3) = vs (dst+4) ∨ vs (dst+5) = vs (dst+6)) →
      (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)) ≠ 0 →
      0 < (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt := by
    intro cases nonzero
    have nz : (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt ≠ 0 := by
      simpa [← BitVec.toInt_inj] using nonzero
    rw [exactResult] at nz ⊢
    rcases cases with same | equal
    · simp only [same, beq_self_eq_true, ↓reduceIte] at nz ⊢
      omega
    · have eqx : vs (dst+5) = ex := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rx))
      have eqy : vs (dst+6) = ey := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans ry))
      have eqq : vs (dst+7) = q := Option.some.inj
        ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rq))
      have ee : ex = ey := eqx.symm.trans (equal.trans eqy)
      have jr : vs (dst+16) = r := by
        rw [jeq, ee]
        simp [floatShiftJamWord, Runner.IR.bool]
      have order := dominance.2 ee.symm
      have ir : r.toInt = (r.toNat : Int) :=
        BitVec.toInt_eq_toNat_of_lt (by rw [← req]; omega)
      rw [← eqq, iq, ir] at order
      rw [jr] at nz ⊢
      by_cases hs : vs (dst+3) = vs (dst+4) <;>
        simp [hs] at nz ⊢ <;> omega
  have canonicalPositive : ∀ (x y : Gleitkomma.GBits F), F.dicht →
      F.ebits + F.fracBits + 1 ≤ 64 → F.fracBits ≤ 52 → 1 < F.bexpMax →
      Gleitkomma.wf F x → Gleitkomma.wf F y →
      x.bexp ≠ F.bexpMax → y.bexp ≠ F.bexpMax →
      wa = BitVec.ofNat 64 (Gleitkomma.zuBits F x) →
      wb = BitVec.ofNat 64 (Gleitkomma.zuBits F y) →
      (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)) ≠ 0 →
      0 < (if vs (dst+3) == vs (dst+4) then
        vs (dst+7)+vs (dst+16) else vs (dst+7)-vs (dst+16)).toInt := by
    intro x y dense wide precision expmax hx hy fx fy ax ay nz
    by_cases same : vs (dst+3) = vs (dst+4)
    · exact positiveResult (Or.inl same) nz
    by_cases equal : vs (dst+5) = vs (dst+6)
    · exact positiveResult (Or.inr equal) nz
    have eqx : vs (dst+5) = ex := Option.some.inj
      ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rx))
    have eqy : vs (dst+6) = ey := Option.some.inj
      ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans ry))
    have eqq : vs (dst+7) = q := Option.some.inj
      ((vreads _ (by omega)).symm.trans ((keep _ (by omega)).trans rq))
    have expcap : F.bexpMax < 2^63 := by
      have cap := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat))
        (show F.ebits ≤ 63 by omega)
      have hd := dense
      unfold Gleitkomma.Format.dicht at hd
      omega
    have order : (vs (dst+6)).toNat < (vs (dst+5)).toNat := by
      have ix : ex.toInt = (ex.toNat : Int) :=
        BitVec.toInt_eq_toNat_of_lt (by rw [← eqx]; omega)
      have iy : ey.toInt = (ey.toNat : Int) :=
        BitVec.toInt_eq_toNat_of_lt (by rw [← eqy]; omega)
      have ne : (vs (dst+5)).toNat ≠ (vs (dst+6)).toNat := by
        intro h
        exact equal (BitVec.eq_of_toNat_eq h)
      have dom := dominance.1
      rw [ix,iy,← eqx,← eqy] at dom
      omega
    have selected (i : Nat) (hi : i = dst+5 ∨ i = dst+6 ∨ i = dst+7 ∨ i = dst+8) :=
      Option.some.inj ((vreads i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).symm.trans
        ((keep i (by rcases hi with rfl | rfl | rfl | rfl <;> omega)).trans
          (sorted i (by rcases hi with rfl | rfl | rfl | rfl <;> omega))))
    have s5 := selected (dst+5) (by omega)
    have s6 := selected (dst+6) (by omega)
    have s7 := selected (dst+7) (by omega)
    have s8 := selected (dst+8) (by omega)
    have jamEq : vs (dst+16) =
        floatShiftJamWord (vs (dst+8)) (vs (dst+5)-vs (dst+6)) := by
      rw [jeq,req,eqx,eqy]
    simp only [same, beq_iff_eq, ↓reduceIte]
    rw [jamEq]
    by_cases swap : ((values (dst+5)).slt (values (dst+6)) ||
      ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8)))) = true
    · simp only [swap, ↓reduceIte] at s5 s6 s7 s8
      simp [h5,h6,h7,h8] at s5 s6 s7 s8
      rw [s5,s6] at order
      rw [s5,s6,s7,s8]
      simpa [finiteAddRemainingValue,ax,ay] using
        (finiteAddRemainingValue_unequal_positive F dense wide precision expmax
          y x hy hx fy fx (by simpa [finiteAddRemainingValue,ax,ay] using order))
    · simp only [swap, ↓reduceIte] at s5 s6 s7 s8
      simp [h5,h6,h7,h8] at s5 s6 s7 s8
      rw [s5,s6] at order
      rw [s5,s6,s7,s8]
      simpa [ax,ay] using (finiteAddRemainingValue_unequal_positive F dense wide precision expmax
        x y hx hy fx fy (by simpa [ax,ay] using order))
  refine ⟨vs (dst+5),vs (dst+6),?_,?_,bx.1,bx.2,byy.1,byy.2,bq,bj,
    resultBounds.1,resultBounds.2,positiveResult,canonicalPositive, r, (keep _ (by omega)).trans rr, ?_⟩
  · exact slotRead_agree finalPre.frame signedAgree (by omega) (by omega)
      (vreads _ (by omega))
  · exact slotRead_agree finalPre.frame signedAgree (by omega) (by omega)
      (vreads _ (by omega))
  · dsimp only
    let den : Int := (2^(vs (dst+5)-vs (dst+6)).toNat : Nat)
    let n : Int := if vs (dst+3) == vs (dst+4) then
      ((vs (dst+7)).toNat : Int)*den + r.toNat else
      ((vs (dst+7)).toNat : Int)*den - r.toNat
    have hd : 0 < den := by
      dsimp only [den]
      exact_mod_cast (Nat.pow_pos (n := (vs (dst+5)-vs (dst+6)).toNat)
        (by decide : 0 < 2))
    have remBounds : 0 ≤ n%den ∧ n%den < den :=
      ⟨Int.emod_nonneg _ (ne_of_gt hd), Int.emod_lt_of_pos _ hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [exactResult]
      split <;> ring
    · have h := floatSumMagnitude_reconstruct (n/den) (n%den) den hd remBounds
      have eq : n/den*den+n%den = n := by
        simpa [Int.mul_comm] using Int.mul_ediv_add_emod n den
      simpa only [eq] using h
    · have h := floatSumSign_exact (n/den) (n%den) den hd remBounds
      have eq : n/den*den+n%den = n := by
        simpa [Int.mul_comm] using Int.mul_ediv_add_emod n den
      simpa only [eq] using h
    · constructor
      · intro h
        simp only [h, Int.zero_ediv, Int.zero_emod, and_self]
      · rintro ⟨hq, hr⟩
        have h := Int.mul_ediv_add_emod n den
        rw [hq, hr] at h
        change n = 0
        simpa only [Int.mul_zero, Int.zero_add] using h.symm

end Gabbro.Stage0.Senke
