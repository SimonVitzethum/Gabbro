import Grammatik.Code.Refine.Expr
import Grammatik.Code.Refine.Mono

/-
  File:      Grammatik/Code/Refine/Match/PayCode.lean
  Subject:   TRACK L, PHASE L1 -- THE PAYLOAD OF AN ARM: what `payCode` computes.

  The word of a tagged value is `i + L * (n - lo)` (`Lower/Sum.lean`); the arm of case `i` with the
  payload range `lo .. hi` finds `n` as `(word / L) + lo`: one unsigned division by the constant `L`
  (its precondition, `L` nonzero, is `i < L`; `L` is below `2^w` because the word is carried at a width
  that holds `top >= L`), one wrapping addition of `lo`, one move to the width of the payload's own
  range. All three run at the width of `min 0 lo .. max top hi`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

/-- `0 <= x` and `x < 2^w` hold for the upper end of a range that fits `w` bits. -/
theorem fits_hi_lt {lo hi : Int} {w : Nat} (h : Ar.Fits lo hi w) : hi < 2 ^ w := by
  unfold Ar.Fits at h
  by_cases hl : 0 ≤ lo
  · rw [if_pos hl] at h; exact h
  · rw [if_neg hl] at h
    exact Int.lt_of_lt_of_le h.2 (Ar.two_pow_le (by omega))

theorem payCode_fits {top : Int} {W L : Nat} {lo hi : Int} {ov : Opd} {r : Nat} {c : LR}
    (h : payCode top W L lo hi ov r = some c) : Ar.Fits (min 0 lo) (max top hi) 128 := by
  unfold payCode at h
  split at h
  · rename_i hf; exact hf
  · simp at h

theorem payCode_frag (top : Int) (W L : Nat) (lo hi : Int) (ov : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (i : Nat) (n : Int)
    (hf : Ar.Fits (min 0 lo) (max top hi) 128) (hiL : i < L) (hn1 : lo ≤ n) (hn2 : n ≤ hi)
    (hcode : (i : Int) + L * (n - lo) < top) (hTW : top < 2 ^ W) (hL : (L : Int) ≤ top)
    (hov : ov.ev rs = some (Val.ofInt W ((i : Int) + L * (n - lo)))) (hlt : OpdLt ov r)
    (c : LR) (h : payCode top W L lo hi ov r = some c) :
    Frag m rs r c (Val.ofInt (Ar.wid lo hi) n) := by
  unfold payCode at h
  rw [if_pos hf] at h
  rcases hc : cvt W (Ar.wid (min 0 lo) (max top hi)) false ov r with ⟨c1, o1, r1⟩
  rw [hc] at h
  simp only at h
  rcases hv : cvtG (.int (min 0 lo) (max top hi)) (.int lo hi) (.reg (r1 + 1)) (r1 + 2) with
    _ | ⟨c3, o3, r3⟩
  · simp [hv] at h
  simp only [hv] at h
  obtain rfl := Option.some.inj h
  have hLpos : (0 : Int) < L := by
    have h0 : (0 : Nat) < L := by omega
    exact_mod_cast h0
  have hq : 0 ≤ (n - lo) := by omega
  have hmul : 0 ≤ (L : Int) * (n - lo) := Int.mul_nonneg (Int.natCast_nonneg _) hq
  have hc0 : 0 ≤ (i : Int) + L * (n - lo) := by have := Int.natCast_nonneg i; omega
  have hWp := Ar.wid_fits hf
  have hwp := Ar.wid_pos (min 0 lo) (max top hi)
  have hUW := fits_hi_lt hWp
  -- the word at the working width
  have f1 := cvt_frag W (Ar.wid (min 0 lo) (max top hi)) false ov r m rs ((i : Int) + L * (n - lo)) hov
    (by simp only [FitS, Bool.false_eq_true, if_false]; exact ⟨hc0, by omega⟩) hlt
  rw [hc] at f1
  have ediv : Int.tdiv ((i : Int) + L * (n - lo)) L = n - lo := by
    rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg hc0, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hLpos),
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hiL)]
    omega
  have hm : top ≤ max top hi := Int.le_max_left _ _
  have hb1 : ((i : Int) + L * (n - lo)) < 2 ^ (Ar.wid (min 0 lo) (max top hi)) := by omega
  have hb2 : (L : Int) < 2 ^ (Ar.wid (min 0 lo) (max top hi)) := by omega
  have e : c1 ++ [Instr.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
        (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int)),
      Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
        (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3
      = c1 ++ ([Instr.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
        (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int))] ++
        ([Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
          (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3)) := by simp
  show Frag m rs r (c1 ++ [Instr.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
        (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int)),
      Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
        (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3, o3, r3) _
  rw [e]
  refine frag_two (ct := ([Instr.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
      (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int))] ++
      ([Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
        (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3), o3, r3)) f1 (fun rsA hag hoa hlta => ?_)
  refine frag_two (ca := [Instr.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
      (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int))]) (oa := .reg r1) (r1 := r1 + 1)
      (va := Val.ofInt (Ar.wid (min 0 lo) (max top hi)) (n - lo))
      (ct := ([Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
        (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3, o3, r3)) ?_ (fun rsB hagB hob hltb => ?_)
  · apply frag_one
    have hbin := val_bin_udiv (Ar.wid (min 0 lo) (max top hi)) ((i : Int) + L * (n - lo)) L hc0 hb1 hLpos hb2
    rw [ediv] at hbin
    have e1 : (Opd.int (Ar.wid (min 0 lo) (max top hi)) (L : Int)).ev rsA
        = some (Val.ofInt (Ar.wid (min 0 lo) (max top hi)) (L : Int)) := rfl
    simp only [stepI, hoa, e1, hbin, Option.map_some]
  · refine frag_two (ca := [Instr.bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
        (.int (Ar.wid (min 0 lo) (max top hi)) lo)]) (oa := .reg (r1 + 1)) (r1 := r1 + 2)
        (va := Val.ofInt (Ar.wid (min 0 lo) (max top hi)) n) (ct := (c3, o3, r3)) ?_
        (fun rsC hagC hoc hltc => ?_)
    · apply frag_one
      have hadd := val_bin_add (Ar.wid (min 0 lo) (max top hi)) (n - lo) lo
      rw [Int.sub_add_cancel] at hadd
      have e2 : (Opd.int (Ar.wid (min 0 lo) (max top hi)) lo).ev rsB
          = some (Val.ofInt (Ar.wid (min 0 lo) (max top hi)) lo) := rfl
      have hr1 : (Opd.reg r1).ev rsB = some (Val.ofInt (Ar.wid (min 0 lo) (max top hi)) (n - lo)) := hob
      simp only [stepI, hr1, e2, hadd, Option.map_some]
    · obtain ⟨c', hc', F⟩ := cvtG_frag (lb := lo) (hb := hi) (m := m) (rs := rsC) (z := n) hf
        (by omega) (by omega) hoc hltc
      rw [hv] at hc'
      obtain rfl := Option.some.inj hc'
      exact F

end Gabbro.Code.Lower
