import Grammatik.Code.Refine.Match.Opt

/-
  File:      Grammatik/Code/Refine/Match/Case.lean
  Subject:   TRACK L, PHASE L1 -- THE `case` EXPRESSION: what `numCode` computes.

  A tagged value of case `i` with a payload `n` in `lo .. hi` has the word `i + L * (n - lo)`
  (`Lower/Sum.lean`). The code moves the payload to the width of the word, subtracts `lo`, multiplies by
  `L` and adds `i`: three wrapping instructions, no precondition. Wrapping is harmless because the
  word is the exact result and below `2^w`, and a narrower payload is moved by `trunc`, exact modulo `2^w`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

theorem numCode_frag {lo hi : Int} (W L i : Nat) (n : Int) (hf : Ar.Fits lo hi 128) (h1 : lo ≤ n) (h2 : n ≤ hi)
    (oe : Opd) (r : Nat) (m : Mem) (rs : Regs)
    (hev : oe.ev rs = some (Val.ofInt (Ar.wid lo hi) n)) (hlt : OpdLt oe r) :
    Frag m rs r (numCode lo hi W L i oe r) (Val.ofInt W ((i : Int) + L * (n - lo))) := by
  unfold numCode
  rcases hc : cvt (Ar.wid lo hi) W (decide (lo < 0)) oe r with ⟨c1, o1, r2⟩
  simp only
  have f1 := cvt_frag (Ar.wid lo hi) W (decide (lo < 0)) oe r m rs n hev
    (fitS_of_fits (Ar.wid_fits hf) (by have := Ar.wid_pos lo hi; omega) h1 h2) hlt
  rw [hc] at f1
  have e : c1 ++ [Instr.bin r2 .sub W o1 (.int W lo), Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int)),
        Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))]
      = c1 ++ ([Instr.bin r2 .sub W o1 (.int W lo)] ++ ([Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int))] ++
        [Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))])) := by simp only [List.cons_append, List.nil_append]
  show Frag m rs r (c1 ++ [Instr.bin r2 .sub W o1 (.int W lo), Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int)),
        Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))], .reg (r2 + 2), r2 + 3) _
  rw [e]
  refine frag_two (ct := ([Instr.bin r2 .sub W o1 (.int W lo)] ++ ([Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int))] ++
        [Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))]), .reg (r2 + 2), r2 + 3)) f1
    (fun rsA hag hoa hlta => ?_)
  refine frag_two (ca := [Instr.bin r2 .sub W o1 (.int W lo)]) (oa := .reg r2) (r1 := r2 + 1)
    (va := Val.ofInt W (n - lo))
    (ct := ([Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int))] ++
        [Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))], .reg (r2 + 2), r2 + 3)) ?_
    (fun rsB hagB hob hltb => ?_)
  · apply frag_one
    have hsub := val_bin_sub W n lo
    have e1 : (Opd.int W lo).ev rsA = some (Val.ofInt W lo) := rfl
    simp only [stepI, hoa, e1, hsub, Option.map_some]
  · refine frag_two (ca := [Instr.bin (r2 + 1) .mul W (.reg r2) (.int W (L : Int))]) (oa := .reg (r2 + 1))
      (r1 := r2 + 2) (va := Val.ofInt W ((n - lo) * L))
      (ct := ([Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int))], .reg (r2 + 2), r2 + 3)) ?_
      (fun rsC hagC hoc hltc => ?_)
    · apply frag_one
      have hmul := val_bin_mul W (n - lo) (L : Int)
      have e2 : (Opd.int W (L : Int)).ev rsB = some (Val.ofInt W (L : Int)) := rfl
      have hr : (Opd.reg r2).ev rsB = some (Val.ofInt W (n - lo)) := hob
      simp only [stepI, hr, e2, hmul, Option.map_some]
    · have hadd := val_bin_add W ((n - lo) * L) (i : Int)
      have e3 : (Opd.int W (i : Int)).ev rsC = some (Val.ofInt W (i : Int)) := rfl
      have hr : (Opd.reg (r2 + 1)).ev rsC = some (Val.ofInt W ((n - lo) * L)) := hoc
      have eq : (n - lo) * (L : Int) + (i : Int) = (i : Int) + L * (n - lo) := by
        rw [Int.mul_comm (n - lo) (L : Int), Int.add_comm]
      rw [eq] at hadd
      exact frag_one m rsC (r2 + 2) (Instr.bin (r2 + 2) .add W (.reg (r2 + 1)) (.int W (i : Int)))
        (Val.ofInt W ((i : Int) + L * (n - lo)))
        (by simp only [stepI, hr, e3, hadd, Option.map_some])

end Gabbro.Code.Lower
