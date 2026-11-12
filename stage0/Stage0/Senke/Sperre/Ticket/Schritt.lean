/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Schritt.lean
  Subject:   The one-instruction lemma the ticket lock needs beyond `Sperre/Schritt.lean`: `cas` on the serving word
             at `a + 8` (its address in slot `e`, the expected serving ticket in slot `x`, the ticket after it in
             slot `x + 1`; the old serving word into slot `d`).
-/
module
public import Stage0.Senke.Sperre.Schritt
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- `cas d e x` on the serving word: its address in slot `e`, the expected serving ticket in slot `x`, the next one
    in slot `x + 1`; the old serving word into slot `d`. -/
theorem ls_cas_serve (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {i d e x : Nat} {D A X : Int}
    (hi : code[i]? = some (ci 22 D A X)) (hD : D = ((s + d : Nat) : Int)) (hA : A = ((s + e : Nat) : Int))
    (hX : X = ((s + x : Nat) : Int)) (hd : d < 18) (he : e < 18) (hx : x + 1 < 18)
    (hae : f e = BitVec.ofNat 64 (a + 8)) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f d c) o (if c = f x then f (x + 1) else c) w := by
  subst hD hA hX
  have hI := E.ins h.ag hi
  simp only [ci] at hI
  have hs := E.small
  have hcas := cas_spec (e := f x) (n := f (x + 1)) h.c (by rw [h.ag.wr]; exact E.wr1)
  have hL1 : LS m0 (if c = f x then write m (BitVec.ofNat 64 (a + 8)) 8 (f (x + 1)).toNat else m) fp s a f
      o (if c = f x then f (x + 1) else c) w := by
    by_cases heq : c = f x
    · simp only [heq, ite_true]; exact h.count E _
    · simp only [heq, ite_false]; exact h
  generalize hm1 : (if c = f x then write m (BitVec.ofNat 64 (a + 8)) 8 (f (x + 1)).toNat else m) = m1 at hcas hL1
  have hF := E.frameK hL1.ag
  refine ⟨_, ls_star hI (by decide) ?_, hL1.slot E hd c⟩
  rw [← pc_next]
  simp only [op]
  refine f2_run hI ?_
  rw [sx_nat (d := s + e) (by omega)]
  simp only [ld]
  refine run_rd64 (h.sl e he) ?_
  refine f3_run hI ?_
  rw [sx_nat (d := s + x) (by omega)]
  refine run_rd64 (h.sl x (by omega)) ?_
  rw [slot_plus8]
  refine run_rd64 (h.sl (x + 1) hx) ?_
  rw [hae]
  refine .ask (a := some (c, 0)) (m' := m1) (by simp only [memAns, hcas]) ?_
  simp only [opt_some, ret1]
  have hI1 := E.ins hL1.ag hi
  simp only [ci] at hI1
  refine f1_run hI1 ?_
  rw [sx_nat (d := s + d) (by omega)]
  exact run_wr64 (wr64_some (hF.wr _ (by omega)))

end

end Gabbro.Stage0.Senke
