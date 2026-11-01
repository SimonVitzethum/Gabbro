/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Eng.lean
  Subject:   Expression narrowing (`eng`) of an integer of any width.

  The input is evaluated once and extended in place to the width at which its interval and the narrowed bounds
  are all in the signed range. `wideOutC` leaves the operand untouched and a flag word `x ∉ [lo', hi']` in slot
  `d + k + 3`. A flag of zero branches over the fallback: the narrowed value is the first limbs already in
  place. A flag of one falls into the fallback, evaluated into `d`.
-/
import Stage0.Senke.Ausdruck.Aggregat.WideInt.Compare
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Eng

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

section
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat} {c : List II} {top : Nat}
variable {m : Runner.Mem} {pc : Runner.W}

theorem wideEng_ok {lo hi lo' hi' : Int} (x : Zahl lo hi) (fallback result : Zahl lo' hi')
    (inside : lo' ≤ x.n ∧ x.n ≤ hi' → result.n = x.n)
    (outside : ¬ (lo' ≤ x.n ∧ x.n ≤ hi') → result = fallback)
    {fe fb : Nat → Option (List II × Nat)}
    (ihe : ∀ ce te, fe d = some (ce, te) → te ≤ K → ∀ m pc, Pre L m pc fp K d ce ρ W reserved →
      ValueOk L m pc fp K d ce (.int lo hi) x)
    (ihb : ∀ cb tb, fb d = some (cb, tb) → tb ≤ K → ∀ m pc, Pre L m pc fp K d cb ρ W reserved →
      ValueOk L m pc fp K d cb (.int lo' hi') fallback)
    (h : wideEngL lo hi lo' hi' d fe fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int lo' hi') result := by
  unfold wideEngL at h
  split at h
  · next ce te cb tb heqe heqb =>
    split at h
    · next hlen =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hne : lo' ≤ hi' := by have := fallback.lo_le; have := fallback.le_hi; omega
      have wordsX : integerWords lo hi ≤ engWords lo hi lo' hi' :=
        Nat.le_trans (integerWords_le_signedWords lo hi) (Nat.le_max_left _ _)
      have signedX : signedWords lo hi ≤ engWords lo hi lo' hi' := Nat.le_max_left _ _
      have signedB : signedWords lo' hi' ≤ engWords lo hi lo' hi' := Nat.le_max_right _ _
      have wordsB : integerWords lo' hi' ≤ engWords lo hi lo' hi' :=
        Nat.le_trans (integerWords_le_signedWords lo' hi') signedB
      have positive : 1 ≤ engWords lo hi lo' hi' := Nat.le_trans (integerWords_pos' lo hi) wordsX
      have hp' : Pre L m pc fp K d (ce ++ (wideExtendC (extSigned lo) (integerWords lo hi)
          (engWords lo hi lo' hi') d ++ (wideOutC (engWords lo hi lo' hi') d lo' hi' ++
          ([ci 19 (d + engWords lo hi lo' hi' + 3 : Nat) ((16 * (cb.length + 1) : Nat) : Int) 0] ++ cb))))
          ρ W reserved := by
        simpa only [List.append_assoc] using hp
      obtain ⟨m1, s1, a1, v1⟩ := ihe ce te heqe (by omega) m pc hp'.left
      have h1 := hp'.next a1 (Nat.le_refl d) (by omega)
      obtain ⟨m2, s2, a2, w2⟩ := wideExtend_run (extSigned lo) x.n (integerWords_pos' lo hi) wordsX
        (wideFits_zahl x) h1.frame h1.small (by omega) h1.left.code h1.left.far v1.2
      have h2 := h1.next a2 (Nat.le_refl d) (by omega)
      have fx := signedFits_zahl x signedX
      have fb' := signedFits_endpoints hne signedB
      obtain ⟨m3, s3, a3, w3, flag⟩ := wideOut_run (k := engWords lo hi lo' hi') (a := d) lo' hi' x.n
        h2.frame h2.small (by omega) positive h2.left.code h2.left.far fx.1 fx.2 fb'.1.1 fb'.1.2
        fb'.2.1 fb'.2.2 w2
      have h3 := h2.next a3 (Nat.le_refl d) (by omega)
      have brz := h3.code 0 (by simp)
      simp only [ci, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.mul_zero,
        BitVec.add_zero] at brz
      rw [← sx_nat (d := d + engWords lo hi lo' hi' + 3) (by have := hp.small; omega)] at flag
      have narrowed : lo' ≤ x.n ∧ x.n ≤ hi' → ValueAt L m3 fp d (.int lo' hi') result :=
        fun hin => valueAt_int_of_wide result wordsB (by rw [inside hin]; exact w3)
      by_cases hin : lo' ≤ x.n ∧ x.n ≤ hi'
      · have zero : Runner.IR.bool (decide (x.n < lo' ∨ hi' < x.n)) = 0 := by
          have : ¬ (x.n < lo' ∨ hi' < x.n) := by omega
          simp [Runner.IR.bool, this]
        rw [zero] at flag
        have sb := Star.one (run_step (t := ⟨_, fp⟩) brz (by decide) (run_brz_zero brz flag))
        refine ⟨m3, s1.trans (s2.trans (s3.trans (star_cast sb rfl ?_))), a1.trans (a2.trans a3), ?_⟩
        · simp only [T.mk.injEq, and_true]
          rw [sx_nat hlen, pc_add, pc_add, pc_add]
          congr 2 <;> simp only [List.length_append, List.length_singleton] <;> omega
        · exact narrowed hin
      · have one : Runner.IR.bool (decide (x.n < lo' ∨ hi' < x.n)) ≠ 0 := by
          have : (x.n < lo' ∨ hi' < x.n) := by omega
          simp [Runner.IR.bool, this]
        have sb := Star.one (run_step (t := ⟨_, fp⟩) brz (by decide) (run_brz_ne brz flag one))
        have h4 := h3.next (Agree.refl fp d K m3) (Nat.le_refl _) (by omega)
        obtain ⟨m4, s4, a4, v4⟩ := ihb cb tb heqb (by omega) m3 _ h4
        refine ⟨m4, s1.trans (s2.trans (s3.trans ((star_cast sb rfl ?_).trans (star_cast s4 rfl ?_)))),
          a1.trans (a2.trans (a3.trans a4)), ?_⟩
        · rfl
        · simp only [T.mk.injEq, and_true]
          rw [pc_add, pc_add, pc_add, pc_add]
          congr 2 <;> simp only [List.length_append, List.length_singleton] <;> omega
        · rw [outside hin]
          exact v4
    · cases h
  · cases h

end

end Gabbro.Stage0.Senke
