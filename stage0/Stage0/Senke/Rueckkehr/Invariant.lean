/- Generic execution of the ordered owed-invariant checks. -/
module
public import Stage0.Senke.Rueckkehr.EpilogueCode
public import Stage0.Senke.Rueckkehr.Context
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 2000000

/-- Recording reads changes the trace, never the represented table/global values. -/
theorem owedWorld_at (P : Programm D) (f : D.Fn) (σ : World D) (m : Runner.Mem)
    (world : WeltAt m L σ) : WeltAt m L (owedWorld P f σ) := by
  unfold owedWorld
  generalize D.invs.filter (schuldet f) = carriers
  induction carriers generalizing σ with
  | nil => exact world
  | cons i rest ih => exact ih (σ.lese (invSicht D i) (P.invariante i).orte) world

/-- Every successful suffix changes only scratch slots; the first failed predicate stops at 103. -/
theorem lowInvs_ok (P : Programm D) (f : D.Fn) (σ : World D)
    {fp : Runner.W} {K d : Nat} (above : FB ≤ d) (layout : LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) :
    ∀ (is : List D.Inv) (code : List II) (top : Nat),
      lowInvs L P f d is = some (code, top) → top ≤ K →
      ∀ (m : Runner.Mem) (pc : Runner.W),
      PreS L m pc fp K d code (Env.nil : Env D []) → WeltAt m L σ →
      if (is.find? (fun i => schuldet f i && !wahr? (eval σ (P.invariante i) σ .nil))).isSome
      then Stops ⟨pc, fp⟩ m 103
      else ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
        Agree fp d K m m' := by
  intro is
  induction is with
  | nil =>
    intro code top lower fits m pc pre world
    simp only [lowInvs, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _⟩
  | cons i rest ih =>
    intro code top lower fits m pc pre world
    simp only [lowInvs] at lower
    by_cases owed : schuldet f i = true
    · rw [if_pos owed] at lower
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨⟨ci, ti⟩, hi, ⟨cr, tr⟩, hr, rfl, rfl⟩ := lower
      have tailBound := lowInvs_scratch L P f d rest cr tr hr
      have exprPre := PreS.welt pre.left (Nat.le_refl K) world layout separated
      obtain ⟨m1, run, changed, b, read, encoded⟩ :=
        lowE_ok σ σ (fun _ h => h) layout (P.invariante i) d ci ti hi
          (by omega) m pc .nil exprPre |>.word trivial
      have next := pre.next changed (Nat.le_refl _) (by omega)
      have frame1 := pre.frame.agree changed
      have far1 := codeFar_tail (a := ci) pre.far
      have guardFar := codeFar_left (by rw [← List.length_append]; exact far1)
      simp only [Enc] at encoded
      simp only [List.find?_cons, owed, Bool.true_and]
      by_cases failure : wahr? (eval σ (P.invariante i) σ .nil) = false
      · simp only [failure, Bool.not_false, ite_true, Option.isSome_some, Bool.true_eq_true]
        have zero : b = 0 := by simpa only [failure, Bool.false_eq_true, ↓reduceIte] using encoded
        exact Stops.prefix run (guard_stop (codeAt_left next.code) guardFar frame1
          (by omega) (by omega) pre.small (by decide) (by simpa only [zero] using read))
      · have success : wahr? (eval σ (P.invariante i) σ .nil) = true := by
          cases h : wahr? (eval σ (P.invariante i) σ .nil) <;> simp_all
        simp only [success, Bool.not_true, Bool.false_eq_true, ite_false]
        have one : b = 1 := by simpa only [success, ite_true] using encoded
        have guardRun := guard_pass (codeAt_left next.code) (by omega) read (by rw [one]; decide)
        have restPre : PreS L m1 _ fp K d cr (Env.nil : Env D []) :=
          ⟨next.ctx, next.small, next.frame, codeAt_right next.code,
            codeFar_tail (a := guardC d 103 d) next.far, next.env, trivial, wstab_true _ _⟩
        have result := ih cr tr hr (by omega) m1 _ restPre
          (exprPre.wstab m m1 world (changed.mono (Nat.zero_le _)))
        by_cases bad : (rest.find? (fun j => schuldet f j &&
            !wahr? (eval σ (P.invariante j) σ .nil))).isSome = true
        · rw [if_pos bad] at result ⊢
          exact Stops.prefix (run.trans guardRun) result
        · rw [if_neg bad] at result ⊢
          obtain ⟨m2, run2, changed2⟩ := result
          refine ⟨m2, ?_, changed.trans changed2⟩
          simpa only [List.append_assoc, List.length_append, pc_add, Nat.add_assoc]
            using run.trans (guardRun.trans run2)
    · have unowed : schuldet f i = false := by cases h : schuldet f i <;> simp_all
      rw [if_neg owed] at lower
      simpa only [List.find?_cons, unowed, Bool.false_and, Bool.false_eq_true, ite_false]
        using ih code top lower fits m pc pre world

end Gabbro.Stage0.Senke
