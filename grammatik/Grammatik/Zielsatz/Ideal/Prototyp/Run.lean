/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Run.lean
  Subject:   PROTOTYPE of S7: THE THEOREM -- every implementation run of a race-free, lock-disciplined fragment
             program has a corresponding run of `I` (`dokumente/PERFECT-MODEL.md` §2, §3.6), for finite runs and
             as ONE ideal run per infinite run, with the same answers per context and bounded stutter.

  Answers are compared PER CONTEXT: the ideal run receives a unit's answers when it commits the unit, so the
  global interleaving of answers of different contexts differs, while each context's sequence is the same up to
  the answers of its still running unit (`pa`); between units they are equal (`pa_ruhig`).
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Step

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The answers context `c` received in an implementation trace. -/
def antS (c : Ctx) (tr : List (Ctx × Option Int)) : List Int :=
  tr.flatMap fun p => if p.1 = c then p.2.toList else []

/-- The answers context `c` received in an ideal trace. -/
def antI (c : Ctx) (tr : List (Ctx × List Int)) : List Int :=
  tr.flatMap fun p => if p.1 = c then p.2 else []

/-- **Finite runs.** Every finite implementation run from the start has an ideal run from the start that ends in
    relation with it, and every context received the same answers, up to the pending answers of its running
    unit. -/
theorem sim_star {P : Prog} (hD : Disc P) {tr : List (Ctx × Option Int)} {s : S}
    (h : SStar P (S.init P) tr s) :
    ∃ itr i pa, IStar P (IS.init P) itr i ∧ R P s i pa ∧ ∀ c, antS c tr = antI c itr ++ pa c := by
  induction h with
  | refl => exact ⟨[], IS.init P, fun _ => [], IStar.refl _, r_init P hD, fun _ => rfl⟩
  | @tail s₁ s₂ tr c a _ hs ih =>
      obtain ⟨itr, i, pa, hI, hR, hA⟩ := ih
      obtain ⟨⟨i', pa'⟩, hF, hR'⟩ := sim_step (x := (i, pa)) hD hR hs
      rcases hF with ⟨_, he, hpa⟩ | ⟨_, _, w, hst, hpa⟩
      · simp only at he hpa
        subst he hpa
        refine ⟨itr, _, _, hI, hR', fun c' => ?_⟩
        simp only [antS, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        by_cases hc : c' = c
        · subst hc; simp only [ite_true, upd_same]; rw [← List.append_assoc, ← antS, hA]
        · simp only [ite_eq_right (Ne.symm hc), upd_ne _ _ hc, List.append_nil]
          exact hA c'
      · simp only at hst hpa
        subst hpa
        refine ⟨itr ++ [(c, pa c ++ a.toList)], i', _, IStar.tail hI hst, hR', fun c' => ?_⟩
        simp only [antS, antI, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        by_cases hc : c' = c
        · subst hc; simp only [ite_true, upd_same, List.append_nil]
          rw [← List.append_assoc, ← antS, hA, ← antI, List.append_assoc]
        · rw [ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc), upd_ne _ _ hc, List.append_nil, List.append_nil]
          exact hA c'

/-- Between units nothing is pending: a context outside its unit has received exactly the same answers. -/
theorem pa_ruhig {P : Prog} {s : S} {i : IS} {pa : Ctx → List Int} (hR : R P s i pa) {c : Ctx}
    (hc : Rest s c = 0) : pa c = [] := by
  cases c with
  | thr t =>
      have ht := hR.thr t
      unfold ThR at ht
      unfold Rest at hc
      cases hcur : (s.th t).cur with
      | none => simp only [hcur] at ht; exact ht.2
      | some cu => cases cu <;> simp [hcur] at hc
  | irq =>
      have hh := hR.hd
      unfold HdR at hh
      unfold Rest at hc
      cases hhd : s.hd with
      | none => simp only [hhd] at hh; exact hh
      | some x => obtain ⟨r, ρ⟩ := x; simp [hhd] at hc
  | dma => exact hR.dma

/-! ## Infinite runs: ONE ideal run per run -/

/-- An infinite implementation run: states, the context and the answer of each step. -/
structure Lauf (P : Prog) where
  st : Nat → S
  ctx : Nat → Ctx
  ans : Nat → Option Int
  start : st 0 = S.init P
  step : ∀ n, SStep P (st n) (ctx n) (ans n) (st (n + 1))

open Classical in
/-- The ideal run of an implementation run, built step by step along the run (never per prefix): the pair of the
    ideal state and the pending answers. -/
noncomputable def ideal {P : Prog} (hD : Disc P) (L : Lauf P) : Nat → IS × (Ctx → List Int)
  | 0 => (IS.init P, fun _ => [])
  | n + 1 =>
      if h : R P (L.st n) (ideal hD L n).1 (ideal hD L n).2 then
        Classical.choose (sim_step (x := ideal hD L n) hD h (L.step n))
      else ideal hD L n

theorem ideal_r {P : Prog} (hD : Disc P) (L : Lauf P) :
    ∀ n, R P (L.st n) (ideal hD L n).1 (ideal hD L n).2
  | 0 => by rw [L.start]; exact r_init P hD
  | n + 1 => by
      have h := ideal_r hD L n
      simp only [ideal, dite_eq_left h]
      exact (Classical.choose_spec (sim_step (x := ideal hD L n) hD h (L.step n))).2

theorem ideal_folgt {P : Prog} (hD : Disc P) (L : Lauf P) (n : Nat) :
    Folgt P (L.st (n + 1)) (L.ctx n) (L.ans n) (ideal hD L n) (ideal hD L (n + 1)) := by
  have h := ideal_r hD L n
  simp only [ideal, dite_eq_left h]
  exact (Classical.choose_spec (sim_step (x := ideal hD L n) hD h (L.step n))).1

/-- The answers of context `c` in the first `n` steps of the implementation run. -/
def Lauf.antS {P : Prog} (L : Lauf P) (c : Ctx) : Nat → List Int
  | 0 => []
  | n + 1 => L.antS c n ++ if L.ctx n = c then (L.ans n).toList else []

/-- The answers of context `c` in the ideal steps taken during the first `n` implementation steps. -/
noncomputable def antIdeal {P : Prog} (hD : Disc P) (L : Lauf P) (c : Ctx) : Nat → List Int
  | 0 => []
  | n + 1 => antIdeal hD L c n ++
      if L.ctx n = c ∧ Rest (L.st (n + 1)) (L.ctx n) = 0 ∧ L.ctx n ≠ .dma then
        (ideal hD L n).2 c ++ (L.ans n).toList else []

/-- Per context, the ideal run received the implementation's answers, up to the pending ones. -/
theorem ideal_ant {P : Prog} (hD : Disc P) (L : Lauf P) (c : Ctx) :
    ∀ n, L.antS c n = antIdeal hD L c n ++ (ideal hD L n).2 c
  | 0 => rfl
  | n + 1 => by
      have ih := ideal_ant hD L c n
      have hF := ideal_folgt hD L n
      simp only [Lauf.antS, antIdeal]
      rcases hF with ⟨hst, _, hpa⟩ | ⟨hd, h0, _, _, hpa⟩
      · rw [hpa]
        have hno : ¬ (L.ctx n = c ∧ Rest (L.st (n + 1)) (L.ctx n) = 0 ∧ L.ctx n ≠ .dma) := fun ⟨_, h0, hd⟩ =>
          hst.elim (fun h => hd h) (fun h => h h0)
        rw [ite_eq_right hno, List.append_nil, ih]
        by_cases hc : L.ctx n = c
        · rw [ite_eq_left hc]; subst hc; rw [upd_same, List.append_assoc]
        · rw [ite_eq_right hc, upd_ne _ _ (Ne.symm hc), List.append_nil]
      · rw [hpa, ih]
        by_cases hc : L.ctx n = c
        · rw [ite_eq_left hc, ite_eq_left ⟨hc, h0, hd⟩]; subst hc; rw [upd_same, List.append_nil, List.append_assoc]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.1), upd_ne _ _ (Ne.symm hc), List.append_nil, List.append_nil]

/-- **Bounded stutter.** In any stretch of the run in which context `c` (a thread or the handler) takes no ideal
    step, it takes at most `maxLen P + 1` implementation steps. -/
theorem ideal_stotter {P : Prog} (hD : Disc P) (L : Lauf P) (c : Ctx) (hd : c ≠ .dma) (n : Nat) :
    ∀ m, (∀ j, j < m → L.ctx (n + j) = c → Rest (L.st (n + j + 1)) c ≠ 0) →
      ((List.range m).filter fun j => decide (L.ctx (n + j) = c)).length + psi P (L.st (n + m)) c ≤
        psi P (L.st n) c
  | 0, _ => by simp
  | m + 1, hno => by
      have ih := ideal_stotter hD L c hd n m (fun j hj => hno j (Nat.lt_succ_of_lt hj))
      rw [List.range_succ, List.filter_append, List.length_append]
      have hs := L.step (n + m)
      by_cases hc : L.ctx (n + m) = c
      · have hlt := psi_lt (hc ▸ hs) (ideal_r hD L (n + m + 1)) hd (hno m (Nat.lt_succ_self m) hc)
        simp only [List.filter_cons, List.filter_nil, hc, decide_true, ite_true, List.length_cons,
          List.length_nil]
        rw [show n + (m + 1) = n + m + 1 by omega]
        omega
      · have heq : Rest (L.st (n + m + 1)) c = Rest (L.st (n + m)) c := rest_other hs (Ne.symm hc)
        simp only [List.filter_cons, List.filter_nil, hc, decide_false]
        rw [show n + (m + 1) = n + m + 1 by omega]
        unfold psi at ih ⊢
        rw [heq]
        simpa using ih

theorem ideal_stotter_schranke {P : Prog} (hD : Disc P) (L : Lauf P) (c : Ctx) (hd : c ≠ .dma) (n m : Nat)
    (hno : ∀ j, j < m → L.ctx (n + j) = c → Rest (L.st (n + j + 1)) c ≠ 0) :
    ((List.range m).filter fun j => decide (L.ctx (n + j) = c)).length ≤ maxLen P + 1 := by
  have h := ideal_stotter hD L c hd n m hno
  have h1 := psi_le (ideal_r hD L n) c
  have h2 := psi_pos P (L.st (n + m)) c
  omega

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
