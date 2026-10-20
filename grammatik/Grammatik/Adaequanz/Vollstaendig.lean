/-
  File:      Grammatik/Adaequanz/Vollstaendig.lean
  Subject:   WHEN M AND N ARE COMPLETE (step 5 of PLAN-TEST-SET, stated and proved first): the condition on a set M of
             valid tests and a set N of refused tests under which EVERY conjunctive checker that agrees with the model
             on M and N agrees with it on ALL programs. Unlike `muster_hinlaenglich` (Muster.lean) it needs no canonical
             program per cell and no closure of the program class; it needs four facts about M and N:

    * `gut_m`    every program of M is valid;
    * `gut`      every cell that occurs in SOME valid program occurs in a program of M;
    * `schlecht` every refused program contains a bad cell that some program of N has as its ONLY bad cell;
    * `gut_in_n` every good cell of a program of N occurs in a program of M (otherwise an implementation could refuse
                 that program of N at a good cell and still agree on it).

  The four are what steps 1-4 deliver for Gabbro: `gut` and `schlecht` quantify over ALL programs, so a cell without a
  witness needs a proof that no valid program has it (for `gut`) or that every program having it also has an isolated
  bad cell (for `schlecht`). The theorem is over an arbitrary program type, cell type and occurrence relation.
-/
import Grammatik.Adaequanz.Muster

namespace Gabbro.Grammatik.Adaequanz

variable {P Z : Type} (T : P → Z → Prop)

/-- **The test sets M (valid) and N (refused) are complete** for the table `φS` of the model. -/
structure Vollstaendig (φS : Z → Bool) (M N : List P) : Prop where
  gut_m : ∀ m ∈ M, akzeptiert T φS m
  gut : ∀ p z, T p z → akzeptiert T φS p → ∃ m ∈ M, T m z
  schlecht : ∀ p, ¬ akzeptiert T φS p → ∃ z, T p z ∧ ∃ n ∈ N, NurSchlecht T φS n z
  gut_in_n : ∀ n ∈ N, ∀ w, T n w → φS w = true → ∃ m ∈ M, T m w

/-- **Theorem 5 (complete test sets suffice).** A conjunctive checker that agrees with the model on every program of M
    and of N agrees with it on every program. -/
theorem vollstaendig_hinreichend {φS : Z → Bool} {M N : List P} (h : Vollstaendig T φS M N) (φ : Z → Bool)
    (hM : ∀ m ∈ M, akzeptiert T φ m ↔ akzeptiert T φS m) (hN : ∀ n ∈ N, akzeptiert T φ n ↔ akzeptiert T φS n) :
    ∀ p, akzeptiert T φ p ↔ akzeptiert T φS p := by
  classical
  -- every cell of a program of M is admitted by `φ`
  have imM : ∀ m ∈ M, ∀ w, T m w → φ w = true := fun m hm w hw => (hM m hm).mpr (h.gut_m m hm) w hw
  intro p
  constructor
  · intro hφ
    by_contra hS
    obtain ⟨z, hz, n, hn, hns⟩ := h.schlecht p hS
    -- `n` is refused by the model, so by `φ`: some cell of `n` is refused by `φ`
    have hnS : ¬ akzeptiert T φS n := fun ha => by
      have := ha z hns.1
      rw [hns.2.1] at this
      exact Bool.false_ne_true this
    have hnφ : ¬ akzeptiert T φ n := fun ha => hnS ((hN n hn).mp ha)
    simp only [akzeptiert, not_forall] at hnφ
    obtain ⟨w, hw, hwf⟩ := hnφ
    by_cases hwz : w = z
    · subst hwz
      exact hwf (hφ w hz)
    · -- `w` is a good cell of `n`, so it occurs in M and `φ` admits it
      obtain ⟨m, hm, hmw⟩ := h.gut_in_n n hn w hw (hns.2.2 w hw hwz)
      exact hwf (imM m hm w hmw)
  · intro hS z hz
    obtain ⟨m, hm, hmz⟩ := h.gut p z hz hS
    exact imM m hm z hmz

/-! ## A witness: the condition is satisfiable and the theorem is not vacuous -/

/-- Two programs over two cells: `gut` has only the good cell `true`; `boese` has the bad cell `false`. -/
def zeugeT : Bool → Bool → Prop := fun p z => z = true ∨ (p = false ∧ z = false)

/-- The model admits the cell `true` and refuses the cell `false`. -/
def zeugeS : Bool → Bool := id

theorem zeuge_vollstaendig : Vollstaendig zeugeT zeugeS [true] [false] where
  gut_m := by
    intro m hm z hz
    simp only [List.mem_singleton] at hm
    subst hm
    rcases hz with h | ⟨h, _⟩
    · subst h; rfl
    · cases h
  gut := by
    intro p z hz hacc
    refine ⟨true, List.mem_singleton.2 rfl, ?_⟩
    rcases hz with h | ⟨hp, h⟩
    · exact Or.inl h
    · -- the cell `false` occurs only in `false`, which the model refuses
      have := hacc z (Or.inr ⟨hp, h⟩)
      subst h
      exact absurd this (by decide)
  schlecht := by
    intro p hp
    refine ⟨false, ?_, false, List.mem_singleton.2 rfl, ?_⟩
    · cases p
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd (fun z hz => by
          rcases hz with h | ⟨h, _⟩
          · subst h; rfl
          · cases h) hp
    · refine ⟨Or.inr ⟨rfl, rfl⟩, rfl, fun z hz hne => ?_⟩
      rcases hz with h | ⟨_, h⟩
      · subst h; rfl
      · exact absurd h hne
  gut_in_n := by
    intro n _ w _ hw
    exact ⟨true, List.mem_singleton.2 rfl, Or.inl (by cases w <;> simp_all [zeugeS])⟩

/-- **Non-degenerate**: a checker that admits every cell agrees on `true` but not on `false`, so the theorem's agreement
    premise on M and N is what excludes it. -/
theorem zeuge_nicht_leer : ¬ (akzeptiert zeugeT (fun _ => true) false ↔ akzeptiert zeugeT zeugeS false) := by
  intro h
  have h1 : akzeptiert zeugeT (fun _ => true) false := fun _ _ => rfl
  have := (h.mp h1) false (Or.inr ⟨rfl, rfl⟩)
  exact Bool.false_ne_true this

end Gabbro.Grammatik.Adaequanz
