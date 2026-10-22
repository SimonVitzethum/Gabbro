/-
  File:      Grammatik/Adaequanz/Vollstaendig.lean
  Subject:   WHEN M AND N ARE COMPLETE: the condition on a set M of valid tests and a set N of refused tests under which
             EVERY conjunctive checker that agrees with the model on M and N agrees with it on ALL programs. It needs no
             canonical program per cell and no closure of the program class; it needs four facts:

    * `gut_m`      every program of M is valid;
    * `gut`        every cell that occurs in SOME valid program occurs in a program of M;
    * `n_schlecht` every program of N is refused;
    * `schlecht`   every refused program `p` has a test `n` in N each of whose cells occurs in `p` or in a program of M.

  So a checker that refuses `n` refuses it at a cell of `p` (a cell of a program of M it must admit). The last condition
  allows several bad cells in a test and bad cells that never come alone (masking): `n` needs no single bad cell, only
  no cell outside `p` that the tests leave free. The theorem is over an arbitrary program type, cell type and
  occurrence relation.
-/
import Grammatik.Adaequanz.Muster

namespace Gabbro.Grammatik.Adaequanz

universe u

variable {P : Type u} {Z : Type} (T : P → Z → Prop)

/-- **The test sets M (valid) and N (refused) are complete** for the table `φS` of the model. -/
structure Vollstaendig (φS : Z → Bool) (M N : List P) : Prop where
  gut_m : ∀ m ∈ M, akzeptiert T φS m
  gut : ∀ p z, T p z → akzeptiert T φS p → ∃ m ∈ M, T m z
  n_schlecht : ∀ n ∈ N, ¬ akzeptiert T φS n
  schlecht : ∀ p, ¬ akzeptiert T φS p → ∃ n ∈ N, ∀ w, T n w → T p w ∨ ∃ m ∈ M, T m w

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
    obtain ⟨n, hn, hdeck⟩ := h.schlecht p hS
    -- `n` is refused by the model, so by `φ`: some cell of `n` is refused by `φ`
    have hnφ : ¬ akzeptiert T φ n := fun ha => h.n_schlecht n hn ((hN n hn).mp ha)
    simp only [akzeptiert, not_forall] at hnφ
    obtain ⟨w, hw, hwf⟩ := hnφ
    rcases hdeck w hw with hpw | ⟨m, hm, hmw⟩
    · exact hwf (hφ w hpw)
    · exact hwf (imM m hm w hmw)
  · intro hS z hz
    obtain ⟨m, hm, hmz⟩ := h.gut p z hz hS
    exact imM m hm z hmz

/-- **Theorem 4's sufficiency from conditions (a) and (b)**: complete test sets M and N are a sufficient test set in
    the sense of `MusterHinreichend` (`Muster.lean`), with no canonical program per cell and no closure of the program
    class. (a) is `gut_m` + `gut` (the valid tests carry every cell of a valid program), (b) is `n_schlecht` +
    `schlecht` (every refused program has a refused test whose cells it has or a valid test has). -/
theorem vollstaendig_muster {φS : Z → Bool} {M N : List P} (h : Vollstaendig T φS M N) :
    MusterHinreichend T φS (M ++ N) := fun φ hMN =>
  vollstaendig_hinreichend T h φ (fun m hm => hMN m (List.mem_append_left _ hm))
    (fun n hn => hMN n (List.mem_append_right _ hn))

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
  n_schlecht := by
    intro n hn ha
    simp only [List.mem_singleton] at hn
    subst hn
    exact absurd (ha false (Or.inr ⟨rfl, rfl⟩)) (by decide)
  schlecht := by
    intro p hp
    refine ⟨false, List.mem_singleton.2 rfl, fun w hw => ?_⟩
    cases p
    · exact Or.inl hw
    · exact absurd (fun z hz => by
        rcases hz with h | ⟨h, _⟩
        · subst h; rfl
        · cases h) hp

/-- **Non-degenerate**: a checker that admits every cell agrees on `true` but not on `false`, so the theorem's agreement
    premise on M and N is what excludes it. -/
theorem zeuge_nicht_leer : ¬ (akzeptiert zeugeT (fun _ => true) false ↔ akzeptiert zeugeT zeugeS false) := by
  intro h
  have h1 : akzeptiert zeugeT (fun _ => true) false := fun _ _ => rfl
  have := (h.mp h1) false (Or.inr ⟨rfl, rfl⟩)
  exact Bool.false_ne_true this

/-- The witness of `vollstaendig_muster`: the two-program test set is sufficient in the sense of Theorem 4. -/
theorem zeuge_muster : MusterHinreichend zeugeT zeugeS ([true] ++ [false]) :=
  vollstaendig_muster zeugeT zeuge_vollstaendig

end Gabbro.Grammatik.Adaequanz
