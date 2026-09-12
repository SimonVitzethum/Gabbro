/-
  File:      Grammatik/Trennung.lean
  Subject:   THREAD-SEPARATION FACTS BY COMPUTATION (lane 100, D2).

  `PCMarkSep` / `PCUnsharedSep` (Maschine.lean) and the `hNurG` shape of
  `eigenzustand_nur_eigene_schritteD_rep` (EigenZustandD.lean) are facts
  about PROGRAM TEXTS, so the checker can decide them. This file provides
  the decision functions (`markSepB`, `unsharedSepB`, `nurGB`) computed
  over atom lists, with soundness theorems into the three predicates.

  Thread enumeration: `Faden` is `Nat` (Marken.lean), hence infinite. A
  decidable check ranges over an explicit thread list `fs` (the threads
  the checker spawns -- DATA, not a proposition); soundness carries the
  coverage side-condition `hcov : forall h, h notin fs -> prog h = []`.
  On the witness it is proved from the program definition, not assumed.
-/
import Grammatik.Maschine
import Grammatik.Extraktion

namespace Gabbro.Grammatik

open Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- Mark separation, decided: no code named by one listed thread's text
    is named by another's. Diagonal pairs pass silently. -/
def markSepB (code : D.Marke → Nat) (prog : PCProg D)
    (fs : List Faden) : Bool :=
  fs.all fun f => fs.all fun g =>
    (decide (f = g) ||
      ((prog.marks f).map code).all fun c =>
        !decide (c ∈ (prog.marks g).map code))

/-- Carrier separation for unshared carriers, decided: a carrier reached
    from two listed threads' texts is declared shared. Membership runs
    through `any` (`DecidableEq` holds; `BEq` does not). -/
def unsharedSepB (prog : PCProg D) (fs : List Faden) : Bool :=
  fs.all fun f => fs.all fun g =>
    (decide (f = g) ||
      (prog.carriers f).all fun o =>
        (!((prog.carriers g).any fun o' => decide (o = o')) ||
          match o with
          | .inl t => D.geteilt t
          | .inr x => D.ggeteilt x))

/-- Own-state text fact, decided: no listed thread other than `g` names
    the table carrier `t` in any atom. -/
def nurGB (t : D.Tab) (g : Faden) (prog : PCProg D)
    (fs : List Faden) : Bool :=
  fs.all fun h =>
    (decide (h = g) || (prog h).all fun a =>
      !((PCAtom.carriers a).any fun o => decide (o = Sum.inl t)))

/-! ## 2. Soundness: decided checks imply the separation predicates.

  `fs` is the checker's thread list (DATA); `hcov` ties it to the
  program (every thread outside `fs` has empty text). Both fire in the
  proof: `hB` on listed pairs, `hcov` on unlisted threads. -/

/-- Decided mark separation is sound: every named code sits in one
    listed thread's text only (unlisted threads name nothing). -/
theorem markSep_aus_B (code : D.Marke → Nat) (prog : PCProg D)
    (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → prog h = [])
    (hB : markSepB code prog fs = true) :
    PCMarkSep code prog := by
  intro f g hfg c hcf hcg
  have hall : ∀ f ∈ fs, ∀ g ∈ fs,
      (decide (f = g) ||
        ((prog.marks f).map code).all fun c =>
          !decide (c ∈ (prog.marks g).map code)) = true := by
    intro f hf g hg
    have h1 := (List.all_eq_true.mp (by unfold markSepB at hB; exact hB)) f hf
    exact (List.all_eq_true.mp h1) g hg
  by_cases hf : f ∈ fs <;> by_cases hg : g ∈ fs
  · have hcond := hall f hf g hg
    rw [decide_eq_false hfg] at hcond
    simp only [Bool.false_or] at hcond
    have hmem := (List.all_eq_true.mp hcond) c hcf
    exact absurd hcg (by simpa using hmem)
  · have e := hcov g hg
    unfold PCProg.marks at hcg
    rw [e] at hcg
    simp at hcg
  · have e := hcov f hf
    unfold PCProg.marks at hcf
    rw [e] at hcf
    simp at hcf
  · have e := hcov f hf
    unfold PCProg.marks at hcf
    rw [e] at hcf
    simp at hcf

/-- Decided carrier separation is sound: a carrier reached from two
    threads' texts is declared shared (unlisted threads reach nothing). -/
theorem unsharedSep_aus_B (prog : PCProg D) (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → prog h = [])
    (hB : unsharedSepB prog fs = true) :
    PCUnsharedSep prog := by
  intro f g hfg o hof hog
  have hall : ∀ f ∈ fs, ∀ g ∈ fs,
      (decide (f = g) ||
        (prog.carriers f).all fun o =>
          (!((prog.carriers g).any fun o' => decide (o = o')) ||
            match o with
            | .inl t => D.geteilt t
            | .inr x => D.ggeteilt x)) = true := by
    intro f hf g hg
    have h1 := (List.all_eq_true.mp (by unfold unsharedSepB at hB; exact hB)) f hf
    exact (List.all_eq_true.mp h1) g hg
  by_cases hf : f ∈ fs <;> by_cases hg : g ∈ fs
  · have hcond := hall f hf g hg
    rw [decide_eq_false hfg] at hcond
    simp only [Bool.false_or] at hcond
    have hmem := (List.all_eq_true.mp hcond) o hof
    have hany : ((prog.carriers g).any fun o' => decide (o = o')) = true := by
      rw [List.any_eq_true]
      exact ⟨o, hog, by simp⟩
    rw [hany] at hmem
    simp only [Bool.not_true, Bool.false_or] at hmem
    cases o with
    | inl t =>
      dsimp only at hmem ⊢
      intro hcon
      rw [hmem] at hcon
      exact Bool.noConfusion hcon
    | inr x =>
      dsimp only at hmem ⊢
      intro hcon
      rw [hmem] at hcon
      exact Bool.noConfusion hcon
  · have e := hcov g hg
    unfold PCProg.carriers at hog
    rw [e] at hog
    simp at hog
  · have e := hcov f hf
    unfold PCProg.carriers at hof
    rw [e] at hof
    simp at hof
  · have e := hcov f hf
    unfold PCProg.carriers at hof
    rw [e] at hof
    simp at hof

/-- The decided own-state fact is sound: no thread other than `g` names
    the table carrier in any atom (unlisted threads name nothing). This
    is the `hNurG` shape of `eigenzustand_nur_eigene_schritteD_rep`. -/
theorem nurG_aus_B (t : D.Tab) (g : Faden) (prog : PCProg D)
    (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → prog h = [])
    (hB : nurGB t g prog fs = true) :
    ∀ h, h ≠ g → ∀ a ∈ prog h, (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a := by
  intro h hne a ha
  have hall : ∀ h ∈ fs,
      (decide (h = g) || (prog h).all fun a =>
        !((PCAtom.carriers a).any fun o => decide (o = Sum.inl t))) = true := by
    intro h hh
    exact (List.all_eq_true.mp (by unfold nurGB at hB; exact hB)) h hh
  by_cases hh : h ∈ fs
  · have hcond := hall h hh
    rw [decide_eq_false hne] at hcond
    simp only [Bool.false_or] at hcond
    have hmem := (List.all_eq_true.mp hcond) a ha
    intro hcon
    have hany : ((PCAtom.carriers a).any fun o => decide (o = Sum.inl t)) = true := by
      rw [List.any_eq_true]
      exact ⟨Sum.inl t, hcon, by simp⟩
    rw [hany] at hmem
    simp at hmem
  · have e := hcov h hh
    rw [e] at ha
    simp at ha

/-! ## 3. Instances over the extracted thread program.

  The task shape: conclusions over
  `Extraktion.progAus P fcode tabs globs`. Each is the general
  soundness theorem instantiated; every premise is passed through. -/

/-- Decided mark separation over the extracted program implies
    `PCMarkSep`: the `hMSep` premise of the goal family, by computation. -/
theorem markSep_aus_B_progAus (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (code : D.Marke → Nat) (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → progAus P fcode tabs globs h = [])
    (hB : markSepB code (progAus P fcode tabs globs) fs = true) :
    PCMarkSep code (progAus P fcode tabs globs) :=
  markSep_aus_B code _ fs hcov hB

/-- Decided carrier separation over the extracted program implies
    `PCUnsharedSep`: the `hCSep` premise of the goal family. -/
theorem unsharedSep_aus_B_progAus (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → progAus P fcode tabs globs h = [])
    (hB : unsharedSepB (progAus P fcode tabs globs) fs = true) :
    PCUnsharedSep (progAus P fcode tabs globs) :=
  unsharedSep_aus_B _ fs hcov hB

/-- The decided own-state fact over the extracted program implies the
    `hNurG` shape of the own-state theorem. -/
theorem nurG_aus_B_progAus (P : Programm D) (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (t : D.Tab) (g : Faden) (fs : List Faden)
    (hcov : ∀ h, h ∉ fs → progAus P fcode tabs globs h = [])
    (hB : nurGB t g (progAus P fcode tabs globs) fs = true) :
    ∀ h, h ≠ g → ∀ a ∈ progAus P fcode tabs globs h,
      (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a :=
  nurG_aus_B t g _ fs hcov hB

end Gabbro.Grammatik
