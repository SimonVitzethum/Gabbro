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
import Grammatik.ReferenzB

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

/-! ## 4. Structural special case: distinct threads run distinct functions.

  The marks named in a body are the flattened atoms' marks
  (`endblockAtome` is what `progAus` flattens per thread).

  On the task sketch: its two premises (distinct functions with nonzero
  mark codes) do NOT suffice -- two distinct function bodies may name
  the SAME mark (hence the same code), exactly as two same-function
  threads do (`pcMarkSep_scheitert_gleich_fn` in MarkenInstanzA.lean).
  `pcMarkSep_scheitert_geteilte_marke` below mechanizes that gap for an
  arbitrary program text. The repaired theorem therefore carries the
  load-bearing premise `hDisj`: distinct function bodies name marks with
  distinct codes. The nonzero-code premise of the sketch is load-free
  for `PCMarkSep` (zero collides like any code) and is not carried. -/

/-- The marks named anywhere in a function body: the flattened atoms'
    marks, the same traversal `progAus` uses per thread. -/
def koerperMarken (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V false Γ Λ) : List D.Marke :=
  (endblockAtome tabs globs b).flatMap PCAtom.marks

/-- A mark in a thread's extracted text sits in its function's body
    marks: `progAus` unfolds to the body's atoms. -/
theorem marke_aus_progAus_in_koerper (P : Programm D)
    (fcode : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (f : Faden) (m : D.Marke)
    (hm : m ∈ (progAus P fcode tabs globs).marks f) :
    m ∈ koerperMarken tabs globs (P.rumpf (fcode f)) := by
  show m ∈ (endblockAtome tabs globs (P.rumpf (fcode f))).flatMap PCAtom.marks
  exact hm

/-- Structural mark separation: distinct threads run distinct functions
    whose bodies name marks with pairwise distinct codes. Every premise
    fires: `hFn` separates the functions, `hDisj` the codes. -/
theorem pcMarkSep_aus_verschiedenen_funktionen (P : Programm D)
    (fcode : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (code : D.Marke → Nat)
    (hFn : ∀ g₁ g₂, g₁ ≠ g₂ → fcode g₁ ≠ fcode g₂)
    (hDisj : ∀ (f₁ f₂ : D.Fn), f₁ ≠ f₂ →
      ∀ m₁ ∈ koerperMarken tabs globs (P.rumpf f₁),
      ∀ m₂ ∈ koerperMarken tabs globs (P.rumpf f₂),
        code m₁ ≠ code m₂) :
    PCMarkSep code (progAus P fcode tabs globs) := by
  intro f g hfg c hcf hcg
  obtain ⟨m₁, hm₁, hc₁⟩ := List.mem_map.mp hcf
  obtain ⟨m₂, hm₂, hc₂⟩ := List.mem_map.mp hcg
  exact absurd (hc₁.trans hc₂.symm)
    (hDisj _ _ (hFn f g hfg) _ (marke_aus_progAus_in_koerper P fcode tabs globs f m₁ hm₁)
      _ (marke_aus_progAus_in_koerper P fcode tabs globs g m₂ hm₂))

/-- Why the two sketch premises do not suffice, over an arbitrary text:
    one mark named by two threads' texts already breaks `PCMarkSep`,
    whatever the functions and codes are. Every premise fires: `hmf` and
    `hmg` name the shared code on both sides. -/
theorem pcMarkSep_scheitert_geteilte_marke (code : D.Marke → Nat)
    (prog : PCProg D) (f g : Faden) (hfg : f ≠ g)
    (m : D.Marke)
    (hmf : m ∈ prog.marks f) (hmg : m ∈ prog.marks g) :
    ¬ PCMarkSep code prog := by
  intro hSep
  exact (hSep f g hfg (code m)
    (List.mem_map.mpr ⟨m, hmf, rfl⟩))
    (List.mem_map.mpr ⟨m, hmg, rfl⟩)

/-! ## 5. Witnesses on the reference program `refB_prog`.

  Both_soundness theorems take general `prog`; the companions below
  instantiate ALL premises JOINTLY on `refB_prog` (thread 1 takes the
  lock, then fires the writing leaf; thread 0 rests). The Bools evaluate
  by `decide`. Non-degeneracy rides along: `einzahlen` writes `konto`
  (`refEin_schreibt`) and the reached PC run moves memory
  (`refB_pc_erreicht`, `refB_pc_schreibt`). -/

/-- Coverage for the witness: every thread outside `[0, 1]` has empty
    text in `refB_prog`. Proved from the program definition. -/
theorem refB_prog_abdeckung : ∀ h, h ∉ [0, 1] → refB_prog h = [] := by
  intro h hh
  -- `h1` discharges the wildcard equation's side condition; the linter
  -- reports it unused, but dropping it leaves the match unsolved.
  have h1 : h ≠ 1 := by
    intro e
    subst e
    simp at hh
  simp [refB_prog, h1]

/-- Joint witness for `markSep_aus_B`: decided check, coverage, a table
    the function writes, and a reached run that changes memory. -/
theorem markSep_aus_B_zeuge :
    ∃ (code : refD.Marke → Nat) (fs : List Faden),
      markSepB code refB_prog fs = true ∧
      (∀ h, h ∉ fs → refB_prog h = []) ∧
      (vertragVon refD refEin).schreibt () = true ∧
      ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hB : markSepB (fun _ => 0) refB_prog [0, 1] = true := by decide
  exact ⟨fun _ => 0, [0, 1], hB, refB_prog_abdeckung,
    refEin_schreibt (), refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-- Joint witness for `nurG_aus_B`: thread 1 owns `konto`, thread 0
    names nothing; decided check, coverage, written table, moving run. -/
theorem nurG_aus_B_zeuge :
    ∃ (t : refD.Tab) (g : Faden) (fs : List Faden),
      nurGB t g refB_prog fs = true ∧
      (∀ h, h ∉ fs → refB_prog h = []) ∧
      (vertragVon refD refEin).schreibt () = true ∧
      ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hB : nurGB () 1 refB_prog [0, 1] = true := by decide
  exact ⟨(), 1, [0, 1], hB, refB_prog_abdeckung,
    refEin_schreibt (), refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-- The unshared check agrees on the witness program (shared `konto`,
    silent thread 0): corroboration, no witness obligation. -/
example : unsharedSepB refB_prog [0, 1] = true := by decide

/-! ## CUTS: what is not proved.

  * The decided checks range over an explicit thread list `fs` with the
    coverage side-condition `hcov`; the checker discharges `hcov` by
    construction (it spawns exactly `fs`). No theorem here ties `fs` to
    a checker thread table.
  * `pcMarkSep_aus_verschiedenen_funktionen` carries the cross-function
    code-disjointness premise `hDisj`: the task's two premises (distinct
    functions, nonzero codes) do not suffice, mechanized as
    `pcMarkSep_scheitert_geteilte_marke`. Same-function threads stay
    excluded (B8); per-thread instances are groundwork in
    MarkenInstanzA.lean, not a discharge here.
  * No `PCSchritt` firing is built here: separation is program text;
    the run discharge is `pc_discharge_einfaedig` / `pc_discharge_unshared`
    (Maschine.lean). The witnesses reuse the reached `refB_prog` run
    (`refB_pc_erreicht`) for non-degeneracy only.
  * `refB_prog` names no marks (`refD.Marke` is empty), so both witnesses
    discharge vacuously on the mark side; the carrier side (`konto`,
    shared) fires for real.
-/

#print axioms Gabbro.Grammatik.markSep_aus_B
#print axioms Gabbro.Grammatik.unsharedSep_aus_B
#print axioms Gabbro.Grammatik.nurG_aus_B
#print axioms Gabbro.Grammatik.markSep_aus_B_progAus
#print axioms Gabbro.Grammatik.unsharedSep_aus_B_progAus
#print axioms Gabbro.Grammatik.nurG_aus_B_progAus
#print axioms Gabbro.Grammatik.marke_aus_progAus_in_koerper
#print axioms Gabbro.Grammatik.pcMarkSep_aus_verschiedenen_funktionen
#print axioms Gabbro.Grammatik.pcMarkSep_scheitert_geteilte_marke
#print axioms Gabbro.Grammatik.refB_prog_abdeckung
#print axioms Gabbro.Grammatik.markSep_aus_B_zeuge
#print axioms Gabbro.Grammatik.nurG_aus_B_zeuge

end Gabbro.Grammatik
