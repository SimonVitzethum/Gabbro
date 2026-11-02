/- C16: admission of declared checks -- the decider, the Prop and the site duty.

   `checkOkB` decides one check: the probe answers `Bool` on a reason-free channel,
   threads exactly the Duty, is read-only over the declared carriers, every gate
   consumes the Duty, the gates are pairwise distinct, the probe is none of its
   gates, and every other function the probe may call is read-only and forges no
   Duty. `checkB` lifts this over the unit with pairwise-distinct check names.
   `CheckAdmission` is the same as a Prop, with the call-graph closure
   (`CheckRahmen`, through `reachB`) beside the exact expansion. `checkB_iff`
   ties them: the Bool decides exactly the Prop, given complete member lists.

   `CheckSitePflicht` is the site duty of one declared check: the probe and every
   declared gate meet their body duties, tied to the same Duty by the expansion.
   `checkSitePflicht_aus` derives it from the admission and the user's logic.

   Folding the admission into `AkzeptiertSpec`/`AkzeptiertSpecX` and the goal chain
   is the lead's build step: every `AkzeptiertSpec` construction site moves together. -/
module

public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil2
public import Grammatik.Kern.Syntax.Satz.Pruefung

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Pruefung

variable [DecidableEq D.Fn]

/-- Gate names are pairwise distinct: one Duty is never duplicated across them. -/
def toreEindeutig : List D.Fn → Bool
  | [] => true
  | g :: rest => decide (∀ x ∈ rest, x ≠ g) && toreEindeutig rest

/-- Gate-name distinctness as a Prop. -/
theorem toreEindeutig_iff {gs : List D.Fn} :
    toreEindeutig gs = true ↔ gs.Nodup := by
  induction gs with
  | nil => simp [toreEindeutig]
  | cons g rest ih =>
    have hmem : (∀ x ∈ rest, x ≠ g) ↔ g ∉ rest := by
      constructor
      · intro h hm
        exact h g hm rfl
      · intro h x hx heq
        subst heq
        exact h hx
    simp only [toreEindeutig, List.nodup_cons, Bool.and_eq_true, decide_eq_true_eq]
    rw [ih]
    exact and_congr hmem Iff.rfl

/-- Every other function the probe may call is read-only and forges no Duty. -/
def rahmenOkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (c : CheckDecl D) : Bool :=
  fns.all fun f => !(reachB P fns c.probe f) || decide (f = c.probe) ||
    (tabs.all (fun t => !((D.signatur f).schreibt t)) &&
     globs.all (fun g => !((D.signatur f).gschreibt g)) &&
     decide (c.duty ∉ (D.signatur f).produziert))

/-- One check, decided. -/
def checkOkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (c : CheckDecl D) : Bool :=
  decide (D.erg c.probe = some .bool) &&
  decide ((D.signatur c.probe).gruende = 0) &&
  decide ((D.signatur c.probe).konsumiert = [c.duty]) &&
  decide ((D.signatur c.probe).produziert = [c.duty]) &&
  tabs.all (fun t => !((D.signatur c.probe).schreibt t)) &&
  globs.all (fun g => !((D.signatur c.probe).gschreibt g)) &&
  c.gates.all (fun g => decide (c.duty ∈ (D.signatur g).konsumiert) && decide (g ∈ fns)) &&
  toreEindeutig c.gates &&
  decide (c.probe ∉ c.gates) &&
  decide (c.probe ∈ fns) &&
  rahmenOkB P tabs globs fns c

/-- Check names are pairwise distinct. -/
def eindeutigeNamen : List (CheckDecl D) → Bool
  | [] => true
  | c :: rest => decide (∀ d ∈ rest, d.name ≠ c.name) && eindeutigeNamen rest

/-- The checks of a unit, decided. -/
def checkB (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob) (fns : List D.Fn)
    (checks : List (CheckDecl D)) : Bool :=
  checks.all (checkOkB P tabs globs fns) && eindeutigeNamen checks

/-- The call-graph closure of one check: whatever the probe may call (other than
    itself) is read-only and produces no Duty. -/
def CheckRahmen (P : Programm D) (fs : List D.Fn) (c : CheckDecl D) : Prop :=
  ∀ f, reachB P fs c.probe f = true → f ≠ c.probe →
    (∀ t, (D.signatur f).schreibt t = false) ∧
    (∀ g, (D.signatur f).gschreibt g = false) ∧
    c.duty ∉ (D.signatur f).produziert

/-- The admission of declared checks: every check expands exactly, its call graph
    keeps the frame, probe and gates are functions of the unit, and no two checks
    share a name. -/
def CheckAdmission (P : Programm D) (fs : List D.Fn) (checks : List (CheckDecl D)) : Prop :=
  (∀ c ∈ checks, CheckExpansion P c) ∧
  (∀ c ∈ checks, CheckRahmen P fs c) ∧
  (∀ c ∈ checks, c.probe ∈ fs) ∧
  (∀ c ∈ checks, ∀ g ∈ c.gates, g ∈ fs) ∧
  List.Nodup (checks.map CheckDecl.name)

/-- Distinct names as a Prop: no two checks share a name. -/
theorem eindeutig_iff {checks : List (CheckDecl D)} :
    eindeutigeNamen checks = true ↔ List.Nodup (checks.map CheckDecl.name) := by
  induction checks with
  | nil => simp [eindeutigeNamen]
  | cons c rest ih =>
    have hmem : (∀ d ∈ rest, d.name ≠ c.name) ↔ c.name ∉ List.map CheckDecl.name rest := by
      constructor
      · intro h hmem
        obtain ⟨d, hd, heq⟩ := List.mem_map.mp hmem
        exact h d hd heq
      · intro h d hd heq
        exact h (List.mem_map.mpr ⟨d, hd, heq⟩)
    simp only [eindeutigeNamen, List.map_cons, List.nodup_cons, Bool.and_eq_true,
      decide_eq_true_eq]
    rw [ih]
    exact and_congr hmem Iff.rfl

/-- One check: the Bool decides exactly the Prop. -/
theorem checkOkB_iff {P : Programm D} {tabs : List D.Tab} {globs : List D.Glob}
    {fns : List D.Fn} {c : CheckDecl D}
    (hvoll : ∀ g : D.Fn, g ∈ fns) (htabs : ∀ t : D.Tab, t ∈ tabs)
    (hglobs : ∀ g : D.Glob, g ∈ globs) :
    checkOkB P tabs globs fns c = true ↔
      (CheckExpansion P c ∧ CheckRahmen P fns c ∧ c.probe ∈ fns ∧
        ∀ g ∈ c.gates, g ∈ fns) := by
  constructor
  · intro h
    simp only [checkOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    have hnd : c.gates.Nodup := toreEindeutig_iff.mp h8
    refine ⟨⟨h1, h2, h3, h4, ?_, ?_, ?_, h9, hnd⟩, ?_, h10, ?_⟩
    · intro t
      have ht := List.all_eq_true.mp h5 t (htabs t)
      simpa only [Bool.not_eq_true'] using ht
    · intro g
      have hg := List.all_eq_true.mp h6 g (hglobs g)
      simpa only [Bool.not_eq_true'] using hg
    · intro g hg
      have hgg := List.all_eq_true.mp h7 g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
      exact hgg.1
    · intro f hf hne
      have hfall := List.all_eq_true.mp h11 f (hvoll f)
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hfall
      cases hfall with
      | inl hnr => simp [hf] at hnr
      | inr h =>
        cases h with
        | inl heq => exact absurd heq hne
        | inr hframe =>
          obtain ⟨hft, hfg, hfd⟩ := hframe
          refine ⟨?_, ?_, hfd⟩
          · intro t
            have ht := List.all_eq_true.mp hft t (htabs t)
            simpa only [Bool.not_eq_true'] using ht
          · intro g
            have hg := List.all_eq_true.mp hfg g (hglobs g)
            simpa only [Bool.not_eq_true'] using hg
    · intro g hg
      have hgg := List.all_eq_true.mp h7 g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
      exact hgg.2
  · rintro ⟨hexp, hrahmen, hprobe, hgates⟩
    simp only [checkOkB, Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hexp
    have hnd : toreEindeutig c.gates = true := toreEindeutig_iff.mpr h9
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, hnd, h8, ?_, ?_⟩
    · exact List.all_eq_true.mpr fun t _ => by simp [h5 t]
    · exact List.all_eq_true.mpr fun g _ => by simp [h6 g]
    · exact List.all_eq_true.mpr fun g hg => by simp [h7 g hg, hgates g hg]
    · exact hprobe
    · exact List.all_eq_true.mpr fun f _ => by
        by_cases hr : reachB P fns c.probe f = true
        · by_cases he : f = c.probe
          · simp [hr, he]
          · have hfr := hrahmen f hr he
            obtain ⟨hft, hfg, hfd⟩ := hfr
            have e1 : tabs.all (fun t => !((D.signatur f).schreibt t)) = true :=
              List.all_eq_true.mpr fun t _ => by simp [hft t]
            have e2 : globs.all (fun g => !((D.signatur f).gschreibt g)) = true :=
              List.all_eq_true.mpr fun g _ => by simp [hfg g]
            have e3 : decide (c.duty ∉ (D.signatur f).produziert) = true := by simp [hfd]
            simp [hr, he, e1, e2, e3]
        · simp [hr]

/-- The checks of a unit: the Bool decides exactly the Prop. -/
theorem checkB_iff {P : Programm D} {tabs : List D.Tab} {globs : List D.Glob}
    {fns : List D.Fn} {checks : List (CheckDecl D)}
    (hvoll : ∀ g : D.Fn, g ∈ fns) (htabs : ∀ t : D.Tab, t ∈ tabs)
    (hglobs : ∀ g : D.Glob, g ∈ globs) :
    checkB P tabs globs fns checks = true ↔ CheckAdmission P fns checks := by
  simp only [checkB, CheckAdmission, Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨hall, huniq⟩ := h
    have hexp : ∀ c ∈ checks, CheckExpansion P c ∧ CheckRahmen P fns c ∧ c.probe ∈ fns ∧
        ∀ g ∈ c.gates, g ∈ fns :=
      fun c hc => (checkOkB_iff hvoll htabs hglobs).mp (List.all_eq_true.mp hall c hc)
    refine ⟨fun c hc => (hexp c hc).1, fun c hc => (hexp c hc).2.1,
      fun c hc => (hexp c hc).2.2.1, fun c hc g hg => (hexp c hc).2.2.2 g hg, ?_⟩
    exact eindeutig_iff.mp huniq
  · intro h
    obtain ⟨hexp, hrah, hprobe, hgates, huniq⟩ := h
    refine ⟨?_, eindeutig_iff.mpr huniq⟩
    exact List.all_eq_true.mpr fun c hc =>
      (checkOkB_iff hvoll htabs hglobs).mpr
        ⟨hexp c hc, hrah c hc, hprobe c hc, hgates c hc⟩

/-- The site duty of one declared check: the probe and every declared gate meet
    their body duties, tied to the same Duty by the expansion. Contract use of a
    semantic claim needs an explicit formal predicate and user proof, outside
    prose interpretation. -/
def CheckSitePflicht (P : Programm D) (Q : AxEns D) (S : SperrInv D) (passes : Nat)
    (c : CheckDecl D) : Prop :=
  CheckExpansion P c ∧
  KoerperGutS P passes Q S c.probe ∧ InvGutS P passes Q S c.probe ∧
  InvGutGrund P passes Q S c.probe ∧
  ∀ g ∈ c.gates, KoerperGutS P passes Q S g ∧ InvGutS P passes Q S g ∧
    InvGutGrund P passes Q S g

/-- The site duty follows from the admission and the user's logic. -/
theorem checkSitePflicht_aus {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    {fs : List D.Fn} {checks : List (CheckDecl D)} {c : CheckDecl D} {passes : Nat}
    (hA : CheckAdmission P fs checks) (hL : LogikPflicht P S Q) (hc : c ∈ checks) :
    CheckSitePflicht P Q S passes c := by
  obtain ⟨hexp, _, _, _, _⟩ := hA
  obtain ⟨hK, _, _⟩ := hL
  obtain ⟨hKp, hIp, hIg⟩ := hK passes c.probe
  refine ⟨hexp c hc, hKp, hIp, hIg, fun g hg => ?_⟩
  obtain ⟨hKg, hIg2, hIgg⟩ := hK passes g
  exact ⟨hKg, hIg2, hIgg⟩

/-! ## Probes: the decider on the fixture -/

/-- The fixture check is admitted over its probe and gate. -/
example : checkB pruefP [] [] [true, false] [pruefC] = true := by decide

/-- Without its gate in the unit the fixture check is refused. -/
example : checkB pruefP [] [] [true] [pruefC] = false := by decide

/-- A duplicated check name is refused. -/
example : checkB pruefP [] [] [true, false] [pruefC, pruefC] = false := by decide

end Pruefung

end Gabbro.Grammatik
