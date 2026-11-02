/- C16: the check decider is exact, and the site duty follows from it.

   `toreEindeutig_iff`/`checkOkB_iff`/`checkB_iff` tie the Bool decider
   (`CheckDecide.checkB`, over complete member lists) to exactly the Prop
   (`CheckDecide.CheckAdmission`, with the call-graph closure `CheckRahmen`
   beside the exact expansion).

   `CheckSitePflicht` is the site duty of one declared check: the probe and every
   declared gate meet their body duties, tied to the same Duty by the expansion.
   `checkSitePflicht_aus` derives it from the admission and the user's logic.

   The admission enters `AkzeptiertSpec`/`AkzeptiertSpecX` and the goal chain
   through the `checks`/`pruef` fields and the `E.pruefungen` of the unit. -/
module

public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil2
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Pruefung

variable [DecidableEq D.Fn]

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

/-! ## Witnesses: the decider and the Prop agree on the fixture -/

/-- The fixture admits its check: `checkB_iff` on the non-degenerate
    `pruefP`/`pruefC`, satisfying every premise jointly. -/
theorem checkAdmission_zeuge : CheckAdmission pruefP [true, false] [pruefC] :=
  (checkB_iff (fun g => by cases g <;> decide) (fun t => t.elim) (fun g => g.elim)).mp (by decide)

/-- The fixture gate list is distinct. -/
theorem toreEindeutig_zeuge : [false].Nodup :=
  toreEindeutig_iff.mp (by decide)

/-- The fixture check name is unique. -/
theorem eindeutig_zeuge : ([pruefC].map CheckDecl.name).Nodup :=
  eindeutig_iff.mp (by decide)

end Pruefung

end Gabbro.Grammatik
