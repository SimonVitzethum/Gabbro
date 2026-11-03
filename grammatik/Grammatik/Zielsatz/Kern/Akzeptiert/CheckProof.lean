module

public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Spec

@[expose] public section
namespace Gabbro.Grammatik
open Zielsatz
variable {D : Deklaration}
section Pruefung

variable [DecidableEq D.Fn]

/-- Distinct gates as a Prop: one Duty is never duplicated across them. -/
theorem toreEindeutig_iff {gates : List D.Fn} :
    toreEindeutig gates = true ↔ gates.Nodup := by
  induction gates with
  | nil => simp [toreEindeutig]
  | cons g rest ih =>
    have hmem : (∀ x ∈ rest, x ≠ g) ↔ g ∉ rest := by
      constructor
      · intro h hg
        exact h g hg rfl
      · intro h x hx heq
        exact h (heq ▸ hx)
    simp only [toreEindeutig, Bool.and_eq_true, decide_eq_true_eq, List.nodup_cons]
    exact and_congr hmem ih

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
    simp only [checkOkB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
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
      simp only [rahmenOkB, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_eq_true', or_assoc, and_assoc] at h11
      have hfall := h11 f (hvoll f)
      cases hfall with
      | inl hnr => simp [hf] at hnr
      | inr h =>
        cases h with
        | inl heq => exact absurd heq hne
        | inr hframe =>
          obtain ⟨hft, hfg, hfd⟩ := hframe
          refine ⟨?_, ?_, hfd⟩
          · intro t
            exact hft t (htabs t)
          · intro g
            exact hfg g (hglobs g)
    · intro g hg
      have hgg := List.all_eq_true.mp h7 g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgg
      exact hgg.2
  · rintro ⟨hexp, hrahmen, hprobe, hgates⟩
    simp only [checkOkB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hexp
    have hnd : toreEindeutig c.gates = true := toreEindeutig_iff.mpr h9
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, hnd, h8, ?_, ?_⟩
    · exact List.all_eq_true.mpr fun t _ => by simp [h5 t]
    · exact List.all_eq_true.mpr fun g _ => by simp [h6 g]
    · exact List.all_eq_true.mpr fun g hg => by simp [h7 g hg, hgates g hg]
    · exact hprobe
    · unfold rahmenOkB
      exact List.all_eq_true.mpr fun f _ => by
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

private theorem pruef_fns_voll (f : pruefD.Fn) : f ∈ [true, false] := by
  cases f <;> simp

private theorem pruef_checkOkB : checkOkB pruefP [] [] [true, false] pruefC = true := by
  apply (checkOkB_iff (D := pruefD) (tabs := []) (globs := [])
    pruef_fns_voll (fun t => nomatch t) (fun g => nomatch g)).mpr
  refine ⟨pruef_expansion, ?_, by simp [pruefC], ?_⟩
  · intro f _ hne
    cases f with
    | false => exact ⟨(fun t => nomatch t), (fun g => nomatch g), List.not_mem_nil⟩
    | true => exact False.elim (hne rfl)
  · intro g hg
    have hf : g = false := List.mem_singleton.mp hg
    subst g
    simp

private theorem pruef_checkB : checkB pruefP [] [] [true, false] [pruefC] = true := by
  simp [checkB, pruef_checkOkB, eindeutigeNamen]

/-- The fixture check is admitted over its probe and gate. -/
example : checkB pruefP [] [] [true, false] [pruefC] = true := pruef_checkB

/-- Without its gate in the unit the fixture check is refused. -/
example : checkB pruefP [] [] [true] [pruefC] = false := by
  have hg : pruefC.gates.all (fun g =>
      decide (pruefC.duty ∈ (pruefD.signatur g).konsumiert) &&
        decide (g ∈ ([true] : List pruefD.Fn))) = false := by decide
  have hc : checkOkB pruefP [] [] [true] pruefC = false := by
    simp only [checkOkB, hg, Bool.and_false, Bool.false_and]
  simp [checkB, hc]

/-- A duplicated check name is refused. -/
example : checkB pruefP [] [] [true, false] [pruefC, pruefC] = false := by
  have hn : eindeutigeNamen (D := pruefD) [pruefC, pruefC] = false := by decide
  simp only [checkB, hn, Bool.and_false]

/-! ## Witnesses: the decider and the Prop agree on the fixture -/

/-- The fixture admits its check: `checkB_iff` on the non-degenerate
    `pruefP`/`pruefC`, satisfying every premise jointly. -/
theorem checkAdmission_zeuge : CheckAdmission pruefP [true, false] [pruefC] :=
  (checkB_iff (D := pruefD) (tabs := []) (globs := [])
    pruef_fns_voll (fun t => nomatch t) (fun g => nomatch g)).mp pruef_checkB

/-- The fixture gate list is distinct. -/
theorem toreEindeutig_zeuge : [false].Nodup :=
  (toreEindeutig_iff (D := pruefD)).mp (by decide)

/-- The fixture check name is unique. -/
theorem eindeutig_zeuge : ([pruefC].map CheckDecl.name).Nodup :=
  eindeutig_iff.mp (by decide)

end Pruefung

end Gabbro.Grammatik
