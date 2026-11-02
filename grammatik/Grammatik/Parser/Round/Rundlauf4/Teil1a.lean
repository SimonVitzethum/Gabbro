/-
  File:      Grammatik/Parser/Rundlauf4.lean
  Subject:   T3 (lane 195): the remaining primaries -- level 6.

  Rundlauf3 closes at level 5 (`gutEmb`: kernel, comparisons,
  bits, add/mul spellings, calls, builtins). MUSE-REPORT-172
  "Open" lists what is left per constructor: `alt`, `res`,
  `fnref`, `grund` ("single-constructor primaries, small, not
  started") and statements (`SAnw`, untouched -- NOT this file).

  This file takes the four primaries, each as one new layer over
  the previous predicate, in the established one-level pattern
  (no nested list patterns -- MUSE-REPORT-172 finding 3):

  - `altNeu`: `.old x` over KERNEL places (`gutKernPlatz`, the
    `sizeof` precedent). Full `gutPlatz` payloads carry arbitrary
    `gut` index expressions and need the joint size induction
    (Rundlauf3 header: the exact remaining blocker).
  - `ergebnisNeu`: `.res`, no payload (lane 161's
    `prim_ergebnis`, reused).
  - `fnwertNeu`: `.fnref p`, no tree payload. `primFrei` is
    false, so there is no primary leg -- the leg below is at
    `parseUnary` (`&` arm, segments stop by `sammleSeg_stop`
    under `ruhigSuff`).
  - `grundNeu`: `.why g f` with exactly `gut`'s side
    conditions (lane 161's `prim_grund`, reused).

  `gutPrim e = gutEmb e || primNeu e`; `parse_druck_prim` is the
  level-6 goal. Statements are NOT entered here.
-/
module

public import Grammatik.Parser.Round.Rundlauf4.Teil1
public import Grammatik.Parser.Round.Rundlauf3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser
-- `&p` legs from the unary `&` arm; the primary component is
-- vacuous (`primFrei` is false for `fnref`).
theorem fnwertLegs : ∀ (p : String), Legs (.fnref p) := by
  intro p
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.fnref p) + 1) + groesse (.fnref p) + 2 ≤ G →
      parseUnary G (druckToks (.fnref p) ++ rest') =
        .ok (.fnref p, rest') := by
    intro rest' G hrs hrg hG
    exact un_fnwert_legs p rest' G hrs hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    simp only [primFrei, Bool.false_eq_true] at hpf
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnref p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- `G::F` legs (primary leg by lane 161's `prim_grund`).
theorem grundLegs : ∀ (g f : String),
    (!istKopfWort g) = true → (!istIntWort g) = true →
    (!istZuckerBreite g) = true → (!(strEq g "Self")) = true →
    Legs (.why g f) := by
  intro g f hkp hit hzuk hself
  have hd : druckToks (.why g f) = [nameTok g] ++
      [.zeichen "::", nameTok f] := by
    simp only [druckToks, List.cons_append, List.nil_append]
  apply identTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_grund g f rest' G hkp hit hzuk hself hrs (by omega)

-- Every `altNeu` tree has legs.
theorem legsAlt : ∀ (e : SExpr), altNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp only [altNeu, Bool.false_eq_true] at hg
  | float s => simp only [altNeu, Bool.false_eq_true] at hg
  | tru => simp only [altNeu, Bool.false_eq_true] at hg
  | fls => simp only [altNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [altNeu, Bool.false_eq_true] at hg
  | un o x => simp only [altNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [altNeu, Bool.false_eq_true] at hg
  | field x f => simp only [altNeu, Bool.false_eq_true] at hg
  | index x i => simp only [altNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [altNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [altNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [altNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [altNeu, Bool.false_eq_true] at hg
  | old x =>
    simp only [altNeu] at hg
    exact altLegs x hg
  | res => simp only [altNeu, Bool.false_eq_true] at hg
  | why g f => simp only [altNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [altNeu, Bool.false_eq_true] at hg

-- Every `ergebnisNeu` tree has legs.
theorem legsErgebnis : ∀ (e : SExpr), ergebnisNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | float s => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | tru => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | fls => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | un o x => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | field x f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | index x i => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | old x => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | res => exact ergebnisLegs
  | why g f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg

-- Every `fnwertNeu` tree has legs.
theorem legsFnwert : ∀ (e : SExpr), fnwertNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | float s => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | tru => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | fls => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | un o x => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | field x f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | index x i => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | fnref p => exact fnwertLegs p
  | built f xs => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | old x => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | res => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | why g f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [fnwertNeu, Bool.false_eq_true] at hg

-- Every `grundNeu` tree has legs.
theorem legsGrund : ∀ (e : SExpr), grundNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp only [grundNeu, Bool.false_eq_true] at hg
  | float s => simp only [grundNeu, Bool.false_eq_true] at hg
  | tru => simp only [grundNeu, Bool.false_eq_true] at hg
  | fls => simp only [grundNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [grundNeu, Bool.false_eq_true] at hg
  | un o x => simp only [grundNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [grundNeu, Bool.false_eq_true] at hg
  | field x f => simp only [grundNeu, Bool.false_eq_true] at hg
  | index x i => simp only [grundNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [grundNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [grundNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [grundNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [grundNeu, Bool.false_eq_true] at hg
  | old x => simp only [grundNeu, Bool.false_eq_true] at hg
  | res => simp only [grundNeu, Bool.false_eq_true] at hg
  | why g f =>
    simp only [grundNeu, Bool.and_eq_true] at hg
    obtain ⟨hABC, hself⟩ := hg
    obtain ⟨hAB, hzuk⟩ := hABC
    obtain ⟨hkp, hit⟩ := hAB
    exact grundLegs g f hkp hit hzuk hself
  | ext xk xn xs => simp only [grundNeu, Bool.false_eq_true] at hg

-- Every level-6-new tree has legs (the `obtain` shape mirrors
-- `legsEmb`: the four-way `||` splits left-nested).
theorem legsPrimNeu : ∀ (e : SExpr), primNeu e = true → Legs e := by
  intro e hg
  simp only [primNeu, Bool.or_eq_true] at hg
  obtain h123 | h4 := hg
  · obtain h12 | h3 := h123
    · obtain h1 | h2 := h12
      · exact legsAlt e h1
      · exact legsErgebnis e h2
    · exact legsFnwert e h3
  · exact legsGrund e h4

-- Every level-6 tree has legs.
theorem legsPrim : ∀ (e : SExpr), gutPrim e = true → Legs e := by
  intro e hg
  simp only [gutPrim, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact legsEmb e hold
  · exact legsPrimNeu e hnew

-- Level-6 goal: every `gutPrim` tree parses back from its
-- printed tokens with `brennstoff` fuel.
theorem parse_druck_prim : ∀ (e : SExpr), gutPrim e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsPrim e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Bridge for the `alt` layer (kernel places are places).
theorem gut_of_altNeu : ∀ (e : SExpr), altNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp only [altNeu, Bool.false_eq_true] at hg
  | float s => simp only [altNeu, Bool.false_eq_true] at hg
  | tru => simp only [altNeu, Bool.false_eq_true] at hg
  | fls => simp only [altNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [altNeu, Bool.false_eq_true] at hg
  | un o x => simp only [altNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [altNeu, Bool.false_eq_true] at hg
  | field x f => simp only [altNeu, Bool.false_eq_true] at hg
  | index x i => simp only [altNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [altNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [altNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [altNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [altNeu, Bool.false_eq_true] at hg
  | old x =>
    simp only [altNeu] at hg
    simp only [gut]
    exact gutPlatz_of_gutKernPlatz x hg
  | res => simp only [altNeu, Bool.false_eq_true] at hg
  | why g f => simp only [altNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [altNeu, Bool.false_eq_true] at hg

-- Bridge for the `res` layer.
theorem gut_of_ergebnisNeu : ∀ (e : SExpr),
    ergebnisNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | float s => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | tru => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | fls => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | un o x => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | field x f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | index x i => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | old x => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | res => rfl
  | why g f => simp only [ergebnisNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [ergebnisNeu, Bool.false_eq_true] at hg

-- Bridge for the `fnref` layer.
theorem gut_of_fnwertNeu : ∀ (e : SExpr),
    fnwertNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | float s => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | tru => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | fls => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | un o x => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | field x f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | index x i => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | fnref p => rfl
  | built f xs => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | old x => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | res => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | why g f => simp only [fnwertNeu, Bool.false_eq_true] at hg
  | ext xk xn xs => simp only [fnwertNeu, Bool.false_eq_true] at hg

end Gabbro.Grammatik.Parser
