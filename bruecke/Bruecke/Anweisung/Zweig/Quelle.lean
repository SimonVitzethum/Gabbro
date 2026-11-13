module
public import Bruecke.Anweisung.Zweig.Simulation
public import Bruecke.Anweisung.Lokal.QuelleB
@[expose] public section

/-!
# C6, part 10: premise (b) for every source text, with conditionals

`PflichtenB`/`nutzer_aus_quelleB` (`Lokal/QuelleB.lean`) over the duties of `zuBodyZ`. The
duties of bodies with local bindings are duties of bodies with conditionals (`pflichtenZ_of`): a
unit `zuBodyB` carries is carried by `zuBodyZ` with the same duty.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The duties of a source text whose functions may bind locals and branch: THE STATEMENT,
    computed. -/
def PflichtenZ (src : String) : Prop :=
  ∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
    bindFrischAllB u = true ∧ rangB u (rangAuto u) = true ∧ ohneTransitionB u = true ∧
    SchnittstellenPflicht u ∧
    ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body

/-- **The duties with local bindings are duties with conditionals**: `zuBodyZ` extends
    `zuBodyB`. -/
theorem pflichtenZ_of {src : String} (hp : PflichtenB src) : PflichtenZ src := by
  obtain ⟨u, hu, hn, hs, hf, hr, hPlain, hPtr, hz⟩ := hp
  refine ⟨u, hu, hn, hs, hf, hr, hPlain, hPtr, fun c => ?_⟩
  obtain ⟨body, hbody, hm⟩ := hz c
  exact ⟨body, zuBodyZ_of_zuBodyB hbody, hm⟩

/-- **PREMISE (b) OF THE GOAL THEOREM FOR EVERY SOURCE TEXT** the Lean front end accepts, from the
    computed duties of its bodies with local bindings and conditionals -- generic in `src`. -/
theorem nutzer_aus_quelleZ {src : String} (hp : PflichtenZ src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨u', hu', hn, hs, hf, hr, hPlain, hPtr, hz⟩ := hp
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact ⟨hn, bruecke_nutzerZ (lower_of_uebersetze h) (stimmigLokal_of hs hPlain hf) (rangAuto u)
    (rang_of hr) hz (hPtr P fs (lower_of_uebersetze h)) _ rfl rfl rfl⟩

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`). -/
theorem nutzerA_aus_quelleZ {src : String} (hp : PflichtenZ src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_quelleZ hp h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_kein_atomar u (nullB_globs hn)) hb⟩

end Gabbro.Bruecke
