module
public import Bruecke.Anweisung.Lokal.SimulationB
public import Bruecke.Quelle
@[expose] public section

/-!
# C5, part 6: premise (b) for every source text, with local bindings

`Pflichten`/`nutzer_aus_quelle` (`Quelle.lean`) over the duties of `zuBodyB`, with freshness of
every binder decided beside the other per-unit checks. The old duties give the new ones
(`pflichtenB_of`): a unit `zuBody` carries is carried by `zuBodyB` with the same duty.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The duties of a source text whose functions may bind locals: THE STATEMENT, computed. -/
def PflichtenB (src : String) : Prop :=
  ∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
    bindFrischAllB u = true ∧ rangB u (rangAuto u) = true ∧ ohneTransitionB u = true ∧
    SchnittstellenPflicht u ∧
    ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body

/-- **The old duties are new duties**: `zuBodyB` extends `zuBody`, and a body without binders
    passes the freshness check. -/
theorem pflichtenB_of {src : String} (hp : Pflichten src) : PflichtenB src := by
  obtain ⟨u, hu, hn, hs, hr, hPlain, hPtr, hz⟩ := hp
  refine ⟨u, hu, hn, hs, ?_, hr, hPlain, hPtr, fun c => ?_⟩
  · refine List.all_eq_true.mpr (fun f hf => ?_)
    obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hf
    obtain ⟨body, hbody, _⟩ := hz c
    rw [zuBody_eq] at hbody
    cases hs' : stmtsBody u (fnAt u c) (fnAt u c).body with
    | none => rw [hs'] at hbody; cases hbody
    | some bs => exact bindFrischLB_ohne _ _ bs hs'
  · obtain ⟨body, hbody, hm⟩ := hz c
    exact ⟨body, zuBodyB_of_zuBody hbody, hm⟩

/-- **PREMISE (b) OF THE GOAL THEOREM FOR EVERY SOURCE TEXT** the Lean front end accepts, from the
    computed duties of its bodies with local bindings -- generic in `src`. -/
theorem nutzer_aus_quelleB {src : String} (hp : PflichtenB src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨u', hu', hn, hs, hf, hr, hPlain, hPtr, hz⟩ := hp
  rw [uOf_eq h] at hu'
  injection hu' with hu'
  subst hu'
  exact ⟨hn, bruecke_nutzerB (lower_of_uebersetze h) (stimmigLokal_of hs hPlain hf) (rangAuto u)
    (rang_of hr) hz (hPtr P fs (lower_of_uebersetze h)) _ rfl rfl rfl⟩

/-- The same premise WITH THE ATOMIC RELY (`NutzerPflichtA`). -/
theorem nutzerA_aus_quelleB {src : String} (hp : PflichtenB src) {u : UProg}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_quelleB hp h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_kein_atomar u (nullB_globs hn)) hb⟩

end Gabbro.Bruecke
