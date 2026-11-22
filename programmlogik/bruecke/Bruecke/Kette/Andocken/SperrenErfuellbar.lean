module
public import Bruecke.Kette.Andocken.Sperren
public import Bruecke.Kette.Andocken.BildErfuellbar
@[expose] public section

/-!
# The premises of `nutzerA_aus_compiled_sperren` hold jointly, with a declared lock

An instance in which the form occurs: the unit of `nutzerA_aus_compiled_erfuellbar` (one carried
function `main` returning `42`, its duty `meetsU` proved) with one declared lock `L` (no
invariant). Its duties hold, it declares a lock and no foreign body, and Stage 0's lock decision
accepts the judged unit for every program, axiom family, initial memory, entry, starts and checks.
The two run facts (`c.unit = u`, `ohneAltGlobalB c.expanded`) are facts of a Stage 0 run and are
not instantiated here.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.Cover.Differenz

/-- The unit of `einheitErfuellbar` with one declared lock. -/
def einheitSperrErfuellbar : UProg :=
  { einheitErfuellbar with locks := [{ name := "L", rank := 0, guard := [] }] }

theorem einheitSperrErfuellbar_pflichten : PflichtenEinheit einheitSperrErfuellbar := by
  refine ⟨⟨by with_unfolding_all decide, by with_unfolding_all decide,
    by with_unfolding_all decide⟩, fun _ => 0, ?_⟩
  intro f hf
  have hf' : f = mainErfuellbar := by
    simpa only [einheitSperrErfuellbar, einheitErfuellbar, List.mem_singleton] using hf
  subst hf'
  refine ⟨by with_unfolding_all decide, by with_unfolding_all decide, by with_unfolding_all decide,
    [.ret (some (.lit (.int 42)))], by with_unfolding_all rfl, ?_⟩
  intro ρ s hwf _
  refine ⟨s, rfl, ?_⟩
  simp only [postU, ensList, mainErfuellbar, resultClause, Gabbro.Body.finalValue, Gabbro.Body.exec,
    Gabbro.Body.step, Gabbro.Body.eval, chain, Option.toList, List.append_nil, Option.map_some,
    Option.getD_some]
  exact ⟨hwf, 42, rfl, by decide, by decide⟩

/-- **The premises hold jointly**: the unit's duties, a declared lock, no foreign body, and Stage
    0's lock decision on its judged unit, for every program, memory, entry, starts and checks. -/
theorem nutzerA_aus_compiled_sperren_erfuellbar :
    ∃ u : UProg, PflichtenEinheit u ∧ u.axs = [] ∧ u.locks ≠ [] ∧
      ∀ (P : Programm (declOf u)) (Q : AxEns (declOf u)) (sp : Speicher (declOf u))
        (main : (declOf u).Fn) (args : Env (declOf u) ((declOf u).params main))
        (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
        (checks : List (CheckDecl (declOf u))),
        sperrenGeprueftB (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks)
          (List.finRange u.locks.length) = true := by
  refine ⟨einheitSperrErfuellbar, einheitSperrErfuellbar_pflichten, rfl, by simp [einheitSperrErfuellbar], ?_⟩
  intro P Q sp main args roots gestartet checks
  with_unfolding_all rfl

#print axioms nutzerA_aus_compiled_sperren_erfuellbar

end Gabbro.Bruecke
