module
public import Bruecke.Kette.Andocken.Zertifikat
public import Bruecke.Kette.Andocken.BildErfuellbar
@[expose] public section

/-!
# The premises of `nutzerA_aus_ziele` hold jointly

For the unit of one function `main` returning `42`: every function's duty `ZielF` holds, the
unit has no foreign body, and Stage 0's decision of the data parts accepts its judged unit for
every lowered program, axiom family, memory, entry and arguments. The two run facts are facts of
a Stage 0 run and are not instantiated here.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

theorem nutzerA_aus_ziele_erfuellbar :
    ∃ u : UProg, (∀ f, ZielF u f) ∧ u.fns ≠ [] ∧ u.axs = [] ∧
      ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs) →
        ∀ (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
          (args : Env (declOf u) ((declOf u).params main)),
          entschiedenB (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args [] [] [])
            (List.finRange u.locks.length) = true := by
  have hp : PflichtenEinheit einheitErfuellbar := by
    refine ⟨⟨by with_unfolding_all decide, by with_unfolding_all decide,
      by with_unfolding_all decide⟩, fun _ => 0, ?_⟩
    intro f hf
    have hf' : f = mainErfuellbar := by
      simpa only [einheitErfuellbar, List.mem_singleton] using hf
    subst hf'
    refine ⟨by with_unfolding_all decide, by with_unfolding_all decide, by with_unfolding_all decide,
      [.ret (some (.lit (.int 42)))], by with_unfolding_all rfl, ?_⟩
    intro ρ s hwf _
    refine ⟨s, rfl, ?_⟩
    simp only [postU, ensList, mainErfuellbar, resultClause, Gabbro.Body.finalValue, Gabbro.Body.exec,
      Gabbro.Body.step, Gabbro.Body.eval, chain, Option.toList, List.append_nil, Option.map_some,
      Option.getD_some]
    exact ⟨hwf, 42, rfl, by decide, by decide⟩
  have hl : einheitErfuellbar.locks = [] := rfl
  have ha : einheitErfuellbar.axs = [] := rfl
  refine ⟨einheitErfuellbar, fun f P fs hlow Q sp main args roots gestartet checks =>
    (logik_aus_nutzerA _ (nutzerA_einheitDer hp hl ha hlow Q sp main args roots gestartet checks)).1 f,
    by simp [einheitErfuellbar], rfl, ?_⟩
  intro P fs hlow Q sp main args
  have hreq : P.requires main = .tru := by
    refine requires_tru_of_needs_leer hlow main ?_
    match main with
    | ⟨0, _⟩ => rfl
  simp only [entschiedenB, Bool.and_eq_true]
  refine ⟨by with_unfolding_all rfl, ?_⟩
  simp only [List.all_eq_true]
  intro a ha'
  simp only [Gabbro.Stage0.OldSource.einheitDer, Gabbro.Stage0.OldSource.einheitVon, List.append_nil,
    List.mem_singleton] at ha'
  subst ha'
  show (checkStartRequires P sp ⟨main, args⟩).toOption.isSome = true
  have hk : (Invarianten.Frag.translate (P.requires main) args).toOption.isSome = true := by
    generalize P.requires main = r at hreq ⊢
    subst hreq
    with_unfolding_all rfl
  cases he : Invarianten.Frag.translate (P.requires main) args with
  | error e => rw [he] at hk; cases hk
  | ok enc =>
    refine (checkStartRequires_iff (start := ⟨main, args⟩) he).mpr ?_
    unfold ReqAmEintritt
    rw [hreq]
    rfl

#print axioms nutzerA_aus_ziele_erfuellbar

end Gabbro.Bruecke
