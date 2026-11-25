/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Beweise/Bestimmt.lean
  Subject:   DETERMINACY OF AN ACCESS INSTRUCTION UP TO THE VALUE IT READS. The open duty
             `ZugriffBestimmtAussage` (pinned in the closure of `ZugriffBefehlAussage`) states that two ideal
             steps of one access instruction from one state, context and choice coincide once the values their
             recorded reads return coincide. The proof is generic over the step form: `zugriffsschritt` splits
             on `befugt`, which the state decides; a refusal is the private plan and the halted frame; a granted
             step picks a value `v`, and the class records `v` in the read label of its plan. For a reading class
             (`lesen`, `rmw`) the equality of read values gives `v = v'`; for a class that does not read, both
             values are `0` (`Wirkungsklasse.Lesewert`). Equal values make the plan and the updated state equal.
             No per-instruction case and no witness is used.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Aussagen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-! ### Determinacy of one step of a class -/

/-- **A step of a class is determined up to the value it reads.** Two steps of the same form from the same state
    and context with the same authority decision are equal as soon as the values their plans record as read are
    equal. -/
theorem Schrittform.zugriffsschritt_bestimmt (F : Schrittform) {c : Kontext} {s : Zustand}
    {plans plans' : List Plan} {u u' : Zustand}
    (step : F.zugriffsschritt c s plans u) (step' : F.zugriffsschritt c s plans' u')
    (hlesen : ∀ p p', plans = [p] → plans' = [p'] →
      p.lesen.map (fun l => l.gelesen) = p'.lesen.map (fun l => l.gelesen)) :
    plans = plans' ∧ u = u' := by
  by_cases hg : F.klasse.befugt (F.operand (s.lokal c)) s c
  · rcases step with ⟨hng, _, _⟩ | ⟨_, v, hv, hp, hu⟩
    · exact (hng hg).elim
    rcases step' with ⟨hng', _, _⟩ | ⟨_, v', hv', hp', hu'⟩
    · exact (hng' hg).elim
    have vv : v = v' := by
      by_cases hl : F.klasse.liest = true
      · have gl := hlesen (F.plan (s.lokal c) v) (F.plan (s.lokal c) v') hp hp'
        obtain ⟨k, o, t⟩ := F
        cases k with
        | lesen m =>
            exact (List.cons.inj (by
              simpa only [Schrittform.plan, Wirkungsklasse.plan, List.map_cons, List.map_nil] using gl)).1
        | rmw m =>
            exact (List.cons.inj (by
              simpa only [Schrittform.plan, Wirkungsklasse.plan, List.map_cons, List.map_nil] using gl)).1
        | lokal => cases hl
        | ruf => cases hl
        | schreiben _ => cases hl
        | zaun _ => cases hl
        | sperre _ => cases hl
        | frage => cases hl
        | starte => cases hl
        | beende => cases hl
        | verbinde => cases hl
        | wechsle => cases hl
      · have hv0 : v = 0 := by
          simpa only [Wirkungsklasse.Lesewert, hl, reduceCtorEq, false_or] using hv
        have hv0' : v' = 0 := by
          simpa only [Wirkungsklasse.Lesewert, hl, reduceCtorEq, false_or] using hv'
        exact hv0.trans hv0'.symm
    subst v'
    exact ⟨hp.trans hp'.symm, hu.trans hu'.symm⟩
  · rcases step with ⟨_, hp, hu⟩ | ⟨hgg, _, _, _, _⟩
    · rcases step' with ⟨_, hp', hu'⟩ | ⟨hgg', _, _, _, _⟩
      · exact ⟨hp.trans hp'.symm, hu.trans hu'.symm⟩
      · exact (hg hgg').elim
    · exact (hg hgg).elim

/-! ### The instruction -/

/-- The ideal step of an access instruction is the step of its form: each of the seven forms has a reading or
    writing class, for which `Schrittform.ideal` is `zugriffsschritt`. -/
theorem zugriff_ideal_zugriffsschritt (z : Zugriffsform) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    (Befehl.zugriff z).ideal c s w plans u ↔ (Befehl.zugriff z).form.zugriffsschritt c s plans u := by
  cases z <;> rfl

/-- **Determinacy of an access instruction up to the value it reads** (the proof of `ZugriffBestimmtAussage`). -/
theorem zugriffBestimmt : ZugriffBestimmtAussage := by
  intro z c s w plans plans' u u' step step' hlesen
  exact Schrittform.zugriffsschritt_bestimmt (Befehl.zugriff z).form
    ((zugriff_ideal_zugriffsschritt z c s w plans u).1 step)
    ((zugriff_ideal_zugriffsschritt z c s w plans' u').1 step') hlesen

end Gabbro.Core.Ast.Semantik
