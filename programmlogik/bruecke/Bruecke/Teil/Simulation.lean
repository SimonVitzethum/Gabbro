module
public import Bruecke.Teil.Lauf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem tabEnv_gut_teil {A : List Eintrag} (hG : ∀ e ∈ A, EintragGut u e) (ρP : Gabbro.Body.Env)
    (hP : ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract ρP n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧ Gabbro.Body.Frame ρP n (writesU (fnAt u c))) :
    ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract (tabEnv A ρP) n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
      Gabbro.Body.Frame (tabEnv A ρP) n (writesU (fnAt u c)) := by
  intro n c hc hgf
  refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm (fnAt u c) (by rw [hn]; exact hgf)).1 (by rw [hi]; exact ht)
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n c hc hgf).1 t ht
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm (fnAt u c) (by rw [hn]; exact hgf)).2 p hp
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n c hc hgf).2 t p hp

end Gabbro.Bruecke
