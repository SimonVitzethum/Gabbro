module
public import Grammatik.Zielsatz.Faeden.Ruhe.Teil1Basis
import all Grammatik.Zielsatz.Faeden.Ruhe.Teil1Basis
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch
import Grammatik.Kern.Semantik.Semantik.T1.SummeTransport
@[expose] public section



namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Transfer

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

theorem reach_mitRuhe_cases (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {w : D.Fn} {g' : D.mitRuhe.Fn} (h : reachB P.mitRuhe (fsRuhe fs) (some w) g' = true) :
    ∃ g, g' = some g ∧ reachB P fs w g = true := by
  cases g' with
  | none => rw [reachB_mitRuhe_nicht_ruhe P hAbg] at h; cases h
  | some g => exact ⟨g, rfl, by rw [← reachB_mitRuhe P hvoll hAbg]; exact h⟩

theorem reach_mitRuhe_ruhe_cases {g' : D.mitRuhe.Fn}
    (h : reachB P.mitRuhe (fsRuhe fs) none g' = true) : g' = none := by
  cases g' with
  | none => rfl
  | some g => rw [reachB_mitRuhe_ruhe P g] at h; cases h

theorem getrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : Getrennt P fs ws c) :
    Getrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne f' g' hf' hc hg'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  rw [fussOrteG_mitRuhe] at hc
  rw [traegerSchreibt_mitRuhe]
  have hne' : w₁ ≠ w₂ ∨ Mehrfach ws w₁ := by
    rcases hne with hne | hne
    · exact Or.inl (fun e => hne (e ▸ rfl))
    · exact Or.inr ((mehrfach_map_inj (fun a b e => Option.some.inj e)).mp hne)
  exact h w₁ hw₁ w₂ hw₂ hne' f g hf hc hg

theorem schreibGetrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ w, AbgK P fs (reachB P fs w)) {c : D.Tab ⊕ D.Glob}
    (h : SchreibGetrennt P fs ws c) : SchreibGetrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne g' hg' hgw h' hh'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  obtain ⟨k, rfl, hk⟩ := reach_mitRuhe_cases P hvoll hAbg hh'
  rw [fussOrteG_mitRuhe, traegerSchreibt_mitRuhe]
  rw [traegerSchreibt_mitRuhe] at hgw
  exact h w₁ hw₁ w₂ hw₂ (fun e => hne (e ▸ rfl)) g hg hgw k hk

theorem lokW_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : lokW P fs ws c = true) :
    lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws) c = true := by
  unfold lokW at h ⊢
  exact @decide_eq_true _ (Classical.propDecidable _)
    (getrennt_mitRuhe P hvoll hAbg (@of_decide_eq_true _ (Classical.propDecidable _) h))

/-- **The pool condition transfers to `P.mitRuhe`** (fix lane F10): the root is
    declared nowhere, and a user routine keeps its graph, writes and guards. -/
theorem einzelnPool_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : EinzelnPool P fs ws) : EinzelnPool P.mitRuhe (fsRuhe fs) (wsRuhe ws) := by
  intro w' hm
  cases w' with
  | none =>
      exfalso
      obtain ⟨w, _, e⟩ := mem_wsRuhe.mp (hm.subset List.mem_cons_self)
      cases e
  | some w =>
      have hp := h w ((mehrfach_map_inj (fun a b e => Option.some.inj e)).mp hm)
      refine ⟨hp.1, hp.2.1, fun f' hf' c hc => ?_⟩
      obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
      rw [traegerSchreibt_mitRuhe] at hc
      rcases hp.2.2 f hf c hc with ⟨L, hL⟩ | hA
      · exact Or.inl ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL⟩
      · exact Or.inr ((atomar_mitRuhe (D := D) c).mpr hA)

omit [DecidableEq D.Fn] in
theorem kandB_mitRuhe (L : List (D.Tab ⊕ D.Glob)) :
    kZ (kandB P.mitRuhe (fsRuhe fs) L) = kandB P fs L := by
  funext n
  show kandB P.mitRuhe (fsRuhe fs) L (n + 1) = kandB P fs L n
  unfold kandB
  rw [all_fsRuhe]
  have h0 : (D.mitRuhe).passt none (n + 1) = false :=
    decide_eq_false (Nat.succ_ne_zero n)
  rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
  congr 1
  funext g
  show (!D.passt g n ||
    ((P.mitRuhe.requires (some g)).orte ++ (P.mitRuhe.ensures (some g)).orte).all _) = _
  rw [requires_mitRuhe_orte, ensures_mitRuhe_orte]

omit [DecidableEq D.Fn] in
theorem frag_mitRuhe (h : programmImFragmentG P fs = true) :
    programmImFragmentG P.mitRuhe (fsRuhe fs) = true := by
  unfold programmImFragmentG
  rw [all_fsRuhe]
  refine Bool.and_eq_true_iff.mpr ⟨rfl, List.all_eq_true.mpr fun f hf => ?_⟩
  refine (rumpf_mitRuhe_gOk P _ _ f).trans ?_
  rw [kandB_mitRuhe, fussOrteG_mitRuhe]
  exact (List.all_eq_true.mp h) f hf

theorem abg_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w)) :
    ∀ w', AbgK P.mitRuhe (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) w') := by
  intro w' f' hf'
  cases w' with
  | none =>
      rw [reach_mitRuhe_ruhe_cases P hf']
      rfl
  | some w =>
      obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
      rw [rumpf_mitRuhe_mE]
      have e : mZ (rufM (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) (some w))) =
          rufM fs (reachB P fs w) := by
        apply merkmal_ext
        · funext h
          exact reachB_mitRuhe P hvoll hAbg w h
        · funext n
          show (fsRuhe fs).all (fun g' => !((D.mitRuhe).passt g' (n + 1)) ||
            reachB P.mitRuhe (fsRuhe fs) (some w) g') = _
          rw [all_fsRuhe]
          have h0 : (D.mitRuhe).passt none (n + 1) = false :=
            decide_eq_false (Nat.succ_ne_zero n)
          rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
          congr 1
          funext g
          show (!D.passt g n || reachB P.mitRuhe (fsRuhe fs) (some w) (some g)) = _
          rw [reachB_mitRuhe P hvoll hAbg]
        · rfl
      rw [e]
      exact hAbg w f hf

theorem fussS_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : ∀ f, FussS P S (lokW P fs ws) f) :
    ∀ f', FussS P.mitRuhe S.mitRuhe (lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws)) f'
  | none => ⟨fun c hc => by rw [fussOrte_mitRuhe_ruhe] at hc; exact absurd hc List.not_mem_nil,
      fun c hc => absurd hc List.not_mem_nil⟩
  | some f => by
      obtain ⟨h1, h2⟩ := h f
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [fussOrte_mitRuhe] at hc
        rcases h1 c hc with h3 | ⟨L, hL, hcL⟩
        · left
          simp only [Bool.or_eq_true] at h3 ⊢
          rw [sigB_mitRuhe]
          exact h3.imp id (lokW_mitRuhe P hvoll hAbg)
        · exact Or.inr ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL, hcL⟩
      · have hc' : c ∈ (P.rumpf f).regs.flatMap D.rtraeger := by
          have e := rumpf_mitRuhe_regs P f
          exact e ▸ hc
        have h3 := h2 c hc'
        simp only [Bool.or_eq_true] at h3 ⊢
        rw [sigB_mitRuhe]
        exact h3.imp id (lokW_mitRuhe P hvoll hAbg)

omit [DecidableEq D.Fn] in
theorem stufen_mitRuhe (h : StufenM P) : StufenM P.mitRuhe
  | none => rfl
  | some f => by
      show mE (bodenM (some f)) (P.mitRuhe.rumpf (some f)) = true
      rw [rumpf_mitRuhe_mE]
      exact h f

end Transfer
end Gabbro.Grammatik
