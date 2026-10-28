import Mathlib.Data.List.Nodup

/-!
  File:      Grammatik/Zielsatz/Projekte/Annahmen.lean
  Subject:   **The assumption sets of linked projects join** (BUILD-SYSTEM 7.5, L3): the Lean twin of
             the checker's `manifest::vereinige`.

  An assumption is a KEY (its name and the machine it is about) and a CONTENT (kind, class,
  statement, preconditions). Joining the projects' lists keeps the first entry of every key and
  reports every key that comes again with a different content -- a contradiction in the assumption
  set, never a duplicate (`vereinige`).

  * `vereinige_teil`: nothing is invented -- every kept entry is an input entry.
  * `vereinige_eindeutig`: every key is kept once (the result is a set).
  * **`vereinige_voll`**: without a reported contradiction every input entry is kept, so the joined
    set assumes exactly what every project assumed, no more and no less.
  * `vereinige_streit`: a key is reported exactly when two input entries share it with different
    content.
-/

namespace Gabbro.Grammatik.Zielsatz.Annahmen

variable {K C : Type} [DecidableEq K] [DecidableEq C]

/-- One step: keep a new key, report a known key with another content. -/
def schritt (acc : List (K × C) × List K) (e : K × C) : List (K × C) × List K :=
  match acc.1.find? (fun a => a.1 = e.1) with
  | none => (acc.1 ++ [e], acc.2)
  | some a => if a.2 = e.2 then acc else (acc.1, acc.2 ++ [e.1])

/-- **Join the assumption entries** of all projects: the kept set and the contradictions. -/
def vereinige (alle : List (K × C)) : List (K × C) × List K :=
  alle.foldl schritt ([], [])

/-- The invariant of the fold: kept entries come from the input, keys are kept once, every input
    entry seen so far has its key kept, and a seen entry whose content differs from the kept one
    is reported. -/
structure Inv (gesehen : List (K × C)) (acc : List (K × C) × List K) : Prop where
  teil : ∀ a ∈ acc.1, a ∈ gesehen
  eindeutig : (acc.1.map Prod.fst).Nodup
  schluessel : ∀ e ∈ gesehen, ∃ a ∈ acc.1, a.1 = e.1
  streit : ∀ e ∈ gesehen, ∀ a ∈ acc.1, a.1 = e.1 → a.2 ≠ e.2 → e.1 ∈ acc.2
  gemeldet : ∀ k ∈ acc.2, ∃ e ∈ gesehen, ∃ a ∈ acc.1, a.1 = k ∧ e.1 = k ∧ a.2 ≠ e.2

theorem find_key {l : List (K × C)} {k : K} :
    l.find? (fun a => a.1 = k) = none ↔ ∀ a ∈ l, a.1 ≠ k := by
  simp only [List.find?_eq_none, decide_eq_true_eq, Prod.forall, ne_eq]

theorem eindeutig_eq {l : List (K × C)} (h : (l.map Prod.fst).Nodup) {a b : K × C}
    (ha : a ∈ l) (hb : b ∈ l) (hk : a.1 = b.1) : a = b :=
  List.inj_on_of_nodup_map h ha hb hk

theorem inv_schritt {g : List (K × C)} {acc : List (K × C) × List K} (h : Inv g acc) (e : K × C) :
    Inv (g ++ [e]) (schritt acc e) := by
  unfold schritt
  cases hf : acc.1.find? (fun a => a.1 = e.1) with
  | none =>
      have hn := find_key.mp hf
      show Inv (g ++ [e]) (acc.1 ++ [e], acc.2)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (h.teil a ha)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨h.eindeutig, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; subst hxy
        obtain ⟨a, ha, hae⟩ := List.mem_map.mp hx
        exact hn a ha hae
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨a, ha, hk⟩ := h.schluessel x hx
          exact ⟨a, List.mem_append_left _ ha, hk⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; exact ⟨x, by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true], rfl⟩
      · intro x hx a ha hk hc
        rcases List.mem_append.mp ha with ha1 | ha1
        · rcases List.mem_append.mp hx with hx1 | hx1
          · exact h.streit x hx1 a ha1 hk hc
          · have hxe : x = e := by simpa using hx1
            exact absurd (hk.trans (congrArg Prod.fst hxe)) (hn a ha1)
        · have hae : a = e := by simpa using ha1
          rcases List.mem_append.mp hx with hx1 | hx1
          · obtain ⟨b, hb, hbk⟩ := h.schluessel x hx1
            exact absurd (hbk.trans (hk.symm.trans (congrArg Prod.fst hae))) (hn b hb)
          · have hxe : x = e := by simpa using hx1
            exact absurd (congrArg Prod.snd (hae.trans hxe.symm)) hc
      · intro k hk
        obtain ⟨x, hx, a, ha, h1, h2, h3⟩ := h.gemeldet k hk
        exact ⟨x, List.mem_append_left _ hx, a, List.mem_append_left _ ha, h1, h2, h3⟩
  | some a =>
      show Inv (g ++ [e]) (if a.2 = e.2 then acc else (acc.1, acc.2 ++ [e.1]))
      have ha := List.mem_of_find?_eq_some hf
      have hak : a.1 = e.1 := by have := List.find?_some hf; simpa using this
      have alt : ∀ x ∈ g ++ [e], x ∈ g ∨ x = e := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact Or.inr hx
      by_cases hc : a.2 = e.2
      · simp only [hc, ite_true]
        refine ⟨fun x hx => List.mem_append_left _ (h.teil x hx), h.eindeutig, ?_, ?_, ?_⟩
        · intro x hx
          rcases alt x hx with hx | rfl
          · exact h.schluessel x hx
          · exact ⟨a, ha, hak⟩
        · intro x hx b hb hk hcb
          rcases alt x hx with hx | rfl
          · exact h.streit x hx b hb hk hcb
          · have := eindeutig_eq h.eindeutig hb ha (hk.trans hak.symm)
            subst this; exact absurd hc hcb
        · intro k hk
          obtain ⟨x, hx, b, hb, h1, h2, h3⟩ := h.gemeldet k hk
          exact ⟨x, List.mem_append_left _ hx, b, hb, h1, h2, h3⟩
      · simp only [hc, ite_false]
        refine ⟨fun x hx => List.mem_append_left _ (h.teil x hx), h.eindeutig, ?_, ?_, ?_⟩
        · intro x hx
          rcases alt x hx with hx | rfl
          · exact h.schluessel x hx
          · exact ⟨a, ha, hak⟩
        · intro x hx b hb hk hcb
          rcases alt x hx with hx | rfl
          · exact List.mem_append_left _ (h.streit x hx b hb hk hcb)
          · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · obtain ⟨x, hx, b, hb, h1, h2, h3⟩ := h.gemeldet k hk
            exact ⟨x, List.mem_append_left _ hx, b, hb, h1, h2, h3⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk
            exact ⟨e, List.mem_append_right _ (List.mem_singleton.mpr rfl), a, ha, hak, rfl, hc⟩

theorem inv_foldl : ∀ (l g : List (K × C)) (acc : List (K × C) × List K), Inv g acc →
    Inv (g ++ l) (l.foldl schritt acc)
  | [], g, acc, h => by simpa using h
  | e :: l, g, acc, h => by
      have := inv_foldl l (g ++ [e]) (schritt acc e) (inv_schritt h e)
      simpa using this

theorem inv_vereinige (alle : List (K × C)) : Inv alle (vereinige alle) := by
  have := inv_foldl alle [] ([], []) ⟨(fun _ h => by cases h), List.nodup_nil, (fun _ h => by cases h),
    (fun _ h => by cases h), (fun _ h => by cases h)⟩
  simpa [vereinige] using this

/-- **Nothing is invented.** -/
theorem vereinige_teil (alle : List (K × C)) : ∀ a ∈ (vereinige alle).1, a ∈ alle :=
  (inv_vereinige alle).teil

/-- **Every key is kept once.** -/
theorem vereinige_eindeutig (alle : List (K × C)) : ((vereinige alle).1.map Prod.fst).Nodup :=
  (inv_vereinige alle).eindeutig

/-- **Without a reported contradiction, every input entry is kept**: the joined set assumes exactly
    what the projects assumed. -/
theorem vereinige_voll (alle : List (K × C)) (h : (vereinige alle).2 = []) :
    ∀ e ∈ alle, e ∈ (vereinige alle).1 := by
  intro e he
  obtain ⟨a, ha, hk⟩ := (inv_vereinige alle).schluessel e he
  by_cases hc : a.2 = e.2
  · rw [show e = a from Prod.ext hk.symm hc.symm]; exact ha
  · have := (inv_vereinige alle).streit e he a ha hk hc
    rw [h] at this; cases this

/-- **A key is reported exactly when two input entries share it with different content.** -/
theorem vereinige_streit (alle : List (K × C)) (k : K) :
    k ∈ (vereinige alle).2 ↔ ∃ e ∈ alle, ∃ e' ∈ alle, e.1 = k ∧ e'.1 = k ∧ e.2 ≠ e'.2 := by
  constructor
  · intro hk
    obtain ⟨x, hx, a, ha, h1, h2, h3⟩ := (inv_vereinige alle).gemeldet k hk
    exact ⟨a, vereinige_teil alle a ha, x, hx, h1, h2, h3⟩
  · rintro ⟨e, he, e', he', h1, h2, h3⟩
    obtain ⟨a, ha, hak⟩ := (inv_vereinige alle).schluessel e he
    by_cases hc : a.2 = e.2
    · have : a.2 ≠ e'.2 := hc ▸ h3
      have := (inv_vereinige alle).streit e' he' a ha (hak.trans (h1.trans h2.symm)) this
      rwa [h2] at this
    · have := (inv_vereinige alle).streit e he a ha hak hc
      rwa [h1] at this

#print axioms vereinige_voll
#print axioms vereinige_streit

end Gabbro.Grammatik.Zielsatz.Annahmen
