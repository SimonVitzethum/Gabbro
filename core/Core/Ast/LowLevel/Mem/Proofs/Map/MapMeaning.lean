module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine

private theorem allRange_of {p : Nat → Bool} : ∀ n, (∀ i < n, p i = true) → (List.range n).all p = true
  | 0, _ => by simp only [List.range_zero, List.all_nil]
  | n + 1, h => by
      simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil,
        Bool.and_eq_true, Bool.and_true]
      exact ⟨allRange_of n (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))),
        h n (Nat.lt_succ_self n)⟩

private theorem of_allRange {p : Nat → Bool} : ∀ n, (List.range n).all p = true → ∀ i < n, p i = true
  | 0, h, i, hi => by omega
  | n + 1, h, i, hi => by
      simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil,
        Bool.and_eq_true, Bool.and_true] at h
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · exact of_allRange n h.1 i hlt
      · subst i
        exact h.2

private theorem allAusstehend_of (tokens : List Zuruecknahme) (base pages : Nat)
    (h : ∀ token ∈ tokens, ∀ i < pages, ¬ token.contains (base + i)) :
    tokens.all (fun token => (List.range pages).all (fun i => decide (¬ token.contains (base + i)))) = true := by
  induction tokens with
  | nil => simp only [List.all_nil]
  | cons tok rest ih =>
      simp only [List.all_cons, Bool.and_eq_true]
      constructor
      · apply allRange_of pages
        intro i hi
        have hc := h tok (by simp only [List.mem_cons, eq_self, true_or]) i hi
        simp only [decide_eq_true_eq, hc, not_false_eq_true]
      · exact ih (fun t ht i hi => h t (by simp only [List.mem_cons, ht, or_true]) i hi)

private theorem of_allAusstehend (tokens : List Zuruecknahme) (base pages : Nat)
    (h : tokens.all (fun token => (List.range pages).all (fun i => decide (¬ token.contains (base + i)))) = true) :
    ∀ token ∈ tokens, ∀ i < pages, ¬ token.contains (base + i) := by
  induction tokens with
  | nil => intro t ht; cases ht
  | cons tok rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      intro t ht i hi
      rcases List.mem_cons.mp ht with rfl | ht
      · have hbi := of_allRange pages h.1 i hi
        simpa only [decide_eq_true_eq] using hbi
      · exact ih h.2 t ht i hi

private theorem range_find_add : ∀ pages base i, i < pages →
    (List.range pages).find? (fun j => base + j == base + i) = some i
  | 0, base, i, hi => by omega
  | n + 1, base, i, hi => by
      rw [List.range_succ, List.find?_append]
      by_cases hin : i < n
      · have hprev := range_find_add n base i hin
        rw [hprev]
        simp only [Option.some_or]
      · have hei : i = n := by omega
        subst i
        have hnone : (List.range n).find? (fun j => base + j == base + n) = none := by
          rw [List.find?_eq_none]
          intro j hj hp
          have hlt : j < n := List.mem_range.mp hj
          have hne : base + j ≠ base + n := by omega
          exact hne (by simpa only [beq_iff_eq] using hp)
        rw [hnone]
        simp only [Option.none_or, List.find?_singleton, beq_self_eq_true, ↓reduceIte]

private theorem find_new_entry (pages base i : Nat) (hi : i < pages)
    (rights : List Speicherdienst) (gen von granule : Nat) :
    ((List.range pages).map (fun j => (base + j,
      (⟨von / granule + j, rights, gen⟩ : Seiteneintrag)))).find? (fun e => e.1 == base + i)
      = some (base + i, (⟨von / granule + i, rights, gen⟩ : Seiteneintrag)) := by
  rw [List.find?_map]
  change (List.find? (fun j => base + j == base + i) (List.range pages)).map
      (fun j => (base + j, (⟨von / granule + j, rights, gen⟩ : Seiteneintrag))) =
    some (base + i, (⟨von / granule + i, rights, gen⟩ : Seiteneintrag))
  rw [range_find_add pages base i hi]
  simp only [Option.map_some]

private theorem abbildung_append_new {space : Adressraum} {entries : List (Nat × Seiteneintrag)}
    {pg : Nat} {entry : Seiteneintrag}
    (hold : space.abbildung pg = none)
    (hnew : (entries.find? (fun e => e.1 == pg)) = some (pg, entry)) :
    ({ space with entries := space.entries ++ entries } : Adressraum).abbildung pg = some entry := by
  unfold Adressraum.abbildung
  have hold' : space.entries.find? (fun e => e.1 == pg) = none := by
    unfold Adressraum.abbildung at hold
    cases hfind : space.entries.find? (fun e => e.1 == pg) with
    | none => rfl
    | some e =>
        simp only [hfind, Option.map_some] at hold
        cases hold
  simp only [List.find?_append, hold', hnew, Option.none_or, Option.map_some]

private theorem abbildung_append_old {space : Adressraum} {entries : List (Nat × Seiteneintrag)}
    {pg : Nat} (hno : entries.find? (fun e => e.1 == pg) = none) :
    ({ space with entries := space.entries ++ entries } : Adressraum).abbildung pg = space.abbildung pg := by
  unfold Adressraum.abbildung
  rw [List.find?_append, hno]
  cases hfind : space.entries.find? (fun entry => entry.1 == pg) with
  | none => rfl
  | some e => rfl

private theorem doSomeSomeMem {A B C : Type} (a : A) (b : B) (body : A → B → Option C) :
    (do let x ← (some a : Option A); let y ← (some b : Option B); body x y) = body a b := rfl

private theorem set_self_mem {A : Type} (l : List A) (i : Nat) (a b : A) (h : l[i]? = some a) :
    (l.set i b)[i]? = some b := by
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.1 h
  exact List.getElem?_set_self hlen

theorem mapMeaning : MapMeaningAussage := by
  intro target s c sp virt slot rights space region hspace hregion
  let granule := target.seitengranule
  let base := virt / granule
  let pages := (region.extent.bis - region.extent.von) / granule
  let frame := s.lokal c
  constructor
  · intro hcond
    rcases hcond with ⟨hrights, hseiten, hvalid, habb, htoken⟩
    let entries := (List.range pages).map (fun i => (base + i,
      (⟨region.extent.von / granule + i, rights, space.generation⟩ : Seiteneintrag)))
    let mapped : Adressraum := { space with entries := space.entries ++ entries }
    let next : MemFrame :=
      { frame with
        result := some MemResult.mapped
        spaces := frame.spaces.set sp mapped }
    refine ⟨next, mapped, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold MemInstruction.evaluate
      simp only [hspace, hregion]
      rw [doSomeSomeMem]
      have hallAbb : (List.range pages).all (fun i => (space.abbildung (base + i)).isNone) = true := by
        apply allRange_of pages
        intro i hi
        rw [habb i hi]
        rfl
      have hallTok : space.ausstehend.all (fun token =>
          (List.range pages).all (fun i => decide (¬ token.contains (base + i)))) = true :=
        allAusstehend_of space.ausstehend base pages htoken
      have hc : rights ≠ [] ∧ Strecke.seiten target region.extent ∧
          validVirtualRange target virt ((region.extent.bis - region.extent.von) / target.seitengranule) = true ∧
          ((List.range ((region.extent.bis - region.extent.von) / target.seitengranule)).all fun i =>
            (space.abbildung (virt / target.seitengranule + i)).isNone) = true ∧
          space.ausstehend.all (fun token =>
            (List.range ((region.extent.bis - region.extent.von) / target.seitengranule)).all fun i =>
              decide (¬ token.contains (virt / target.seitengranule + i))) = true :=
        ⟨hrights, hseiten, hvalid, hallAbb, hallTok⟩
      rw [if_pos hc]
      rfl
    · change (frame.spaces.set sp mapped)[sp]? = some mapped
      exact set_self_mem frame.spaces sp space mapped hspace
    · rfl
    · rfl
    · intro i hi
      unfold mapped entries
      apply abbildung_append_new (habb i hi)
      exact find_new_entry pages base i hi rights space.generation region.extent.von granule
    · intro pg hpg
      unfold mapped entries
      apply abbildung_append_old
      rw [List.find?_eq_none]
      intro e he heq
      rcases List.mem_map.mp he with ⟨j, hj, rfl⟩
      have hlt : j < pages := List.mem_range.mp hj
      have hji : base + j = pg := by simpa only [beq_iff_eq] using heq
      subst pg
      exact hpg ⟨Nat.le_add_right base j, Nat.add_lt_add_left hlt base⟩
  · intro hex
    unfold MemInstruction.evaluate
    simp only [hspace, hregion]
    rw [doSomeSomeMem]
    rw [if_neg]
    intro hc
    rcases hc with ⟨_, _, _, _, hallTok⟩
    have hno := of_allAusstehend space.ausstehend base pages hallTok
    obtain ⟨token, htmem, i, hi, hcont⟩ := hex
    exact hno token htmem i hi hcont

end Gabbro.Core.Ast.LowLevel
