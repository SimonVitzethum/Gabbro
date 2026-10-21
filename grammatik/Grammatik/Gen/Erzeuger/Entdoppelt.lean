/-
  File:      Grammatik/Gen/Erzeuger/Entdoppelt.lean
  Subject:   ONE ITEM PER KEY, scanning buckets of growing size: `entdoppelt key aus B` keeps, bucket after bucket, the
             first item of every key not seen before and drops the items `aus` names. Completeness
             (`entdoppelt_vollst`): an item of bucket `j` that is not dropped has a representative with the same key in a
             bucket `≤ j`. The generator's body tables (`Spez.tabellenD`) are this function on the full tables.
-/
namespace Gabbro.Grammatik.Gen

variable {α κ : Type} [DecidableEq κ] (key : α → κ) (aus : α → Bool)

/-- One bucket: keep the items whose key is new and that are not dropped. -/
def entdoppeltEimer (a : List α × List κ) (bucket : List α) : List α × List κ :=
  bucket.foldl (fun (a : List α × List κ) b => if a.2.contains (key b) || aus b then a else (a.1 ++ [b], a.2 ++ [key b])) a

/-- **One item per key**, bucket after bucket. -/
def entdoppelt (B : List (List α)) : List (List α) :=
  (B.foldl (fun (acc : List (List α) × List κ) bucket =>
    let r := entdoppeltEimer key aus ([], acc.2) bucket
    (acc.1 ++ [r.1], r.2)) ([], [])).1

theorem eimer_spec (bucket : List α) (a : List α × List κ) :
    let r := entdoppeltEimer key aus a bucket
    (∃ neu, r.1 = a.1 ++ neu) ∧ (∀ x ∈ a.2, x ∈ r.2) ∧ (∀ x ∈ r.2, x ∈ a.2 ∨ ∃ b ∈ r.1, key b = x) ∧
      (∀ b ∈ bucket, aus b = false → key b ∈ r.2) := by
  induction bucket generalizing a with
  | nil => exact ⟨⟨[], by simp [entdoppeltEimer]⟩, fun x hx => hx, fun x hx => Or.inl hx, fun b hb => by cases hb⟩
  | cons b rest ih =>
    simp only [entdoppeltEimer, List.foldl_cons] at ih ⊢
    split
    · rename_i hc
      obtain ⟨⟨neu, hn⟩, h2, h3, h4⟩ := ih a
      refine ⟨⟨neu, hn⟩, h2, h3, fun b' hb' ha => ?_⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · rcases Bool.or_eq_true_iff.1 hc with hc | hc
        · exact h2 _ (List.contains_iff_mem.1 hc)
        · rw [hc] at ha; cases ha
      · exact h4 b' hb' ha
    · obtain ⟨⟨neu, hn⟩, h2, h3, h4⟩ := ih (a.1 ++ [b], a.2 ++ [key b])
      refine ⟨⟨[b] ++ neu, by rw [hn, List.append_assoc]⟩, fun x hx => h2 x (List.mem_append_left _ hx), ?_, ?_⟩
      · intro x hx
        rcases h3 x hx with hx | ⟨b', hb', hk⟩
        · rcases List.mem_append.1 hx with hx | hx
          · exact Or.inl hx
          · right; exact ⟨b, by rw [hn]; simp, (List.mem_singleton.1 hx).symm⟩
        · exact Or.inr ⟨b', hb', hk⟩
      · intro b' hb' ha
        rcases List.mem_cons.1 hb' with rfl | hb'
        · exact h2 _ (by simp)
        · exact h4 b' hb' ha

/-- A kept item was kept before or is an item of the bucket that is not dropped. -/
theorem eimer_teil (bucket : List α) (a : List α × List κ) :
    ∀ b ∈ (entdoppeltEimer key aus a bucket).1, b ∈ a.1 ∨ (b ∈ bucket ∧ aus b = false) := by
  induction bucket generalizing a with
  | nil => intro b hb; exact Or.inl hb
  | cons x rest ih =>
    intro b hb
    simp only [entdoppeltEimer, List.foldl_cons] at hb
    split at hb
    · rcases ih a b hb with h | ⟨h, h'⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ h, h'⟩
    · rename_i hc
      rcases ih (a.1 ++ [x], a.2 ++ [key x]) b hb with h | ⟨h, h'⟩
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.1 h]
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
          exact Or.inr ⟨List.mem_cons_self .., hc.2⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h, h'⟩

/-- The outer fold, from any state whose seen keys all have a representative. -/
theorem aussen_spec (B : List (List α)) (acc : List (List α)) (seen : List κ)
    (hI : ∀ x ∈ seen, ∃ k < acc.length, ∃ b ∈ acc.getD k [], key b = x) :
    let r := B.foldl (fun (acc : List (List α) × List κ) bucket =>
      let r := entdoppeltEimer key aus ([], acc.2) bucket
      (acc.1 ++ [r.1], r.2)) (acc, seen)
    (∃ rest, r.1 = acc ++ rest ∧ rest.length = B.length) ∧
      ∀ j < B.length, ∀ e ∈ B.getD j [], aus e = false →
        ∃ k ≤ acc.length + j, ∃ b ∈ r.1.getD k [], key b = key e := by
  induction B generalizing acc seen with
  | nil => exact ⟨⟨[], by simp, rfl⟩, fun j hj => by simp at hj⟩
  | cons bucket B ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨⟨neu, hn⟩, _, h3, h4⟩ := eimer_spec key aus bucket ([], seen)
    simp only [List.nil_append] at hn
    generalize entdoppeltEimer key aus ([], seen) bucket = r0 at hn h3 h4 ⊢
    have hI' : ∀ x ∈ r0.2, ∃ k < (acc ++ [r0.1]).length, ∃ b ∈ (acc ++ [r0.1]).getD k [], key b = x := by
      intro x hx
      rcases h3 x hx with hx | ⟨b, hb, hk⟩
      · obtain ⟨k, hk, b, hb, hkb⟩ := hI x hx
        refine ⟨k, by simp; omega, b, ?_, hkb⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
        exact hb
      · refine ⟨acc.length, by simp, b, ?_, hk⟩
        simp [List.getD_eq_getElem?_getD, hb]
    obtain ⟨⟨rest, hrest, hlen⟩, hj⟩ := ih (acc ++ [r0.1]) r0.2 hI'
    refine ⟨⟨[r0.1] ++ rest, by rw [hrest, List.append_assoc], by simp [hlen]⟩, ?_⟩
    intro j hjl e he ha
    match j, hjl, he with
    | 0, _, he =>
      obtain ⟨k, hk, b, hb, hkb⟩ := hI' (key e) (h4 e (by simpa using he) ha)
      refine ⟨k, by simp at hk; omega, b, ?_, hkb⟩
      rw [hrest, List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
      exact hb
    | j + 1, hjl, he =>
      obtain ⟨k, hk, b, hb, hkb⟩ := hj j (by simp at hjl; omega) e (by simpa using he) ha
      exact ⟨k, by simp at hk; omega, b, hb, hkb⟩

/-- **Completeness of the de-duplication**: an item of bucket `j` that is not dropped has a representative with the
    same key in a bucket at most `j`. -/
theorem entdoppelt_vollst (B : List (List α)) (j : Nat) (hj : j < B.length) (e : α) (he : e ∈ B.getD j [])
    (ha : aus e = false) : ∃ k ≤ j, ∃ b ∈ (entdoppelt key aus B).getD k [], key b = key e := by
  have := (aussen_spec key aus B [] [] (fun x hx => by cases hx)).2 j hj e he ha
  simpa [entdoppelt] using this

end Gabbro.Grammatik.Gen
