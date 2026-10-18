/-
  File:      Grammatik/ArenaAuf.lean
  Subject:   WHO IS ON THE CHAIN AFTER A MOVE (PLAN-DYNAMISCH.md section 8a.1, step (3), abstract half).

  `ArenaKette.lean` proves that `push`, `pop` and `unlink` keep a chain well formed. A body that runs SEVERAL moves
  needs more: what it knew about the OTHER slots before a move must still hold after it. Three facts, each for one
  move, over the abstract link function:

    * `auf_push_vor/nach`  -- after linking `i` in at the head, the members are exactly `i` and the old members;
    * `auf_pop_vor`        -- after taking the head off, every member was a member before;
    * `auf_unlink_vor`     -- after cutting the successor of `p` out, every member was a member before.

  Consequence (used by the recognizer): a slot that was not linked stays not linked through pop and unlink and through
  a push of ANOTHER slot; a member stays a member through push.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaKette

namespace Gabbro.Grammatik.ArenaKette

/-- After `push i`: every member of the new chain is `i` or was a member. -/
theorem auf_push_vor {c : Int} {nx nx' : Int → Int} {kopf kopf' i : Int}
    (hchain : ∃ L, KetteF c nx kopf L) (h0 : 0 ≤ i) (hi : i < c) (hnot : ¬ Auf c nx kopf i)
    (hk' : kopf' = i) (hn' : nx' i = kopf) (ho : ∀ j, j ≠ i → nx' j = nx j) :
    ∀ j, Auf c nx' kopf' j → j = i ∨ Auf c nx kopf j := by
  obtain ⟨L, hk⟩ := hchain
  have hiL : i ∉ L := fun hm => hnot ⟨L, hk, hm⟩
  have hch : KetteF c nx' kopf' (i :: L) := by
    rw [hk']
    refine KetteF.cons i h0 hi L ?_
    rw [hn']
    exact hk.uebertragen (fun j hj => ho j (fun e => hiL (e ▸ hj)))
  rintro j ⟨L', hL', hm⟩
  have := KetteF.eindeutig hL' hch
  subst this
  rcases List.mem_cons.mp hm with e | e
  · exact Or.inl e
  · exact Or.inr ⟨L, hk, e⟩

/-- After `push i`: every old member is still a member. -/
theorem auf_push_nach {c : Int} {nx nx' : Int → Int} {kopf kopf' i : Int}
    (hchain : ∃ L, KetteF c nx kopf L) (h0 : 0 ≤ i) (hi : i < c) (hnot : ¬ Auf c nx kopf i)
    (hk' : kopf' = i) (hn' : nx' i = kopf) (ho : ∀ j, j ≠ i → nx' j = nx j) :
    ∀ j, Auf c nx kopf j → Auf c nx' kopf' j := by
  obtain ⟨L, hk⟩ := hchain
  have hiL : i ∉ L := fun hm => hnot ⟨L, hk, hm⟩
  have hch : KetteF c nx' kopf' (i :: L) := by
    rw [hk']
    refine KetteF.cons i h0 hi L ?_
    rw [hn']
    exact hk.uebertragen (fun j hj => ho j (fun e => hiL (e ▸ hj)))
  rintro j ⟨L', hL', hm⟩
  have := KetteF.eindeutig hL' hk
  subst this
  exact ⟨i :: L', hch, List.mem_cons_of_mem _ hm⟩

/-- After `pop`: every member of the new chain was a member before. -/
theorem auf_pop_vor {c : Int} {nx nx' : Int → Int} {kopf kopf' : Int}
    (hchain : ∃ L, KetteF c nx kopf L) (hne : kopf < c)
    (hk' : kopf' = nx kopf) (ho : ∀ j, nx' j = nx j) :
    ∀ j, Auf c nx' kopf' j → Auf c nx kopf j := by
  obtain ⟨L, hk⟩ := hchain
  generalize hg : kopf = kk at hk hne hk'
  cases hk with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk1 L1 h1 =>
    have hch : KetteF c nx' kopf' L1 := by
      rw [hk']; exact h1.uebertragen (fun j _ => ho j)
    rintro j ⟨L', hL', hm⟩
    have := KetteF.eindeutig hL' hch
    subst this
    subst hg
    exact ⟨_ :: L', KetteF.cons _ h0 hk1 L' h1, List.mem_cons_of_mem _ hm⟩

/-- After `unlink` (the successor `i` of a member `p` is cut out): every member of the new chain was a member before. -/
theorem auf_unlink_vor {c : Int} {nx nx' : Int → Int} {kopf p i : Int} {Live : Int → Prop}
    (h : ListOkF c nx kopf Live) (hp : Auf c nx kopf p) (hpi : nx p = i) (hi : i < c)
    (hnp : nx' p = nx i) (ho : ∀ j, j ≠ p → nx' j = nx j) :
    ∀ j, Auf c nx' kopf j → Auf c nx kopf j := by
  obtain ⟨L, hk, hnd, hv⟩ := h
  obtain ⟨L0, hk0, hm⟩ := hp
  have hLL : L0 = L := KetteF.eindeutig hk0 hk
  subst hLL
  obtain ⟨L', hk', hperm⟩ := unlink_aux hi hpi hnp ho hk hnd hm
  rintro j ⟨L2, hL2, hm2⟩
  have := KetteF.eindeutig hL2 hk'
  subst this
  exact ⟨L0, hk0, hperm.symm.subset (List.mem_cons_of_mem _ hm2)⟩

end Gabbro.Grammatik.ArenaKette

#print axioms Gabbro.Grammatik.ArenaKette.auf_push_vor
#print axioms Gabbro.Grammatik.ArenaKette.auf_push_nach
#print axioms Gabbro.Grammatik.ArenaKette.auf_pop_vor
#print axioms Gabbro.Grammatik.ArenaKette.auf_unlink_vor
