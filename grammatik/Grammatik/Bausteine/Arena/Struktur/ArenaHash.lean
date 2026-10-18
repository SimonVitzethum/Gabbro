/-
  File:      Grammatik/ArenaHash.lean
  Subject:   HASH CHAINS (PLAN-DYNAMISCH.md section 8a.1, step (4)), abstractly, over the chains of `ArenaKette.lean`.

  A hash table with chaining is an array of list heads `hd : bucket -> slot` over ONE arena table (one link function `nx`).
  The invariant:

    `HashOkF c nx hd nb Live`  --  every bucket `b < nb` is a well formed list over live slots (`ListOkF`), and no slot is
                                   on two buckets (the chains are pairwise disjoint).

  The moves, each on ONE bucket `b0`, keep it (`hash_push`, `hash_pop`, `hash_unlink`); the hypothesis that makes the
  disjointness survive a push is that the slot is on NO bucket (`N586`: a pushed slot is owned). Without it the chains
  overlap (`hash_defekt_bricht`: a slot pushed into a second bucket while it heads another).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaAuf

namespace Gabbro.Grammatik.ArenaKette

/-- **The invariant of a hash table with chaining:** each of the `nb` buckets is a list of live slots, and the chains are
    pairwise disjoint. -/
def HashOkF (c : Int) (nx : Int → Int) (hd : Int → Int) (nb : Int) (Live : Int → Prop) : Prop :=
  (∀ b, 0 ≤ b → b < nb → ListOkF c nx (hd b) Live) ∧
  (∀ b b', 0 ≤ b → b < nb → 0 ≤ b' → b' < nb → b ≠ b' →
    ∀ j, Auf c nx (hd b) j → ¬ Auf c nx (hd b') j)

/-- A link function that agrees on the members of a chain keeps its members. -/
theorem auf_ho {c : Int} {nx nx' : Int → Int} {k : Int} (h : ∃ L, KetteF c nx k L)
    (g : ∀ j, Auf c nx k j → nx' j = nx j) : ∀ j, Auf c nx' k j ↔ Auf c nx k j := by
  obtain ⟨L, hk⟩ := h
  have hk' : KetteF c nx' k L := hk.uebertragen (fun j hj => g j ⟨L, hk, hj⟩)
  intro j
  constructor
  · rintro ⟨L2, hL2, hm⟩
    have := KetteF.eindeutig hL2 hk'
    subst this
    exact ⟨_, hk, hm⟩
  · rintro ⟨L2, hL2, hm⟩
    have := KetteF.eindeutig hL2 hk
    subst this
    exact ⟨_, hk', hm⟩

/-- **Push into one bucket:** the slot `i` is live and on NO bucket; it becomes the head of bucket `b0`. -/
theorem hash_push {c : Int} {nx nx' hd hd' : Int → Int} {nb b0 i : Int} {Live Live' : Int → Prop}
    (h : HashOkF c nx hd nb Live) (hb0 : 0 ≤ b0 ∧ b0 < nb) (h0 : 0 ≤ i) (hi : i < c) (hlive : Live' i)
    (hl : ∀ j, Live j → Live' j) (hnot : ∀ b, 0 ≤ b → b < nb → ¬ Auf c nx (hd b) i)
    (hhd : ∀ b, b ≠ b0 → hd' b = hd b) (hhd0 : hd' b0 = i) (hn' : nx' i = hd b0)
    (ho : ∀ j, j ≠ i → nx' j = nx j) : HashOkF c nx' hd' nb Live' := by
  obtain ⟨h1, h2⟩ := h
  have hchain : ∀ b, 0 ≤ b → b < nb → ∃ L, KetteF c nx (hd b) L := fun b hb0' hb1 => by
    obtain ⟨L, hk, -, -⟩ := h1 b hb0' hb1; exact ⟨L, hk⟩
  have hg : ∀ b, 0 ≤ b → b < nb → ∀ j, Auf c nx (hd b) j → nx' j = nx j :=
    fun b hb0' hb1 j hj => ho j (fun e => hnot b hb0' hb1 (e ▸ hj))
  have hmem : ∀ b, 0 ≤ b → b < nb → ∀ j,
      Auf c nx' (hd' b) j ↔ ((b = b0 ∧ j = i) ∨ Auf c nx (hd b) j) := by
    intro b hb0' hb1 j
    by_cases hbb : b = b0
    · subst hbb
      constructor
      · intro hj
        rcases auf_push_vor (hchain b hb0' hb1) h0 hi (hnot b hb0' hb1) hhd0 hn' ho j hj with e | e
        · exact Or.inl ⟨rfl, e⟩
        · exact Or.inr e
      · rintro (⟨-, e⟩ | e)
        · subst e
          exact auf_push_kopf (hchain b hb0' hb1) h0 hi (hnot b hb0' hb1) hhd0 hn' ho
        · exact auf_push_nach (hchain b hb0' hb1) h0 hi (hnot b hb0' hb1) hhd0 hn' ho j e
    · rw [hhd b hbb]
      constructor
      · intro hj; exact Or.inr ((auf_ho (hchain b hb0' hb1) (hg b hb0' hb1) j).mp hj)
      · rintro (⟨e, -⟩ | e)
        · exact absurd e hbb
        · exact (auf_ho (hchain b hb0' hb1) (hg b hb0' hb1) j).mpr e
  refine ⟨fun b hb0' hb1 => ?_, fun b b' hb0' hb1 hb0'' hb1' hne j hj hj' => ?_⟩
  · by_cases hbb : b = b0
    · subst hbb
      exact push_ok (h1 b hb0' hb1) h0 hi hlive hl (hnot b hb0' hb1) hhd0 hn' ho
    · rw [hhd b hbb]
      exact (h1 b hb0' hb1).rahmen (fun j hj => hl j ((h1 b hb0' hb1).lebt_auf hj))
        (fun j hj => hg b hb0' hb1 j hj)
  · rw [hmem b hb0' hb1] at hj
    rw [hmem b' hb0'' hb1'] at hj'
    rcases hj with ⟨hbb, hji⟩ | hj
    · subst hji
      rcases hj' with ⟨hb'b, -⟩ | hj'
      · exact hne (hbb.trans hb'b.symm)
      · exact hnot b' hb0'' hb1' hj'
    · rcases hj' with ⟨-, hji⟩ | hj'
      · subst hji
        exact hnot b hb0' hb1 hj
      · exact h2 b b' hb0' hb1 hb0'' hb1' hne j hj hj'

/-- **Pop from one bucket:** the head of bucket `b0` is taken off. -/
theorem hash_pop {c : Int} {nx nx' hd hd' : Int → Int} {nb b0 : Int} {Live Live' : Int → Prop}
    (h : HashOkF c nx hd nb Live) (hb0 : 0 ≤ b0 ∧ b0 < nb) (hne : hd b0 < c) (hl : ∀ j, Live j → Live' j)
    (hhd : ∀ b, b ≠ b0 → hd' b = hd b) (hhd0 : hd' b0 = nx (hd b0)) (ho : ∀ j, nx' j = nx j) :
    HashOkF c nx' hd' nb Live' := by
  have hnx : nx' = nx := funext ho
  subst hnx
  obtain ⟨h1, h2⟩ := h
  have hsub : ∀ b, 0 ≤ b → b < nb → ∀ j, Auf c nx' (hd' b) j → Auf c nx' (hd b) j := by
    intro b hb0' hb1 j hj
    by_cases hbb : b = b0
    · subst hbb
      exact auf_pop_vor (by obtain ⟨L, hk, -, -⟩ := h1 b hb0' hb1; exact ⟨L, hk⟩) hne hhd0 (fun _ => rfl) j hj
    · rw [hhd b hbb] at hj; exact hj
  refine ⟨fun b hb0' hb1 => ?_, fun b b' hb0' hb1 hb0'' hb1' hne' j hj hj' => ?_⟩
  · by_cases hbb : b = b0
    · subst hbb
      exact (pop_ok (h1 b hb0' hb1) hne hl hhd0 (fun _ => rfl)).1
    · rw [hhd b hbb]
      exact (h1 b hb0' hb1).rahmen (fun j hj => hl j ((h1 b hb0' hb1).lebt_auf hj)) (fun _ _ => rfl)
  · exact h2 b b' hb0' hb1 hb0'' hb1' hne' j (hsub b hb0' hb1 j hj) (hsub b' hb0'' hb1' j hj')

/-- **Unlink inside one bucket:** the successor `i` of a member `p` of bucket `b0` is cut out. -/
theorem hash_unlink {c : Int} {nx nx' hd : Int → Int} {nb b0 p i : Int} {Live Live' : Int → Prop}
    (h : HashOkF c nx hd nb Live) (hb0 : 0 ≤ b0 ∧ b0 < nb) (hp : Auf c nx (hd b0) p) (hpi : nx p = i)
    (hi : i < c) (hl : ∀ j, Live j → Live' j) (hnp : nx' p = nx i) (ho : ∀ j, j ≠ p → nx' j = nx j) :
    HashOkF c nx' hd nb Live' := by
  obtain ⟨h1, h2⟩ := h
  have hchain : ∀ b, 0 ≤ b → b < nb → ∃ L, KetteF c nx (hd b) L := fun b hb0' hb1 => by
    obtain ⟨L, hk, -, -⟩ := h1 b hb0' hb1; exact ⟨L, hk⟩
  have hg : ∀ b, 0 ≤ b → b < nb → b ≠ b0 → ∀ j, Auf c nx (hd b) j → nx' j = nx j :=
    fun b hb0' hb1 hbb j hj => ho j (fun e => h2 b0 b hb0.1 hb0.2 hb0' hb1 (Ne.symm hbb) p hp (e ▸ hj))
  have hsub : ∀ b, 0 ≤ b → b < nb → ∀ j, Auf c nx' (hd b) j → Auf c nx (hd b) j := by
    intro b hb0' hb1 j hj
    by_cases hbb : b = b0
    · subst hbb
      exact auf_unlink_vor (h1 b hb0' hb1) hp hpi hi hnp ho j hj
    · exact (auf_ho (hchain b hb0' hb1) (hg b hb0' hb1 hbb) j).mp hj
  refine ⟨fun b hb0' hb1 => ?_, fun b b' hb0' hb1 hb0'' hb1' hne' j hj hj' => ?_⟩
  · by_cases hbb : b = b0
    · subst hbb
      exact (unlink_ok (h1 b hb0' hb1) hp hpi hi hl hnp ho).1
    · exact (h1 b hb0' hb1).rahmen (fun j hj => hl j ((h1 b hb0' hb1).lebt_auf hj))
        (fun j hj => hg b hb0' hb1 hbb j hj)
  · exact h2 b b' hb0' hb1 hb0'' hb1' hne' j (hsub b hb0' hb1 j hj) (hsub b' hb0'' hb1' j hj')

/-! ## The witness and the planted defect (concrete numbers: four slots, nil marker `4`, two buckets) -/

section Zeuge

/-- Bucket `0` holds `2 -> 0`, bucket `1` holds `1`; slot `3` is free. -/
def nxH : Int → Int := fun k => if k = 2 then 0 else 4
def hdH : Int → Int := fun b => if b = 0 then 2 else 1

theorem kette_b0 : KetteF 4 nxH 2 [2, 0] := by
  refine KetteF.cons 2 (by decide) (by decide) [0] ?_
  have : nxH 2 = 0 := by unfold nxH; decide
  rw [this]
  refine KetteF.cons 0 (by decide) (by decide) [] ?_
  have : nxH 0 = 4 := by unfold nxH; decide
  rw [this]; exact KetteF.nil

theorem kette_b1 : KetteF 4 nxH 1 [1] := by
  refine KetteF.cons 1 (by decide) (by decide) [] ?_
  have : nxH 1 = 4 := by unfold nxH; decide
  rw [this]; exact KetteF.nil

theorem hashOk0 : HashOkF 4 nxH hdH 2 (fun j => 0 ≤ j ∧ j < 4) := by
  refine ⟨fun b hb0 hb1 => ?_, fun b b' hb0 hb1 hb0' hb1' hne j hj hj' => ?_⟩
  · have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · refine ⟨[2, 0], ?_, by decide, ?_⟩
      · have : hdH 0 = 2 := by unfold hdH; decide
        rw [this]; exact kette_b0
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide
    · refine ⟨[1], ?_, by decide, ?_⟩
      · have : hdH 1 = 1 := by unfold hdH; decide
        rw [this]; exact kette_b1
      · intro i hi; simp at hi; subst hi; decide
  · have hb : b = 0 ∨ b = 1 := by omega
    have hb' : b' = 0 ∨ b' = 1 := by omega
    obtain ⟨L, hL, hm⟩ := hj
    obtain ⟨L', hL', hm'⟩ := hj'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact hne rfl
    · have e1 : hdH 0 = 2 := by unfold hdH; decide
      have e2 : hdH 1 = 1 := by unfold hdH; decide
      rw [e1] at hL; rw [e2] at hL'
      have := KetteF.eindeutig hL kette_b0; subst this
      have := KetteF.eindeutig hL' kette_b1; subst this
      simp at hm hm'
      rcases hm with rfl | rfl <;> omega
    · have e1 : hdH 0 = 2 := by unfold hdH; decide
      have e2 : hdH 1 = 1 := by unfold hdH; decide
      rw [e1] at hL'; rw [e2] at hL
      have := KetteF.eindeutig hL' kette_b0; subst this
      have := KetteF.eindeutig hL kette_b1; subst this
      simp at hm hm'
      rcases hm' with rfl | rfl <;> omega
    · exact hne rfl

/-- After `3` is pushed into bucket `1`: `hd 1 = 3`, `nx 3 = 1`. -/
def hdH1 : Int → Int := fun b => if b = 1 then 3 else hdH b
def nxH1 : Int → Int := fun k => if k = 3 then 1 else nxH k

/-- **The witness:** the free slot `3` is pushed into bucket `1`; the table stays a hash table with two chains, and
    bucket `1` now holds `3 -> 1`. -/
theorem hash_push_zeuge : HashOkF 4 nxH1 hdH1 2 (fun j => 0 ≤ j ∧ j < 4) ∧ Auf 4 nxH1 (hdH1 1) 1 := by
  have hnot : ∀ b, 0 ≤ b → b < 2 → ¬ Auf 4 nxH (hdH b) 3 := by
    intro b hb0 hb1 ⟨L, hL, hm⟩
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · have e : hdH 0 = 2 := by unfold hdH; decide
      rw [e] at hL
      have := KetteF.eindeutig hL kette_b0; subst this; simp at hm
    · have e : hdH 1 = 1 := by unfold hdH; decide
      rw [e] at hL
      have := KetteF.eindeutig hL kette_b1; subst this; simp at hm
  refine ⟨hash_push hashOk0 (b0 := 1) (i := 3) ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (fun j hj => hj) hnot (fun b hb => by unfold hdH1; simp [hb]) (by unfold hdH1; decide)
    (by unfold nxH1 hdH; decide) (fun j hj => by unfold nxH1; simp [hj]), ?_⟩
  have e : hdH1 1 = 3 := by unfold hdH1; simp
  rw [e]
  refine ⟨[3, 1], ?_, by simp⟩
  refine KetteF.cons 3 (by decide) (by decide) [1] ?_
  have : nxH1 3 = 1 := by unfold nxH1; decide
  rw [this]
  refine KetteF.cons 1 (by decide) (by decide) [] ?_
  have : nxH1 1 = 4 := by unfold nxH1 nxH; decide
  rw [this]; exact KetteF.nil

/-- The planted defect: slot `2`, the head of bucket `0`, is pushed into bucket `1` as well. -/
def hdH2 : Int → Int := fun _ => 2
def nxH2 : Int → Int := fun k => if k = 2 then 1 else nxH k

/-- **The model rejects a slot on two buckets:** after `2` (still the head of bucket `0`) is also pushed into bucket `1`,
    both chains contain `2`, so the chains are not disjoint. -/
theorem hash_defekt_bricht : ¬ HashOkF 4 nxH2 hdH2 2 (fun j => 0 ≤ j ∧ j < 4) := by
  intro h
  have hchain : KetteF 4 nxH2 2 [2, 1] := by
    refine KetteF.cons 2 (by decide) (by decide) [1] ?_
    have : nxH2 2 = 1 := by unfold nxH2; decide
    rw [this]
    refine KetteF.cons 1 (by decide) (by decide) [] ?_
    have : nxH2 1 = 4 := by unfold nxH2 nxH; decide
    rw [this]; exact KetteF.nil
  have e0 : hdH2 0 = 2 := rfl
  have e1 : hdH2 1 = 2 := rfl
  exact h.2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) 2
    (by rw [e0]; exact ⟨[2, 1], hchain, by simp⟩) (by rw [e1]; exact ⟨[2, 1], hchain, by simp⟩)

end Zeuge

end Gabbro.Grammatik.ArenaKette

#print axioms Gabbro.Grammatik.ArenaKette.hash_push
#print axioms Gabbro.Grammatik.ArenaKette.hash_pop
#print axioms Gabbro.Grammatik.ArenaKette.hash_unlink
#print axioms Gabbro.Grammatik.ArenaKette.hashOk0
#print axioms Gabbro.Grammatik.ArenaKette.hash_push_zeuge
#print axioms Gabbro.Grammatik.ArenaKette.hash_defekt_bricht
