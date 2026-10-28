/-
  File:      Grammatik/ArenaKette.lean
  Subject:   LINKED LISTS OVER INDICES, abstractly: the chain as an inductive predicate over the link
             function, with the mutations that matter (link in, unlink the head, unlink after a
             predecessor) proved to keep it well formed (PLAN-DYNAMIC.md section 8a, phase 2,
             abstract half; the binary tree is `ArenaBaum.lean`).

  A link is an INDEX into one arena table; the value `c` (the table's `count`) is the nil marker. A
  structure is described by its link functions `nx : Int → Int` (list) or `l r : Int → Int` (tree).
  This file knows no world and no free list: `ArenaLebt.lean` instantiates the functions with the
  link fields of a world and supplies the notion of a LIVE slot (below the used counter, not on the
  free list).

    * `KetteF c nx k L`   -- following `nx` from `k` visits exactly `L` and ends at `c`. The chain is
      an inductive predicate, so it is FINITE by construction: a cycle has no such `L`.
    * `ListOkF`           -- a chain whose slots are pairwise distinct and live (acyclic, in range).

  The mutations, each with the hypothesis the checker establishes statically:
    * `push_ok`, `pop_ok`, `unlink_ok` (the third is deletion after a predecessor).
  The refusal is modelled by `push_doppelt_bricht`: pushing the head again makes a self loop, so no
  chain exists.
-/
import Mathlib.Data.List.Perm.Basic

namespace Gabbro.Grammatik.ArenaKette

/-! ## 1. The chain -/

/-- Following `nx` from `k` visits exactly `L` and ends at the nil marker `c`. -/
inductive KetteF (c : Int) (nx : Int → Int) : Int → List Int → Prop where
  | nil : KetteF c nx c []
  | cons (k : Int) (h0 : 0 ≤ k) (hk : k < c) (L : List Int)
      (h : KetteF c nx (nx k) L) : KetteF c nx k (k :: L)

theorem KetteF.eindeutig {c : Int} {nx : Int → Int} {k : Int} {L L' : List Int}
    (h : KetteF c nx k L) (h' : KetteF c nx k L') : L = L' := by
  induction h generalizing L' with
  | nil =>
    cases h' with
    | nil => rfl
    | cons _ _ hk _ _ => exact absurd hk (Int.lt_irrefl _)
  | cons k h0 hk L h ih =>
    cases h' with
    | nil => exact absurd hk (Int.lt_irrefl _)
    | cons _ _ _ L' h' => exact congrArg (k :: ·) (ih h')

theorem KetteF.mem_bereich {c : Int} {nx : Int → Int} {k : Int} {L : List Int}
    (h : KetteF c nx k L) : ∀ i ∈ L, 0 ≤ i ∧ i < c := by
  induction h with
  | nil => intro i hi; simp only [List.not_mem_nil] at hi
  | cons k h0 hk L h ih =>
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨h0, hk⟩
    · exact ih i hi

/-- A link function that agrees on the visited slots has the same chain. -/
theorem KetteF.uebertragen {c : Int} {nx nx' : Int → Int} {k : Int} {L : List Int}
    (h : KetteF c nx k L) (g : ∀ j ∈ L, nx' j = nx j) : KetteF c nx' k L := by
  induction h with
  | nil => exact KetteF.nil
  | cons k h0 hk L h ih =>
    refine KetteF.cons k h0 hk L ?_
    rw [g k (by simp only [List.mem_cons, true_or])]
    exact ih (fun j hj => g j (by simp only [List.mem_cons, hj, or_true]))

/-- `i` is a member of the chain from `kopf`. -/
def Auf (c : Int) (nx : Int → Int) (kopf i : Int) : Prop :=
  ∃ L, KetteF c nx kopf L ∧ i ∈ L

/-- **The invariant of a linked list over live slots:** the chain from the head exists (so it ends,
    so it has no cycle), its slots are pairwise distinct and every one is live. -/
def ListOkF (c : Int) (nx : Int → Int) (kopf : Int) (Live : Int → Prop) : Prop :=
  ∃ L, KetteF c nx kopf L ∧ L.Nodup ∧ ∀ i ∈ L, Live i

/-- The empty list is well formed. -/
theorem listOkF_leer (c : Int) (nx : Int → Int) (Live : Int → Prop) : ListOkF c nx c Live :=
  ⟨[], KetteF.nil, List.nodup_nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩

/-- A well formed chain survives a change of the link function away from its slots and a
    widening of the live set. -/
theorem ListOkF.rahmen {c : Int} {nx nx' : Int → Int} {kopf : Int} {Live Live' : Int → Prop}
    (h : ListOkF c nx kopf Live) (hl : ∀ j, Auf c nx kopf j → Live' j)
    (g : ∀ j, Auf c nx kopf j → nx' j = nx j) : ListOkF c nx' kopf Live' := by
  obtain ⟨L, hk, hnd, hv⟩ := h
  exact ⟨L, hk.uebertragen (fun j hj => g j ⟨L, hk, hj⟩), hnd, fun i hi => hl i ⟨L, hk, hi⟩⟩

/-- Every slot on a well formed chain is live. -/
theorem ListOkF.lebt_auf {c : Int} {nx : Int → Int} {kopf : Int} {Live : Int → Prop}
    (h : ListOkF c nx kopf Live) {j : Int} (hj : Auf c nx kopf j) : Live j := by
  obtain ⟨L, hk, _, hv⟩ := h
  obtain ⟨L', hL', hm⟩ := hj
  have := KetteF.eindeutig hL' hk
  subst this
  exact hv j hm

/-- The head of a non-empty chain is on it. -/
theorem auf_kopf {c : Int} {nx : Int → Int} {kopf : Int} (hne : kopf < c)
    (h : ∃ L, KetteF c nx kopf L) : Auf c nx kopf kopf := by
  obtain ⟨L, hk⟩ := h
  cases hk with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk L1 h1 => exact ⟨_, KetteF.cons _ h0 hk L1 h1, List.mem_cons_self⟩

/-- The successor of a member (when it is a slot) is a member. -/
theorem auf_nach {c : Int} {nx : Int → Int} {kopf p : Int} (hp : Auf c nx kopf p) (hn : nx p < c) :
    Auf c nx kopf (nx p) := by
  obtain ⟨L, hk, hm⟩ := hp
  refine ⟨L, hk, ?_⟩
  induction hk with
  | nil => simp only [List.not_mem_nil] at hm
  | cons k h0 hk L h ih =>
    by_cases hkp : k = p
    · subst hkp
      cases h with
      | nil => exact absurd hn (Int.lt_irrefl _)
      | cons k' h0' hk' L1 h1 => exact List.mem_cons_of_mem _ List.mem_cons_self
    · have : p ∈ L := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hkp
        · exact e
      exact List.mem_cons_of_mem _ (ih this)

/-- A slot with a property that no live slot has is not on a well formed chain. -/
theorem ListOkF.nicht_auf {c : Int} {nx : Int → Int} {kopf : Int} {Live : Int → Prop}
    (h : ListOkF c nx kopf Live) (P : Int → Prop) (hP : ∀ j, Live j → ¬ P j) {i : Int} (hi : P i) :
    ¬ Auf c nx kopf i := by
  obtain ⟨L, hk, _, hv⟩ := h
  rintro ⟨L', hL', hm⟩
  have := KetteF.eindeutig hL' hk
  subst this
  exact hP i (hv i hm) hi

/-- **Link in** (`push`): a live slot that is not on the chain becomes the head. -/
theorem push_ok {c : Int} {nx nx' : Int → Int} {kopf kopf' i : Int} {Live Live' : Int → Prop}
    (h : ListOkF c nx kopf Live) (h0 : 0 ≤ i) (hi : i < c) (hlive : Live' i)
    (hl : ∀ j, Live j → Live' j) (hnot : ¬ Auf c nx kopf i)
    (hk' : kopf' = i) (hn' : nx' i = kopf) (ho : ∀ j, j ≠ i → nx' j = nx j) :
    ListOkF c nx' kopf' Live' := by
  obtain ⟨L, hk, hnd, hv⟩ := h
  have hiL : i ∉ L := fun hm => hnot ⟨L, hk, hm⟩
  refine ⟨i :: L, ?_, List.nodup_cons.mpr ⟨hiL, hnd⟩, ?_⟩
  · rw [hk']
    refine KetteF.cons i h0 hi L ?_
    rw [hn']
    exact hk.uebertragen (fun j hj => ho j (fun e => hiL (e ▸ hj)))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hlive
    · exact hl j (hv j hj)

/-- **Unlink the head** (`pop`): the head becomes its link. The slot taken off is not on the new chain
    (it can now be released). -/
theorem pop_ok {c : Int} {nx nx' : Int → Int} {kopf kopf' : Int} {Live Live' : Int → Prop}
    (h : ListOkF c nx kopf Live) (hne : kopf < c) (hl : ∀ j, Live j → Live' j)
    (hk' : kopf' = nx kopf) (ho : ∀ j, nx' j = nx j) :
    ListOkF c nx' kopf' Live' ∧ ¬ Auf c nx' kopf' kopf := by
  obtain ⟨L, hk, hnd, hv⟩ := h
  generalize hg : kopf = kk at hk hne hk'
  cases hk with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hk1 L1 h1 =>
    have hch : KetteF c nx' kopf' L1 := by
      rw [hk']; exact h1.uebertragen (fun j _ => ho j)
    subst hg
    refine ⟨⟨L1, hch, (List.nodup_cons.mp hnd).2, fun i hi => hl i (hv i (List.mem_cons_of_mem _ hi))⟩, ?_⟩
    rintro ⟨L', hL', hm⟩
    have := KetteF.eindeutig hL' hch
    subst this
    exact (List.nodup_cons.mp hnd).1 hm

/-- The core of `unlink_ok`: the chain loses the successor `i` of `p`. -/
theorem unlink_aux {c : Int} {nx nx' : Int → Int} {p i : Int} (hi : i < c)
    (hp : nx p = i) (hnp : nx' p = nx i) (ho : ∀ j, j ≠ p → nx' j = nx j)
    {k : Int} {L : List Int} (h : KetteF c nx k L) (hnd : L.Nodup) (hm : p ∈ L) :
    ∃ L', KetteF c nx' k L' ∧ L.Perm (i :: L') := by
  induction h with
  | nil => simp only [List.not_mem_nil] at hm
  | cons k h0 hk L h ih =>
    by_cases hkp : k = p
    · subst hkp
      rw [hp] at h
      cases h with
      | nil => exact absurd hi (Int.lt_irrefl _)
      | cons _ h0' hi' L1 h1 =>
        have hpL : k ∉ i :: L1 := (List.nodup_cons.mp hnd).1
        refine ⟨k :: L1, KetteF.cons k h0 hk L1 ?_, List.Perm.swap _ _ _⟩
        rw [hnp]
        exact h1.uebertragen (fun j hj => ho j (fun e => hpL (e ▸ List.mem_cons_of_mem _ hj)))
    · have hmL : p ∈ L := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hkp
        · exact e
      obtain ⟨L', hk', hperm⟩ := ih (List.nodup_cons.mp hnd).2 hmL
      refine ⟨k :: L', KetteF.cons k h0 hk L' ?_, ?_⟩
      · rw [ho k hkp]; exact hk'
      · exact (hperm.cons k).trans (List.Perm.swap _ _ _)

/-- **Unlink after a predecessor** (`lnk[p] = lnk[i]`): a member `p` of the chain gives up its successor `i`.
    The new chain is well formed and `i` is no longer on it. -/
theorem unlink_ok {c : Int} {nx nx' : Int → Int} {kopf p i : Int} {Live Live' : Int → Prop}
    (h : ListOkF c nx kopf Live) (hp : Auf c nx kopf p) (hpi : nx p = i) (hi : i < c)
    (hl : ∀ j, Live j → Live' j)
    (hnp : nx' p = nx i) (ho : ∀ j, j ≠ p → nx' j = nx j) :
    ListOkF c nx' kopf Live' ∧ ¬ Auf c nx' kopf i := by
  obtain ⟨L, hk, hnd, hv⟩ := h
  obtain ⟨L0, hk0, hm⟩ := hp
  have hLL : L0 = L := KetteF.eindeutig hk0 hk
  subst hLL
  obtain ⟨L', hk', hperm⟩ := unlink_aux hi hpi hnp ho hk hnd hm
  have hnd' : (i :: L').Nodup := hperm.nodup_iff.mp hnd
  refine ⟨⟨L', hk', (List.nodup_cons.mp hnd').2,
    fun j hj => hl j (hv j (hperm.symm.subset (List.mem_cons_of_mem _ hj)))⟩, ?_⟩
  rintro ⟨L2, hL2, hm2⟩
  have := KetteF.eindeutig hL2 hk'
  subst this
  exact (List.nodup_cons.mp hnd').1 hm2

/-- **The refusal, as a theorem.** Pushing the head again (a slot that is already on the chain) makes its
    link point at itself; no finite chain from it exists. This is the model's reading of why the
    checker demands that a pushed slot is not yet linked. -/
theorem push_doppelt_bricht {c : Int} {nx' : Int → Int} {i : Int} (h0 : 0 ≤ i) (hi : i < c)
    (hn' : nx' i = i) : ¬ ∃ L, KetteF c nx' i L := by
  rintro ⟨L, hL⟩
  have key : ∀ (k : Int) (L : List Int), KetteF c nx' k L → k = i → False := by
    intro k L hL
    induction hL with
    | nil => intro e; omega
    | cons k0 _ _ L _ ih => intro e; subst e; exact ih hn'
  exact key i L hL rfl

end Gabbro.Grammatik.ArenaKette
