/-
  File:      Grammatik/ArenaBaum.lean
  Subject:   THE BINARY TREE OVER INDICES, abstractly (PLAN-DYNAMIC.md section 8a, phase 2, abstract half;
             the capability derivation tree of O4-O6 has this shape).

    * `BaumF c l r k S`   -- the tree rooted at `k` has exactly the slots `S` (preorder); `c` is the nil marker.
    * `BaumOkF`           -- `S.Nodup` (no slot twice: the subtrees are disjoint and no slot is its own ancestor)
      and every slot live.
    * `einfuegen_ok`, `blatt_aus_ok` (left place) and their right-hand mirrors: a leaf in at an empty child place,
      a leaf out. `einfuegen_doppelt_bricht` is the model's reading of the refusal to link a slot below itself.
-/
module
public import Grammatik.Bausteine.Arena.Struktur.ArenaKette
@[expose] public section


namespace Gabbro.Grammatik.ArenaKette

/-- The tree rooted at `k` has exactly the slots `S` (root, left subtree, right subtree). -/
inductive BaumF (c : Int) (l r : Int → Int) : Int → List Int → Prop where
  | nil : BaumF c l r c []
  | node (k : Int) (h0 : 0 ≤ k) (hk : k < c) (S1 S2 : List Int)
      (h1 : BaumF c l r (l k) S1) (h2 : BaumF c l r (r k) S2) :
      BaumF c l r k (k :: (S1 ++ S2))

/-- The empty tree has no slots. -/
theorem BaumF.leer {c : Int} {l r : Int → Int} {S : List Int} (h : BaumF c l r c S) : S = [] := by
  cases h with
  | nil => rfl
  | node _ _ hk _ _ _ _ => exact absurd hk (Int.lt_irrefl _)

theorem BaumF.uebertragen {c : Int} {l r l' r' : Int → Int} {k : Int} {S : List Int}
    (h : BaumF c l r k S) (g : ∀ j ∈ S, l' j = l j ∧ r' j = r j) : BaumF c l' r' k S := by
  induction h with
  | nil => exact BaumF.nil
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    have hk' := g k (by simp only [List.mem_cons, List.mem_append, true_or])
    refine BaumF.node k h0 hk S1 S2 ?_ ?_
    · rw [hk'.1]; exact ih1 (fun j hj => g j (by simp only [List.mem_cons, List.mem_append, hj, true_or, or_true]))
    · rw [hk'.2]; exact ih2 (fun j hj => g j (by simp only [List.mem_cons, List.mem_append, hj, or_true]))

theorem BaumF.mem_bereich {c : Int} {l r : Int → Int} {k : Int} {S : List Int}
    (h : BaumF c l r k S) : ∀ i ∈ S, 0 ≤ i ∧ i < c := by
  induction h with
  | nil => intro i hi; simp only [List.not_mem_nil] at hi
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    intro i hi
    simp only [List.mem_cons, List.mem_append] at hi
    rcases hi with rfl | hi | hi
    · exact ⟨h0, hk⟩
    · exact ih1 i hi
    · exact ih2 i hi

theorem BaumF.eindeutig {c : Int} {l r : Int → Int} {k : Int} {S S' : List Int}
    (h : BaumF c l r k S) (h' : BaumF c l r k S') : S = S' := by
  induction h generalizing S' with
  | nil => exact (BaumF.leer h').symm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    cases h' with
    | nil => exact absurd hk (Int.lt_irrefl _)
    | node _ _ _ T1 T2 g1 g2 => rw [ih1 g1, ih2 g2]

/-- **The invariant of a binary tree over live slots:** every slot occurs at most once (the subtrees are
    disjoint and no slot is its own ancestor: tree shape) and every slot is live. -/
def BaumOkF (c : Int) (l r : Int → Int) (wurzel : Int) (Live : Int → Prop) : Prop :=
  ∃ S, BaumF c l r wurzel S ∧ S.Nodup ∧ ∀ i ∈ S, Live i

def InBaum (c : Int) (l r : Int → Int) (wurzel i : Int) : Prop :=
  ∃ S, BaumF c l r wurzel S ∧ i ∈ S

theorem baumOkF_leer (c : Int) (l r : Int → Int) (Live : Int → Prop) : BaumOkF c l r c Live :=
  ⟨[], BaumF.nil, List.nodup_nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩

/-- A well formed tree survives a change of the links away from its slots and a widening of the live set. -/
theorem BaumOkF.rahmen {c : Int} {l r l' r' : Int → Int} {w : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hl : ∀ j, Live j → Live' j)
    (g : ∀ j, InBaum c l r w j → l' j = l j ∧ r' j = r j) : BaumOkF c l' r' w Live' := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  exact ⟨S, hb.uebertragen (fun j hj => g j ⟨S, hb, hj⟩), hnd, fun i hi => hl i (hv i hi)⟩

/-- The core of `einfuegen_ok`: a fresh leaf `i` below the member `p`, at the empty left place. -/
theorem einfuegen_aux {c : Int} {l r l' r' : Int → Int} {p i : Int} (h0i : 0 ≤ i) (hi : i < c)
    (hpl : l p = c) (hlp : l' p = i) (hli : l' i = c) (hri : r' i = c)
    (hol : ∀ j, j ≠ p → j ≠ i → l' j = l j) (hor : ∀ j, j ≠ i → r' j = r j)
    {k : Int} {S : List Int} (h : BaumF c l r k S) (hnd : S.Nodup) (hiS : i ∉ S) (hm : p ∈ S) :
    ∃ S', BaumF c l' r' k S' ∧ S'.Perm (i :: S) := by
  induction h with
  | nil => simp only [List.not_mem_nil] at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    have hkS : k ≠ i := fun e => hiS (e ▸ List.mem_cons_self)
    have hi1 : i ∉ S1 := fun e => hiS (by simp only [List.mem_cons, List.mem_append, e, true_or, or_true])
    have hi2 : i ∉ S2 := fun e => hiS (by simp only [List.mem_cons, List.mem_append, e, or_true])
    obtain ⟨hk12, hnd12⟩ := List.nodup_cons.mp hnd
    have hk1 : k ∉ S1 := fun e => hk12 (by simp only [List.mem_append, e, true_or])
    have hk2 : k ∉ S2 := fun e => hk12 (by simp only [List.mem_append, e, or_true])
    have hnd1 : S1.Nodup := (List.nodup_append.mp hnd12).1
    have hnd2 : S2.Nodup := (List.nodup_append.mp hnd12).2.1
    have hdisj : ∀ x ∈ S1, x ∉ S2 := fun x hx hx2 => (List.nodup_append.mp hnd12).2.2 x hx x hx2 rfl
    by_cases hkp : k = p
    · subst hkp
      rw [hpl] at h1
      have hS1 : S1 = [] := h1.leer
      subst hS1
      have hleaf : BaumF c l' r' i [i] := by
        have := BaumF.node (l := l') (r := r') i h0i hi [] [] (by rw [hli]; exact BaumF.nil)
          (by rw [hri]; exact BaumF.nil)
        simpa using this
      refine ⟨k :: ([i] ++ S2), BaumF.node k h0 hk [i] S2 ?_ ?_, ?_⟩
      · rw [hlp]; exact hleaf
      · rw [hor k hkS]
        exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hk2 (e ▸ hj)) (fun e => hi2 (e ▸ hj)), hor j (fun e => hi2 (e ▸ hj))⟩)
      · simp only [List.nil_append, List.cons_append]
        exact List.Perm.swap _ _ _
    · have hm' : p ∈ S1 ∨ p ∈ S2 := by
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with e | e | e
        · exact absurd e.symm hkp
        · exact Or.inl e
        · exact Or.inr e
      rcases hm' with hm1 | hm2
      · obtain ⟨T1, g1, hperm⟩ := ih1 hnd1 hi1 hm1
        have hp2 : p ∉ S2 := hdisj p hm1
        refine ⟨k :: (T1 ++ S2), BaumF.node k h0 hk T1 S2 ?_ ?_, ?_⟩
        · rw [hol k hkp hkS]; exact g1
        · rw [hor k hkS]
          exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hp2 (e ▸ hj)) (fun e => hi2 (e ▸ hj)), hor j (fun e => hi2 (e ▸ hj))⟩)
        · exact ((hperm.append_right S2).cons k).trans (List.Perm.swap i k _)
      · obtain ⟨T2, g2, hperm⟩ := ih2 hnd2 hi2 hm2
        have hp1 : p ∉ S1 := fun e => hdisj p e hm2
        refine ⟨k :: (S1 ++ T2), BaumF.node k h0 hk S1 T2 ?_ ?_, ?_⟩
        · rw [hol k hkp hkS]
          exact h1.uebertragen (fun j hj => ⟨hol j (fun e => hp1 (e ▸ hj)) (fun e => hi1 (e ▸ hj)), hor j (fun e => hi1 (e ▸ hj))⟩)
        · rw [hor k hkS]; exact g2
        · exact (((hperm.append_left S1).trans List.perm_middle).cons k).trans (List.Perm.swap i k _)

/-- **Leaf in** (`insert`): a live slot that is not in the tree becomes the left child of a member whose left
    place is empty. The tree stays well formed (disjoint subtrees, no slot twice). -/
theorem einfuegen_ok {c : Int} {l r l' r' : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpl : l p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hlive : Live' i) (hl : ∀ j, Live j → Live' j)
    (hnot : ¬ InBaum c l r w i)
    (hlp : l' p = i) (hli : l' i = c) (hri : r' i = c)
    (hol : ∀ j, j ≠ p → j ≠ i → l' j = l j) (hor : ∀ j, j ≠ i → r' j = r j) :
    BaumOkF c l' r' w Live' ∧ InBaum c l' r' w i := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S0, hb0, hm⟩ := hp
  have hSS : S0 = S := BaumF.eindeutig hb0 hb
  subst hSS
  have hiS : i ∉ S0 := fun e => hnot ⟨S0, hb, e⟩
  obtain ⟨S', hb', hperm⟩ := einfuegen_aux h0i hi hpl hlp hli hri hol hor hb hnd hiS hm
  refine ⟨⟨S', hb', hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hiS, hnd⟩), fun j hj => ?_⟩,
    ⟨S', hb', hperm.symm.subset List.mem_cons_self⟩⟩
  rcases List.mem_cons.mp (hperm.subset hj) with rfl | hj
  · exact hlive
  · exact hl j (hv j hj)

/-- The core of `blatt_aus_ok`: the leaf `i` that hangs at the left place of `p` is cut off. -/
theorem blatt_aus_aux {c : Int} {l l' r : Int → Int} {p i : Int} (h0i : 0 ≤ i) (hi : i < c)
    (hpi : l p = i) (hll : l i = c) (hrl : r i = c) (hlp : l' p = c)
    (hol : ∀ j, j ≠ p → l' j = l j)
    {k : Int} {S : List Int} (h : BaumF c l r k S) (hnd : S.Nodup) (hm : p ∈ S) :
    ∃ S', BaumF c l' r k S' ∧ S.Perm (i :: S') := by
  induction h with
  | nil => simp only [List.not_mem_nil] at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    obtain ⟨hk12, hnd12⟩ := List.nodup_cons.mp hnd
    have hk1 : k ∉ S1 := fun e => hk12 (by simp only [List.mem_append, e, true_or])
    have hk2 : k ∉ S2 := fun e => hk12 (by simp only [List.mem_append, e, or_true])
    have hnd1 : S1.Nodup := (List.nodup_append.mp hnd12).1
    have hnd2 : S2.Nodup := (List.nodup_append.mp hnd12).2.1
    have hdisj : ∀ x ∈ S1, x ∉ S2 := fun x hx hx2 => (List.nodup_append.mp hnd12).2.2 x hx x hx2 rfl
    by_cases hkp : k = p
    · subst hkp
      rw [hpi] at h1
      cases h1 with
      | nil => exact absurd hi (Int.lt_irrefl _)
      | node _ _ _ T1 T2 g1 g2 =>
        rw [hll] at g1
        rw [hrl] at g2
        have e1 : T1 = [] := g1.leer
        have e2 : T2 = [] := g2.leer
        subst e1; subst e2
        refine ⟨k :: S2, BaumF.node k h0 hk [] S2 ?_ ?_, ?_⟩
        · rw [hlp]; exact BaumF.nil
        · exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hk2 (e ▸ hj)), rfl⟩)
        · exact List.Perm.swap i k _
    · have hm' : p ∈ S1 ∨ p ∈ S2 := by
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with e | e | e
        · exact absurd e.symm hkp
        · exact Or.inl e
        · exact Or.inr e
      rcases hm' with hm1 | hm2
      · obtain ⟨T1, g1, hperm⟩ := ih1 hnd1 hm1
        have hp2 : p ∉ S2 := hdisj p hm1
        refine ⟨k :: (T1 ++ S2), BaumF.node k h0 hk T1 S2 ?_ ?_, ?_⟩
        · rw [hol k hkp]; exact g1
        · exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hp2 (e ▸ hj)), rfl⟩)
        · exact ((hperm.append_right S2).cons k).trans (List.Perm.swap i k _)
      · obtain ⟨T2, g2, hperm⟩ := ih2 hnd2 hm2
        have hp1 : p ∉ S1 := fun e => hdisj p e hm2
        refine ⟨k :: (S1 ++ T2), BaumF.node k h0 hk S1 T2 ?_ g2, ?_⟩
        · rw [hol k hkp]
          exact h1.uebertragen (fun j hj => ⟨hol j (fun e => hp1 (e ▸ hj)), rfl⟩)
        · exact (((hperm.append_left S1).trans List.perm_middle).cons k).trans (List.Perm.swap i k _)

end Gabbro.Grammatik.ArenaKette
