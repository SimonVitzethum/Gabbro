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
import Grammatik.Bausteine.Arena.Struktur.ArenaKette

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
    have hk' := g k (by simp)
    refine BaumF.node k h0 hk S1 S2 ?_ ?_
    · rw [hk'.1]; exact ih1 (fun j hj => g j (by simp [hj]))
    · rw [hk'.2]; exact ih2 (fun j hj => g j (by simp [hj]))

theorem BaumF.mem_bereich {c : Int} {l r : Int → Int} {k : Int} {S : List Int}
    (h : BaumF c l r k S) : ∀ i ∈ S, 0 ≤ i ∧ i < c := by
  induction h with
  | nil => intro i hi; simp at hi
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
  ⟨[], BaumF.nil, List.nodup_nil, by simp⟩

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
  | nil => simp at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    have hkS : k ≠ i := fun e => hiS (e ▸ List.mem_cons_self)
    have hi1 : i ∉ S1 := fun e => hiS (by simp [e])
    have hi2 : i ∉ S2 := fun e => hiS (by simp [e])
    obtain ⟨hk12, hnd12⟩ := List.nodup_cons.mp hnd
    have hk1 : k ∉ S1 := fun e => hk12 (by simp [e])
    have hk2 : k ∉ S2 := fun e => hk12 (by simp [e])
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
  | nil => simp at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    obtain ⟨hk12, hnd12⟩ := List.nodup_cons.mp hnd
    have hk1 : k ∉ S1 := fun e => hk12 (by simp [e])
    have hk2 : k ∉ S2 := fun e => hk12 (by simp [e])
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

/-- **Leaf out** (`delete_leaf`): a leaf `i` at the left place of a member `p` is cut off. The tree stays well
    formed and `i` is no longer in it (it can now be released). -/
theorem blatt_aus_ok {c : Int} {l l' r : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : l p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c) (hl : ∀ j, Live j → Live' j)
    (hlp : l' p = c) (hol : ∀ j, j ≠ p → l' j = l j) :
    BaumOkF c l' r w Live' ∧ ¬ InBaum c l' r w i := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S0, hb0, hm⟩ := hp
  have hSS : S0 = S := BaumF.eindeutig hb0 hb
  subst hSS
  obtain ⟨S', hb', hperm⟩ := blatt_aus_aux h0i hi hpi hll hrl hlp hol hb hnd hm
  have hnd' : (i :: S').Nodup := hperm.nodup_iff.mp hnd
  refine ⟨⟨S', hb', (List.nodup_cons.mp hnd').2,
    fun j hj => hl j (hv j (hperm.symm.subset (List.mem_cons_of_mem _ hj)))⟩, ?_⟩
  rintro ⟨S2, hS2, hm2⟩
  have := BaumF.eindeutig hS2 hb'
  subst this
  exact (List.nodup_cons.mp hnd').1 hm2

/-- **The refusal, as a theorem.** Hanging a slot below itself (it is already in the tree) leaves no tree: the
    left link of `i` would be `i`, and no finite tree exists from `i`. -/
theorem einfuegen_doppelt_bricht {c : Int} {l' r' : Int → Int} {i : Int} (hi : i < c)
    (hli : l' i = i) : ¬ ∃ S, BaumF c l' r' i S := by
  rintro ⟨S, hS⟩
  have key : ∀ (k : Int) (S : List Int), BaumF c l' r' k S → k = i → False := by
    intro k S hS
    induction hS with
    | nil => intro e; omega
    | node k0 _ _ S1 S2 _ _ ih1 _ => intro e; subst e; exact ih1 hli
  exact key i S hS rfl

/-- Every slot of a well formed tree is live. -/
theorem BaumOkF.lebt_in {c : Int} {l r : Int → Int} {w : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) {j : Int} (hj : InBaum c l r w j) : Live j := by
  obtain ⟨S, hb, _, hv⟩ := h
  obtain ⟨S', hb', hm⟩ := hj
  have := BaumF.eindeutig hb' hb
  subst this
  exact hv j hm

/-- A slot with a property that no live slot has is not in a well formed tree. -/
theorem BaumOkF.nicht_in {c : Int} {l r : Int → Int} {w : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (P : Int → Prop) (hP : ∀ j, Live j → ¬ P j) {i : Int} (hi : P i) :
    ¬ InBaum c l r w i := fun hj => hP i (h.lebt_in hj) hi

/-- A well formed tree stays well formed when the links change away from its slots and its own slots are live
    afterwards (a weaker side condition than `rahmen`). -/
theorem BaumOkF.rahmen' {c : Int} {l r l' r' : Int → Int} {w : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hl : ∀ j, InBaum c l r w j → Live' j)
    (g : ∀ j, InBaum c l r w j → l' j = l j ∧ r' j = r j) : BaumOkF c l' r' w Live' := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  exact ⟨S, hb.uebertragen (fun j hj => g j ⟨S, hb, hj⟩), hnd, fun i hi => hl i ⟨S, hb, hi⟩⟩

/-- The mirror image of a tree is a tree with the same slots. -/
theorem BaumF.spiegel {c : Int} {l r : Int → Int} {k : Int} {S : List Int} (h : BaumF c l r k S) :
    ∃ S', BaumF c r l k S' ∧ S.Perm S' := by
  induction h with
  | nil => exact ⟨[], BaumF.nil, List.Perm.refl _⟩
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    obtain ⟨T1, g1, p1⟩ := ih1
    obtain ⟨T2, g2, p2⟩ := ih2
    exact ⟨k :: (T2 ++ T1), BaumF.node k h0 hk T2 T1 g2 g1,
      ((p1.append p2).trans List.perm_append_comm).cons k⟩

theorem BaumOkF.spiegel {c : Int} {l r : Int → Int} {w : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) : BaumOkF c r l w Live := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S', hb', hp⟩ := hb.spiegel
  exact ⟨S', hb', hp.nodup_iff.mp hnd, fun i hi => hv i (hp.symm.subset hi)⟩

theorem InBaum.spiegel {c : Int} {l r : Int → Int} {w i : Int} (h : InBaum c l r w i) :
    InBaum c r l w i := by
  obtain ⟨S, hb, hm⟩ := h
  obtain ⟨S', hb', hp⟩ := hb.spiegel
  exact ⟨S', hb', hp.subset hm⟩

/-- **Leaf in at an empty RIGHT place** (the mirror of `einfuegen_ok`). -/
theorem einfuegen_rechts_ok {c : Int} {l r l' r' : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpr : r p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hlive : Live' i) (hl : ∀ j, Live j → Live' j)
    (hnot : ¬ InBaum c l r w i)
    (hrp : r' p = i) (hri : r' i = c) (hli : l' i = c)
    (hor : ∀ j, j ≠ p → j ≠ i → r' j = r j) (hol : ∀ j, j ≠ i → l' j = l j) :
    BaumOkF c l' r' w Live' ∧ InBaum c l' r' w i := by
  have hnot' : ¬ InBaum c r l w i := fun e => hnot e.spiegel
  obtain ⟨h1, h2⟩ := einfuegen_ok (l := r) (r := l) (l' := r') (r' := l') h.spiegel hp.spiegel hpr h0i hi
    hlive hl hnot' hrp hri hli hor hol
  exact ⟨h1.spiegel, h2.spiegel⟩

/-- **Leaf out at the RIGHT place** (the mirror of `blatt_aus_ok`). -/
theorem blatt_aus_rechts_ok {c : Int} {l r r' : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : r p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c) (hl : ∀ j, Live j → Live' j)
    (hrp : r' p = c) (hor : ∀ j, j ≠ p → r' j = r j) :
    BaumOkF c l r' w Live' ∧ ¬ InBaum c l r' w i := by
  obtain ⟨h1, h2⟩ := blatt_aus_ok (l := r) (r := l) (l' := r') h.spiegel hp.spiegel hpi h0i hi hrl hll hl hrp hor
  exact ⟨h1.spiegel, fun e => h2 e.spiegel⟩

/-- A child (when it is a slot) of a member is a member. -/
theorem BaumF.kind_mem {c : Int} {l r : Int → Int} {k : Int} {S : List Int} (h : BaumF c l r k S)
    {p : Int} (hm : p ∈ S) : (l p < c → l p ∈ S) ∧ (r p < c → r p ∈ S) := by
  induction h with
  | nil => simp at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    by_cases hkp : p = k
    · subst hkp
      refine ⟨fun hl => ?_, fun hr => ?_⟩
      · cases h1 with
        | nil => exact absurd hl (Int.lt_irrefl _)
        | node _ _ _ T1 T2 g1 g2 => simp
      · cases h2 with
        | nil => exact absurd hr (Int.lt_irrefl _)
        | node _ _ _ T1 T2 g1 g2 => simp
    · have hm' : p ∈ S1 ∨ p ∈ S2 := by
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with e | e | e
        · exact absurd e hkp
        · exact Or.inl e
        · exact Or.inr e
      rcases hm' with e | e
      · exact ⟨fun hl => by have := (ih1 e).1 hl; simp [this], fun hr => by have := (ih1 e).2 hr; simp [this]⟩
      · exact ⟨fun hl => by have := (ih2 e).1 hl; simp [this], fun hr => by have := (ih2 e).2 hr; simp [this]⟩

theorem InBaum.links {c : Int} {l r : Int → Int} {w p : Int} (h : InBaum c l r w p) (hl : l p < c) :
    InBaum c l r w (l p) := by
  obtain ⟨S, hb, hm⟩ := h
  exact ⟨S, hb, (hb.kind_mem hm).1 hl⟩

theorem InBaum.rechts {c : Int} {l r : Int → Int} {w p : Int} (h : InBaum c l r w p) (hr : r p < c) :
    InBaum c l r w (r p) := by
  obtain ⟨S, hb, hm⟩ := h
  exact ⟨S, hb, (hb.kind_mem hm).2 hr⟩

/-! ## 2. Witnesses (non-degenerate, and the mutations run on them) -/

/-- A concrete list `2 -> 0` in a table of 4 slots, with `1` live and free to link: pushing `1` gives `1 -> 2 -> 0`. -/
theorem liste_zeuge :
    ∃ nx nx' : Int → Int, ListOkF 4 nx 2 (fun j => j < 3) ∧ ¬ Auf 4 nx 2 1 ∧
      ListOkF 4 nx' 1 (fun j => j < 3) ∧ Auf 4 nx' 1 0 := by
  let nx : Int → Int := fun j => if j = 2 then 0 else 4
  let nx' : Int → Int := fun j => if j = 1 then 2 else nx j
  have hk : KetteF 4 nx 2 [2, 0] :=
    KetteF.cons 2 (by omega) (by omega) [0]
      (by show KetteF 4 nx 0 [0]; exact KetteF.cons 0 (by omega) (by omega) []
            (by show KetteF 4 nx 4 []; exact KetteF.nil))
  have h1 : ListOkF 4 nx 2 (fun j => j < 3) :=
    ⟨[2, 0], hk, by decide, by intro i hi; simp at hi; omega⟩
  have hnot : ¬ Auf 4 nx 2 1 := by
    rintro ⟨L, hL, hm⟩
    have := KetteF.eindeutig hL hk
    subst this; simp at hm
  have h2 := push_ok (nx' := nx') (kopf' := 1) h1 (by omega) (by omega) (by omega)
    (fun _ h => h) hnot rfl (by simp [nx']) (by intro j hj; simp [nx', hj])
  refine ⟨nx, nx', h1, hnot, h2, ?_⟩
  obtain ⟨L, hL, _, _⟩ := h2
  have hk' : KetteF 4 nx' 1 [1, 2, 0] :=
    KetteF.cons 1 (by omega) (by omega) [2, 0]
      (by show KetteF 4 nx' 2 [2, 0]
          exact hk.uebertragen (fun j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl <;> simp [nx']))
  exact ⟨[1, 2, 0], hk', by simp⟩

/-- A concrete tree (`0` with children `1`, `2`) in a table of 5 slots; the live leaf `3` is hung below `1`, then cut
    off again. -/
theorem baum_zeuge :
    ∃ l r l' : Int → Int, BaumOkF 5 l r 0 (fun j => j < 4) ∧ ¬ InBaum 5 l r 0 3 ∧
      BaumOkF 5 l' r 0 (fun j => j < 4) ∧ InBaum 5 l' r 0 3 := by
  let l : Int → Int := fun j => if j = 0 then 1 else 5
  let r : Int → Int := fun j => if j = 0 then 2 else 5
  let l' : Int → Int := fun j => if j = 1 then 3 else l j
  have hb : BaumF 5 l r 0 [0, 1, 2] := by
    have := BaumF.node (c := 5) (l := l) (r := r) 0 (by omega) (by omega) [1] [2]
      (BaumF.node (c := 5) (l := l) (r := r) 1 (by omega) (by omega) [] [] (by show BaumF 5 l r 5 []; exact BaumF.nil)
        (by show BaumF 5 l r 5 []; exact BaumF.nil))
      (BaumF.node (c := 5) (l := l) (r := r) 2 (by omega) (by omega) [] [] (by show BaumF 5 l r 5 []; exact BaumF.nil)
        (by show BaumF 5 l r 5 []; exact BaumF.nil))
    simpa using this
  have h1 : BaumOkF 5 l r 0 (fun j => j < 4) :=
    ⟨[0, 1, 2], hb, by decide, by intro i hi; simp at hi; omega⟩
  have hnot : ¬ InBaum 5 l r 0 3 := by
    rintro ⟨S, hS, hm⟩
    have := BaumF.eindeutig hS hb
    subst this; simp at hm
  have hp : InBaum 5 l r 0 1 := ⟨[0, 1, 2], hb, by simp⟩
  have h2 := einfuegen_ok (l' := l') (r' := r) (p := 1) (i := 3) (Live' := fun j => j < 4)
    h1 hp (by simp [l]) (by omega) (by omega) (by omega) (fun _ h => h) hnot (by simp [l'])
    (by simp [l', l]) rfl (by intro j hj _; simp [l', hj]) (fun _ _ => rfl)
  exact ⟨l, r, l', h1, hnot, h2.1, h2.2⟩

end Gabbro.Grammatik.ArenaKette
