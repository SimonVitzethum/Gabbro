/-
  File:      Grammatik/ArenaSibling.lean
  Subject:   SIBLING CONSISTENCY OF THE CAPABILITY TREE (PLAN-DYNAMIC.md section 8a.1, step (4); the demand of TODO O4/O5/O6),
             abstractly, over the binary tree of `ArenaBaum.lean`.

  The capability derivation tree is stored as a first-child / next-sibling tree: the LEFT link `l` is the first child, the
  RIGHT link `r` is the next sibling, and a third field `par` names the parent. The consistency demand:

    `SibF c l r par w`  --  for every slot `j` of the tree rooted at `w`: its first child (if any) has parent `j`, and its
                            next sibling (if any) has the same parent as `j`.

  Two moves keep it, each with the one extra store the demand asks for:
    * a leaf in as the FIRST CHILD of `p` (left place): the new child's parent is `p`            (`sib_einfuegen_links`);
    * a leaf in as the NEXT SIBLING of `p` (right place): the new sibling's parent is `p`'s own   (`sib_einfuegen_rechts`);
    * a leaf out (either place), the parent field untouched                                          (`sib_blatt_aus_*`).
  The planted defects show the extra store is needed: a new sibling with another parent breaks the demand
  (`sib_ohne_vater_bricht`).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaBaum

namespace Gabbro.Grammatik.ArenaKette

/-- **Sibling consistency** of the tree rooted at `w` (`par` is the parent field). -/
def SibF (c : Int) (l r par : Int → Int) (w : Int) : Prop :=
  ∀ j, InBaum c l r w j → (l j < c → par (l j) = j) ∧ (r j < c → par (r j) = par j)

/-! ## 1. Who is in the tree after a move -/

/-- **Leaf in at the left place:** the slots of the new tree are exactly `i` and the old ones. -/
theorem einfuegen_mitglieder {c : Int} {l r l' r' : Int → Int} {w p i : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpl : l p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hnot : ¬ InBaum c l r w i)
    (hlp : l' p = i) (hli : l' i = c) (hri : r' i = c)
    (hol : ∀ j, j ≠ p → j ≠ i → l' j = l j) (hor : ∀ j, j ≠ i → r' j = r j) :
    ∀ j, InBaum c l' r' w j ↔ (j = i ∨ InBaum c l r w j) := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S0, hb0, hm⟩ := hp
  have hSS : S0 = S := BaumF.eindeutig hb0 hb
  subst hSS
  have hiS : i ∉ S0 := fun e => hnot ⟨S0, hb, e⟩
  obtain ⟨S', hb', hperm⟩ := einfuegen_aux h0i hi hpl hlp hli hri hol hor hb hnd hiS hm
  intro j
  constructor
  · rintro ⟨S2, hS2, hj⟩
    have := BaumF.eindeutig hS2 hb'
    subst this
    rcases List.mem_cons.mp (hperm.subset hj) with e | e
    · exact Or.inl e
    · exact Or.inr ⟨S0, hb, e⟩
  · rintro (rfl | ⟨S2, hS2, hj⟩)
    · exact ⟨S', hb', hperm.symm.subset List.mem_cons_self⟩
    · have := BaumF.eindeutig hS2 hb
      subst this
      exact ⟨S', hb', hperm.symm.subset (List.mem_cons_of_mem _ hj)⟩

/-- **Leaf in at the right place** (the mirror). -/
theorem einfuegen_rechts_mitglieder {c : Int} {l r l' r' : Int → Int} {w p i : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpr : r p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hnot : ¬ InBaum c l r w i)
    (hrp : r' p = i) (hri : r' i = c) (hli : l' i = c)
    (hor : ∀ j, j ≠ p → j ≠ i → r' j = r j) (hol : ∀ j, j ≠ i → l' j = l j) :
    ∀ j, InBaum c l' r' w j ↔ (j = i ∨ InBaum c l r w j) := by
  have hnot' : ¬ InBaum c r l w i := fun e => hnot e.spiegel
  have key := einfuegen_mitglieder (l := r) (r := l) (l' := r') (r' := l') h.spiegel hp.spiegel hpr h0i hi
    hnot' hrp hri hli hor hol
  intro j
  constructor
  · intro hj
    rcases (key j).mp hj.spiegel with e | e
    · exact Or.inl e
    · exact Or.inr e.spiegel
  · rintro (e | e)
    · exact ((key j).mpr (Or.inl e)).spiegel
    · exact ((key j).mpr (Or.inr e.spiegel)).spiegel

/-- **Leaf out at the left place:** every slot of the new tree was in the old tree, and `i` is not in it. -/
theorem blatt_aus_mitglieder {c : Int} {l l' r : Int → Int} {w p i : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : l p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c)
    (hlp : l' p = c) (hol : ∀ j, j ≠ p → l' j = l j) :
    ∀ j, InBaum c l' r w j → InBaum c l r w j ∧ j ≠ i := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S0, hb0, hm⟩ := hp
  have hSS : S0 = S := BaumF.eindeutig hb0 hb
  subst hSS
  obtain ⟨S', hb', hperm⟩ := blatt_aus_aux h0i hi hpi hll hrl hlp hol hb hnd hm
  have hnd' : (i :: S').Nodup := hperm.nodup_iff.mp hnd
  rintro j ⟨S2, hS2, hj⟩
  have := BaumF.eindeutig hS2 hb'
  subst this
  refine ⟨⟨S0, hb, hperm.symm.subset (List.mem_cons_of_mem _ hj)⟩, fun e => ?_⟩
  exact (List.nodup_cons.mp hnd').1 (e ▸ hj)

/-- **Leaf out at the right place** (the mirror): every slot of the new tree was in the old tree, and `i` is not in it. -/
theorem blatt_aus_rechts_mitglieder {c : Int} {l r r' : Int → Int} {w p i : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : r p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c)
    (hrp : r' p = c) (hor : ∀ j, j ≠ p → r' j = r j) :
    ∀ j, InBaum c l r' w j → InBaum c l r w j ∧ j ≠ i := by
  intro j hj
  have := blatt_aus_mitglieder (l := r) (r := l) (l' := r') h.spiegel hp.spiegel hpi h0i hi hrl hll hrp hor j
    hj.spiegel
  exact ⟨this.1.spiegel, this.2⟩

/-! ## 2. The demand is kept -/

/-- **Leaf in as the first child:** the new child's parent is `p`. -/
theorem sib_einfuegen_links {c : Int} {l r l' r' par par' : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpl : l p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hnot : ¬ InBaum c l r w i)
    (hlp : l' p = i) (hli : l' i = c) (hri : r' i = c)
    (hol : ∀ j, j ≠ p → j ≠ i → l' j = l j) (hor : ∀ j, j ≠ i → r' j = r j)
    (hpi : par' i = p) (hpo : ∀ j, j ≠ i → par' j = par j) :
    SibF c l' r' par' w := by
  have hmem := einfuegen_mitglieder h hp hpl h0i hi hnot hlp hli hri hol hor
  intro j hj
  rcases (hmem j).mp hj with rfl | hj0
  · exact ⟨fun hlt => by rw [hli] at hlt; exact absurd hlt (Int.lt_irrefl _),
      fun hlt => by rw [hri] at hlt; exact absurd hlt (Int.lt_irrefl _)⟩
  · have hji : j ≠ i := fun e => hnot (e ▸ hj0)
    obtain ⟨hs1, hs2⟩ := hs j hj0
    refine ⟨fun hlt => ?_, fun hlt => ?_⟩
    · by_cases hjp : j = p
      · subst hjp; rw [hlp, hpi]
      · rw [hol j hjp hji] at hlt ⊢
        have hcm : InBaum c l r w (l j) := by
          have := hj0.links hlt; exact this
        have hci : l j ≠ i := fun e => hnot (e ▸ hcm)
        rw [hpo _ hci]; exact hs1 hlt
    · rw [hor j hji] at hlt ⊢
      have hcm : InBaum c l r w (r j) := hj0.rechts hlt
      have hci : r j ≠ i := fun e => hnot (e ▸ hcm)
      rw [hpo _ hci, hpo _ hji]; exact hs2 hlt

/-- **Leaf in as the next sibling:** the new sibling has the parent of `p`. -/
theorem sib_einfuegen_rechts {c : Int} {l r l' r' par par' : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpr : r p = c)
    (h0i : 0 ≤ i) (hi : i < c) (hnot : ¬ InBaum c l r w i)
    (hrp : r' p = i) (hri : r' i = c) (hli : l' i = c)
    (hor : ∀ j, j ≠ p → j ≠ i → r' j = r j) (hol : ∀ j, j ≠ i → l' j = l j)
    (hpi : par' i = par p) (hpo : ∀ j, j ≠ i → par' j = par j) :
    SibF c l' r' par' w := by
  have hmem := einfuegen_rechts_mitglieder h hp hpr h0i hi hnot hrp hri hli hor hol
  intro j hj
  rcases (hmem j).mp hj with rfl | hj0
  · exact ⟨fun hlt => by rw [hli] at hlt; exact absurd hlt (Int.lt_irrefl _),
      fun hlt => by rw [hri] at hlt; exact absurd hlt (Int.lt_irrefl _)⟩
  · have hji : j ≠ i := fun e => hnot (e ▸ hj0)
    obtain ⟨hs1, hs2⟩ := hs j hj0
    refine ⟨fun hlt => ?_, fun hlt => ?_⟩
    · rw [hol j hji] at hlt ⊢
      have hcm : InBaum c l r w (l j) := hj0.links hlt
      have hci : l j ≠ i := fun e => hnot (e ▸ hcm)
      rw [hpo _ hci]; exact hs1 hlt
    · by_cases hjp : j = p
      · subst hjp; rw [hrp, hpi, hpo _ hji]
      · rw [hor j hjp hji] at hlt ⊢
        have hcm : InBaum c l r w (r j) := hj0.rechts hlt
        have hci : r j ≠ i := fun e => hnot (e ▸ hcm)
        rw [hpo _ hci, hpo _ hji]; exact hs2 hlt

/-- **Leaf out at the left place** (the parent field untouched): the demand holds on the smaller tree. -/
theorem sib_blatt_aus_links {c : Int} {l l' r par : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : l p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c)
    (hlp : l' p = c) (hol : ∀ j, j ≠ p → l' j = l j) :
    SibF c l' r par w := by
  have hmem := blatt_aus_mitglieder h hp hpi h0i hi hll hrl hlp hol
  intro j hj
  obtain ⟨hj0, -⟩ := hmem j hj
  obtain ⟨hs1, hs2⟩ := hs j hj0
  refine ⟨fun hlt => ?_, hs2⟩
  by_cases hjp : j = p
  · subst hjp; rw [hlp] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rw [hol j hjp] at hlt ⊢; exact hs1 hlt

/-- **Leaf out at the right place** (the parent field untouched). -/
theorem sib_blatt_aus_rechts {c : Int} {l r r' par : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : r p = i)
    (h0i : 0 ≤ i) (hi : i < c) (hll : l i = c) (hrl : r i = c)
    (hrp : r' p = c) (hor : ∀ j, j ≠ p → r' j = r j) :
    SibF c l r' par w := by
  have hnot := h
  have hmem := blatt_aus_mitglieder (l := r) (r := l) (l' := r') h.spiegel hp.spiegel hpi h0i hi hrl hll hrp hor
  intro j hj
  obtain ⟨hj0, -⟩ := hmem j hj.spiegel
  have hj1 : InBaum c l r w j := hj0.spiegel
  obtain ⟨hs1, hs2⟩ := hs j hj1
  refine ⟨hs1, fun hlt => ?_⟩
  by_cases hjp : j = p
  · subst hjp; rw [hrp] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rw [hor j hjp] at hlt ⊢; exact hs2 hlt

/-! ## 3. The planted defect: a new sibling with a foreign parent -/

/-- **Without the parent store the demand breaks:** hanging `i` as the next sibling of `p` while `i`'s parent is not
    `p`'s parent leaves a tree that violates sibling consistency. -/
theorem sib_ohne_vater_bricht {c : Int} {l' r' par' : Int → Int} {w p i : Int}
    (hp : InBaum c l' r' w p) (hrp : r' p = i) (hi : i < c) (hpar : par' i ≠ par' p) :
    ¬ SibF c l' r' par' w := by
  intro hs
  have := (hs p hp).2 (by rw [hrp]; exact hi)
  rw [hrp] at this
  exact hpar this

/-! ## 4. Witnesses on concrete numbers

    Four slots, nil marker `4`. The tree `2 (first child 0)`; the parent of `0` is `2`, every other parent is `4` (none).
    Then the live slot `3` is hung as the NEXT SIBLING of `0`, with the parent of `0`, which is `2`. -/

section Zeuge

def l0 : Int → Int := fun k => if k = 2 then 0 else 4
def r0 : Int → Int := fun _ => 4
def par0 : Int → Int := fun k => if k = 0 then 2 else 4
def r1 : Int → Int := fun k => if k = 0 then 3 else 4
def par1 : Int → Int := fun k => if k = 3 then 2 else par0 k

theorem baum0 : BaumF 4 l0 r0 2 [2, 0] := by
  have h0 : BaumF 4 l0 r0 0 [0] := by
    have := BaumF.node (c := 4) (l := l0) (r := r0) 0 (by decide) (by decide) [] []
      (by have : l0 0 = 4 := by unfold l0; decide
          rw [this]; exact BaumF.nil)
      (by have : r0 0 = 4 := rfl
          rw [this]; exact BaumF.nil)
    simpa using this
  have := BaumF.node (c := 4) (l := l0) (r := r0) 2 (by decide) (by decide) [0] []
    (by have : l0 2 = 0 := by unfold l0; decide
        rw [this]; exact h0)
    (by have : r0 2 = 4 := rfl
        rw [this]; exact BaumF.nil)
  simpa using this

theorem baumOk0 : BaumOkF 4 l0 r0 2 (fun j => 0 ≤ j ∧ j < 4) :=
  ⟨[2, 0], baum0, by decide, by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> decide⟩

theorem sib0 : SibF 4 l0 r0 par0 2 := by
  intro j ⟨S, hS, hm⟩
  have := BaumF.eindeutig hS baum0
  subst this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simp only [l0, ↓reduceIte, Int.reduceLT, par0, imp_self, r0, Int.lt_irrefl, Int.reduceEq, implies_true, and_self]

theorem hp0 : InBaum 4 l0 r0 2 0 := ⟨[2, 0], baum0, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_false, or_true]⟩

theorem hnot3 : ¬ InBaum 4 l0 r0 2 3 := by
  rintro ⟨S, hS, hm⟩
  have := BaumF.eindeutig hS baum0
  subst this; simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self] at hm

/-- **The witness:** hanging the live slot `3` as the next sibling of `0`, with the parent of `0`, keeps the demand; the new
    sibling link is real (`r1 0 = 3 < 4`), so the second clause of `SibF` is exercised at `0`. -/
theorem sib_einfuegen_zeuge : SibF 4 l0 r1 par1 2 ∧ r1 0 < 4 ∧ par1 (r1 0) = par1 0 := by
  have h := sib_einfuegen_rechts (l' := l0) (r' := r1) (par' := par1) sib0 baumOk0 hp0 rfl (by decide) (by decide) hnot3
    rfl rfl (by unfold l0; decide)
    (fun j hj hji => by unfold r1 r0; simp only [hj, ↓reduceIte])
    (fun j hji => rfl)
    (by unfold par1 par0; decide)
    (fun j hji => by unfold par1; simp only [hji, ↓reduceIte])
  refine ⟨h, by unfold r1; decide, ?_⟩
  unfold r1 par1 par0
  decide

/-- The planted defect: the same hanging with a foreign parent for the new sibling. -/
def parBad : Int → Int := fun k => if k = 0 then 2 else 4

theorem baum1 : BaumF 4 l0 r1 2 [2, 0, 3] := by
  have h3 : BaumF 4 l0 r1 3 [3] := by
    have := BaumF.node (c := 4) (l := l0) (r := r1) 3 (by decide) (by decide) [] []
      (by have : l0 3 = 4 := by unfold l0; decide
          rw [this]; exact BaumF.nil)
      (by have : r1 3 = 4 := by unfold r1; decide
          rw [this]; exact BaumF.nil)
    simpa using this
  have h0 : BaumF 4 l0 r1 0 [0, 3] := by
    have := BaumF.node (c := 4) (l := l0) (r := r1) 0 (by decide) (by decide) [] [3]
      (by have : l0 0 = 4 := by unfold l0; decide
          rw [this]; exact BaumF.nil)
      (by have : r1 0 = 3 := by unfold r1; decide
          rw [this]; exact h3)
    simpa using this
  have := BaumF.node (c := 4) (l := l0) (r := r1) 2 (by decide) (by decide) [0, 3] []
    (by have : l0 2 = 0 := by unfold l0; decide
        rw [this]; exact h0)
    (by have : r1 2 = 4 := by unfold r1; decide
        rw [this]; exact BaumF.nil)
  simpa using this

/-- **The model rejects the foreign parent:** `3` is the next sibling of `0` but `parBad 3 = 4 ≠ 2 = parBad 0`. -/
theorem sib_defekt_bricht : ¬ SibF 4 l0 r1 parBad 2 :=
  sib_ohne_vater_bricht (p := 0) (i := 3) ⟨[2, 0, 3], baum1, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false, or_true]⟩ (by unfold r1; decide) (by decide)
    (by unfold parBad; decide)

end Zeuge

end Gabbro.Grammatik.ArenaKette

#print axioms Gabbro.Grammatik.ArenaKette.einfuegen_mitglieder
#print axioms Gabbro.Grammatik.ArenaKette.einfuegen_rechts_mitglieder
#print axioms Gabbro.Grammatik.ArenaKette.blatt_aus_mitglieder
#print axioms Gabbro.Grammatik.ArenaKette.sib_einfuegen_links
#print axioms Gabbro.Grammatik.ArenaKette.sib_einfuegen_rechts
#print axioms Gabbro.Grammatik.ArenaKette.sib_blatt_aus_links
#print axioms Gabbro.Grammatik.ArenaKette.sib_blatt_aus_rechts
#print axioms Gabbro.Grammatik.ArenaKette.sib_ohne_vater_bricht

#print axioms Gabbro.Grammatik.ArenaKette.sib_einfuegen_zeuge
#print axioms Gabbro.Grammatik.ArenaKette.sib_defekt_bricht
