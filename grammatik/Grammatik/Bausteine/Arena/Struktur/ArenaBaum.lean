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
public import Grammatik.Bausteine.Arena.Struktur.ArenaBaumBasis
public import Grammatik.Bausteine.Arena.Struktur.ArenaKette
@[expose] public section


namespace Gabbro.Grammatik.ArenaKette

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
  | nil => simp only [List.not_mem_nil] at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    by_cases hkp : p = k
    · subst hkp
      refine ⟨fun hl => ?_, fun hr => ?_⟩
      · cases h1 with
        | nil => exact absurd hl (Int.lt_irrefl _)
        | node _ _ _ T1 T2 g1 g2 => simp only [List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, true_or, or_true]
      · cases h2 with
        | nil => exact absurd hr (Int.lt_irrefl _)
        | node _ _ _ T1 T2 g1 g2 => simp only [List.mem_cons, List.mem_append, true_or, or_true]
    · have hm' : p ∈ S1 ∨ p ∈ S2 := by
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with e | e | e
        · exact absurd e hkp
        · exact Or.inl e
        · exact Or.inr e
      rcases hm' with e | e
      · exact ⟨fun hl => by have := (ih1 e).1 hl; simp only [List.mem_cons, List.mem_append, this, true_or, or_true], fun hr => by have := (ih1 e).2 hr; simp only [List.mem_cons, List.mem_append, this, true_or, or_true]⟩
      · exact ⟨fun hl => by have := (ih2 e).1 hl; simp only [List.mem_cons, List.mem_append, this, or_true], fun hr => by have := (ih2 e).2 hr; simp only [List.mem_cons, List.mem_append, this, or_true]⟩

theorem InBaum.links {c : Int} {l r : Int → Int} {w p : Int} (h : InBaum c l r w p) (hl : l p < c) :
    InBaum c l r w (l p) := by
  obtain ⟨S, hb, hm⟩ := h
  exact ⟨S, hb, (hb.kind_mem hm).1 hl⟩

theorem InBaum.rechts {c : Int} {l r : Int → Int} {w p : Int} (h : InBaum c l r w p) (hr : r p < c) :
    InBaum c l r w (r p) := by
  obtain ⟨S, hb, hm⟩ := h
  exact ⟨S, hb, (hb.kind_mem hm).2 hr⟩

/-! ## 2. Witnesses (non-degenerate, and the mutations run on them) -/

end Gabbro.Grammatik.ArenaKette
