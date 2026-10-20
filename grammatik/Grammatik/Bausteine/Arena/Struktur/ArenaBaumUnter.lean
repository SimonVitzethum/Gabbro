/-
  File:      Grammatik/ArenaBaumUnter.lean
  Subject:   CUTTING A WHOLE SUBTREE OFF THE BINARY TREE (`revoke` of the capability tree, PLAN-DYNAMIC.md section 8a.1,
             third pass), abstractly. `blatt_aus_ok` (`ArenaBaum.lean`) cuts a LEAF; here the child `i` of the member `p` may
             be the root of a whole subtree, and the store is the same one (`l p = nil`).

    `unterbaum_aus_ok`  -- the tree that remains is well formed and its members are exactly the old members that were not
                           in the subtree of `i`; the subtree's slots are live and in the remaining tree no longer
                           (they are orphans now, and `baum_frei`-style releases of them keep the tree);
    `sib_unterbaum_aus_links` -- the sibling consistency demand holds on the remaining tree (the parent field is untouched).

  Right-hand mirrors by the mirror image of the tree.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaSibling

namespace Gabbro.Grammatik.ArenaKette

/-- The core: the subtree below the left place of `p` splits off the shape list. -/
theorem unterbaum_aux {c : Int} {l l' r : Int → Int} {p i : Int} (hpi : l p = i) (hlp : l' p = c)
    (hol : ∀ j, j ≠ p → l' j = l j)
    {k : Int} {S : List Int} (h : BaumF c l r k S) (hnd : S.Nodup) (hm : p ∈ S) :
    ∃ T S', BaumF c l r i T ∧ BaumF c l' r k S' ∧ S.Perm (T ++ S') := by
  induction h with
  | nil => simp at hm
  | node k h0 hk S1 S2 h1 h2 ih1 ih2 =>
    obtain ⟨hk12, hnd12⟩ := List.nodup_cons.mp hnd
    have hk2 : k ∉ S2 := fun e => hk12 (by simp [e])
    have hnd1 : S1.Nodup := (List.nodup_append.mp hnd12).1
    have hnd2 : S2.Nodup := (List.nodup_append.mp hnd12).2.1
    have hdisj : ∀ x ∈ S1, x ∉ S2 := fun x hx hx2 => (List.nodup_append.mp hnd12).2.2 x hx x hx2 rfl
    by_cases hkp : k = p
    · subst hkp
      rw [hpi] at h1
      refine ⟨S1, k :: S2, h1, BaumF.node k h0 hk [] S2 ?_ ?_, ?_⟩
      · rw [hlp]; exact BaumF.nil
      · exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hk2 (e ▸ hj)), rfl⟩)
      · simpa using (List.perm_middle (l₁ := S1) (a := k) (l₂ := S2)).symm
    · have hm' : p ∈ S1 ∨ p ∈ S2 := by
        simp only [List.mem_cons, List.mem_append] at hm
        rcases hm with e | e | e
        · exact absurd e.symm hkp
        · exact Or.inl e
        · exact Or.inr e
      rcases hm' with hm1 | hm2
      · obtain ⟨T, T1, gT, g1, hperm⟩ := ih1 hnd1 hm1
        have hp2 : p ∉ S2 := hdisj p hm1
        refine ⟨T, k :: (T1 ++ S2), gT, BaumF.node k h0 hk T1 S2 ?_ ?_, ?_⟩
        · rw [hol k hkp]; exact g1
        · exact h2.uebertragen (fun j hj => ⟨hol j (fun e => hp2 (e ▸ hj)), rfl⟩)
        · have h4 := (hperm.append_right S2).cons k
          rw [List.append_assoc] at h4
          exact h4.trans (List.perm_middle (l₁ := T) (a := k) (l₂ := T1 ++ S2)).symm
      · obtain ⟨T, T2, gT, g2, hperm⟩ := ih2 hnd2 hm2
        have hp1 : p ∉ S1 := fun e => hdisj p e hm2
        refine ⟨T, k :: (S1 ++ T2), gT, BaumF.node k h0 hk S1 T2 ?_ g2, ?_⟩
        · rw [hol k hkp]
          exact h1.uebertragen (fun j hj => ⟨hol j (fun e => hp1 (e ▸ hj)), rfl⟩)
        · have h3 : (S1 ++ (T ++ T2)).Perm (T ++ (S1 ++ T2)) := by
            rw [← List.append_assoc, ← List.append_assoc]
            exact List.perm_append_comm.append_right T2
          exact (((hperm.append_left S1).trans h3).cons k).trans
            (List.perm_middle (l₁ := T) (a := k) (l₂ := S1 ++ T2)).symm

/-- **Cut a subtree off at the left place** (`revoke`): the tree that remains is well formed, its members are old members
    outside the subtree, and no slot of the subtree is a member any more. -/
theorem unterbaum_aus_ok {c : Int} {l l' r : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : l p = i) (hl : ∀ j, Live j → Live' j)
    (hlp : l' p = c) (hol : ∀ j, j ≠ p → l' j = l j) :
    BaumOkF c l' r w Live' ∧
      (∀ j, InBaum c l' r w j → InBaum c l r w j ∧ ¬ InBaum c l r i j) ∧
      (∀ j, InBaum c l r i j → ¬ InBaum c l' r w j) ∧
      (∀ j, InBaum c l r w j → InBaum c l r i j ∨ InBaum c l' r w j) ∧
      (∀ j, InBaum c l r i j → InBaum c l r w j) := by
  obtain ⟨S, hb, hnd, hv⟩ := h
  obtain ⟨S0, hb0, hm⟩ := hp
  have hSS : S0 = S := BaumF.eindeutig hb0 hb
  subst hSS
  obtain ⟨T, S', gT, gS', hperm⟩ := unterbaum_aux hpi hlp hol hb hnd hm
  have hnd' : (T ++ S').Nodup := hperm.nodup_iff.mp hnd
  have hdisj : ∀ x ∈ T, x ∉ S' := fun x hx hx' => (List.nodup_append.mp hnd').2.2 x hx x hx' rfl
  have hin' : ∀ j, InBaum c l' r w j ↔ j ∈ S' := fun j => by
    constructor
    · rintro ⟨S2, hS2, hj⟩
      have := BaumF.eindeutig hS2 gS'
      subst this; exact hj
    · intro hj; exact ⟨S', gS', hj⟩
  have hinT : ∀ j, InBaum c l r i j ↔ j ∈ T := fun j => by
    constructor
    · rintro ⟨S2, hS2, hj⟩
      have := BaumF.eindeutig hS2 gT
      subst this; exact hj
    · intro hj; exact ⟨T, gT, hj⟩
  have hinS : ∀ j, InBaum c l r w j ↔ j ∈ T ∨ j ∈ S' := fun j => by
    constructor
    · rintro ⟨S2, hS2, hj⟩
      have := BaumF.eindeutig hS2 hb
      subst this
      exact List.mem_append.mp (hperm.subset hj)
    · intro hj; exact ⟨S0, hb, hperm.symm.subset (List.mem_append.mpr hj)⟩
  refine ⟨⟨S', gS', (List.nodup_append.mp hnd').2.1, fun j hj => hl j (hv j (hperm.symm.subset
      (List.mem_append.mpr (Or.inr hj))))⟩, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hin'] at hj
    exact ⟨(hinS j).mpr (Or.inr hj), fun e => hdisj j ((hinT j).mp e) hj⟩
  · intro j hj hj'
    rw [hin'] at hj'
    exact hdisj j ((hinT j).mp hj) hj'
  · intro j hj
    rcases (hinS j).mp hj with e | e
    · exact Or.inl ((hinT j).mpr e)
    · exact Or.inr ((hin' j).mpr e)
  · intro j hj
    exact (hinS j).mpr (Or.inl ((hinT j).mp hj))

/-- **Cut a subtree off at the right place** (the mirror image). -/
theorem unterbaum_aus_rechts_ok {c : Int} {l r r' : Int → Int} {w p i : Int} {Live Live' : Int → Prop}
    (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : r p = i) (hl : ∀ j, Live j → Live' j)
    (hrp : r' p = c) (hor : ∀ j, j ≠ p → r' j = r j) :
    BaumOkF c l r' w Live' ∧
      (∀ j, InBaum c l r' w j → InBaum c l r w j ∧ ¬ InBaum c r l i j ∧ True) ∧
      (∀ j, InBaum c r l i j → ¬ InBaum c l r' w j) ∧
      (∀ j, InBaum c l r w j → InBaum c r l i j ∨ InBaum c l r' w j) ∧
      (∀ j, InBaum c r l i j → InBaum c l r w j) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := unterbaum_aus_ok (l := r) (r := l) (l' := r') h.spiegel hp.spiegel hpi hl hrp hor
  refine ⟨h1.spiegel, fun j hj => ?_, fun j hj hj' => h3 j hj hj'.spiegel, fun j hj => ?_,
    fun j hj => (h5 j hj).spiegel⟩
  · obtain ⟨a, b⟩ := h2 j hj.spiegel
    exact ⟨a.spiegel, b, trivial⟩
  · rcases h4 j hj.spiegel with e | e
    · exact Or.inl e
    · exact Or.inr e.spiegel

/-- **The sibling consistency demand survives cutting a subtree off at the left place** (the parent field is untouched). -/
theorem sib_unterbaum_aus_links {c : Int} {l l' r par : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : l p = i)
    (hlp : l' p = c) (hol : ∀ j, j ≠ p → l' j = l j) : SibF c l' r par w := by
  obtain ⟨-, hmem, -, -, -⟩ := unterbaum_aus_ok (Live' := Live) h hp hpi (fun _ h => h) hlp hol
  intro j hj
  obtain ⟨hj0, -⟩ := hmem j hj
  obtain ⟨hs1, hs2⟩ := hs j hj0
  refine ⟨fun hlt => ?_, hs2⟩
  by_cases hjp : j = p
  · subst hjp; rw [hlp] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rw [hol j hjp] at hlt ⊢; exact hs1 hlt

/-- **The same at the right place.** -/
theorem sib_unterbaum_aus_rechts {c : Int} {l r r' par : Int → Int} {w p i : Int} {Live : Int → Prop}
    (hs : SibF c l r par w) (h : BaumOkF c l r w Live) (hp : InBaum c l r w p) (hpi : r p = i)
    (hrp : r' p = c) (hor : ∀ j, j ≠ p → r' j = r j) : SibF c l r' par w := by
  obtain ⟨-, hmem, -, -, -⟩ := unterbaum_aus_rechts_ok (Live' := Live) h hp hpi (fun _ h => h) hrp hor
  intro j hj
  obtain ⟨hj0, -, -⟩ := hmem j hj
  obtain ⟨hs1, hs2⟩ := hs j hj0
  refine ⟨hs1, fun hlt => ?_⟩
  by_cases hjp : j = p
  · subst hjp; rw [hrp] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rw [hor j hjp] at hlt ⊢; exact hs2 hlt

end Gabbro.Grammatik.ArenaKette

#print axioms Gabbro.Grammatik.ArenaKette.unterbaum_aus_ok
#print axioms Gabbro.Grammatik.ArenaKette.unterbaum_aus_rechts_ok
#print axioms Gabbro.Grammatik.ArenaKette.sib_unterbaum_aus_links
#print axioms Gabbro.Grammatik.ArenaKette.sib_unterbaum_aus_rechts
