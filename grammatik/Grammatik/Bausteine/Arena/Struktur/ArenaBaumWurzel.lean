/-
  File:      Grammatik/ArenaBaumWurzel.lean
  Subject:   THE ROOT MOVES OF THE BINARY TREE, abstractly (PLAN-DYNAMIC.md section 8a.1, third pass): the first node
             goes in (`wurzel_ein_ok`: the tree was empty, the root is a fresh leaf) and the last one goes out
             (`wurzel_aus_ok`: the tree becomes empty). Without them no body could ever build a tree from nothing: a
             leaf in (`einfuegen_ok`) needs a member to hang below.

  `InBaum.wurzel` says a non-empty tree has its root among its members; it is what distinguishes the slot a root cut
  releases from every slot a body holds that is not in the tree.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaBaum

namespace Gabbro.Grammatik.ArenaKette

/-- The root of a non-empty tree is a member. -/
theorem InBaum.wurzel {c : Int} {l r : Int → Int} {w : Int} {Live : Int → Prop}
    (h : BaumOkF c l r w Live) (hw : w < c) : InBaum c l r w w := by
  obtain ⟨S, hb, -, -⟩ := h
  refine ⟨S, hb, ?_⟩
  cases hb with
  | nil => exact absurd hw (Int.lt_irrefl _)
  | node _ _ _ S1 S2 _ _ => exact List.mem_cons_self

/-- **The first node:** a live slot `i` whose two child places are empty is a tree by itself; its members are exactly
    `{i}`. -/
theorem wurzel_ein_ok {c : Int} {l' r' : Int → Int} {Live' : Int → Prop} {i : Int}
    (h0i : 0 ≤ i) (hi : i < c) (hlive : Live' i) (hli : l' i = c) (hri : r' i = c) :
    BaumOkF c l' r' i Live' ∧ ∀ j, InBaum c l' r' i j ↔ j = i := by
  have hb : BaumF c l' r' i [i] := by
    have := BaumF.node (l := l') (r := r') i h0i hi [] [] (by rw [hli]; exact BaumF.nil)
      (by rw [hri]; exact BaumF.nil)
    simpa using this
  refine ⟨⟨[i], hb, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · intro j hj
    have : j = i := by simpa using hj
    subst this
    exact hlive
  · rintro ⟨S, hS, hm⟩
    have := BaumF.eindeutig hS hb
    subst this
    simpa using hm
  · rintro rfl
    exact ⟨[j], hb, by simp⟩

/-- **The last node:** with the root set to the nil marker the tree is empty; it has no member. -/
theorem wurzel_aus_ok {c : Int} {l r : Int → Int} {Live : Int → Prop} :
    BaumOkF c l r c Live ∧ ∀ j, ¬ InBaum c l r c j := by
  refine ⟨baumOkF_leer c l r Live, ?_⟩
  rintro j ⟨S, hS, hm⟩
  have := hS.leer
  subst this
  simp at hm

end Gabbro.Grammatik.ArenaKette

#print axioms Gabbro.Grammatik.ArenaKette.InBaum.wurzel
#print axioms Gabbro.Grammatik.ArenaKette.wurzel_ein_ok
#print axioms Gabbro.Grammatik.ArenaKette.wurzel_aus_ok
