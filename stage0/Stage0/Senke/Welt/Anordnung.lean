/-
  File:      stage0/Stage0/Senke/Welt/Anordnung.lean
  Subject:   The world layout of an elaborated program (`layU u b`): from byte `b` every global one word, then every
             column of every table, its elements one after the other (a byte or a word each, `stride`), padded to
             whole words and one word more, so the word read at its last element stays inside (`layU_in`).
-/
import Grammatik.Parser.Elab.UebersetzeAllg
import Stage0.Senke.Welt.WeltAt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The bytes of one column. -/
def colSz (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Nat :=
  (stride (D := declOf u) t f * ((declOf u).count t).toNat + 7) / 8 * 8 + 8

/-- The bytes of one table: its columns. -/
def tabSz (u : UProg) (t : Fin u.tabs.length) : Nat :=
  ((List.finRange (fieldCount u t)).map (colSz u t)).sum

/-- The bytes of all tables. -/
def tabsSz (u : UProg) : Nat := ((List.finRange u.tabs.length).map (tabSz u)).sum

def layU (u : UProg) (b : Nat) : Lay (declOf u) where
  ga g := b + 8 * g.val
  col t f := b + 8 * u.globs.length + (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum +
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum
  lo := b
  hi := b + 8 * u.globs.length + tabsSz u

/-- A part of a sum and the next summand lie inside the sum. -/
theorem take_sum_add (xs : List Nat) (i : Nat) (hi : i < xs.length) : (xs.take i).sum + xs[i] ≤ xs.sum := by
  have h := List.take_append_drop (i + 1) xs
  have e : (xs.take (i + 1)).sum = (xs.take i).sum + xs[i] := by
    rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem hi]; simp
  have : (xs.take (i + 1)).sum ≤ xs.sum := by
    conv => rhs; rw [← h]
    rw [List.sum_append]; omega
  omega

theorem colSz_ge (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Nat)
    (hk : (k : Int) < (declOf u).count t) : stride (D := declOf u) t f * k + 8 ≤ colSz u t f := by
  unfold colSz
  have hs : stride (D := declOf u) t f = 1 ∨ stride (D := declOf u) t f = 8 := by
    unfold stride; split <;> simp
  have hk' : k < ((declOf u).count t).toNat := by omega
  rcases hs with h | h <;> rw [h] <;> omega

theorem col_le (u : UProg) (b : Nat) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) :
    (layU u b).col t f + colSz u t f ≤ (layU u b).hi := by
  simp only [layU, tabsSz]
  have h1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
  have h2 := take_sum_add ((List.finRange u.tabs.length).map (tabSz u)) t.val (by simp)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1 h2
  have : (((List.finRange (fieldCount u t)).map (colSz u t))).sum = tabSz u t := rfl
  omega

/-- The layout keeps every element and every global inside the world, once the world ends below `2^31`. -/
theorem layU_in (u : UProg) (b : Nat) (h : (layU u b).hi < 2 ^ 31) : LayIn (layU u b) := by
  refine ⟨fun t f k hk => ?_, fun g => ?_, h⟩
  · have h1 := colSz_ge u t f k hk
    have h2 := col_le u b t f
    simp only [Lay.elem]
    constructor
    · simp only [layU]; omega
    · omega
  · have := g.isLt
    simp only [layU, tabsSz]
    omega

end Gabbro.Stage0.Senke
