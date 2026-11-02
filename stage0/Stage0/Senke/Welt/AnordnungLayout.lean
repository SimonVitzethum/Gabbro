/- Canonical global prefix spans and typed table-column spans. Geometry is
   independent of image execution, preserving fieldless declared counts exactly. -/
module
public import Stage0.Senke.Welt.AnordnungLayouta
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Stage0.Senke.Welt.WeltAt
public import Mathlib.Basic.IsEmpty.Defs
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

set_option linter.unusedSectionVars false


theorem take_sum_lt (xs : List Nat) (i j : Nat) (hij : i < j) (hi : i < xs.length) :
    (xs.take i).sum + xs[i] ≤ (xs.take j).sum := by
  have e : (xs.take (i + 1)).sum = (xs.take i).sum + xs[i] := by
    rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem hi]; simp
  have := take_sum_mono xs (i + 1) j hij
  omega

/-- A number in the stretch of summand `i` and in the stretch of summand `j`: `i = j`. -/
theorem stretch_eq (xs : List Nat) (i j x : Nat) (hi : i < xs.length) (hj : j < xs.length)
    (h1 : (xs.take i).sum ≤ x) (h2 : x < (xs.take i).sum + xs[i])
    (h3 : (xs.take j).sum ≤ x) (h4 : x < (xs.take j).sum + xs[j]) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := take_sum_lt xs i j h hi; omega
  · exact h
  · have := take_sum_lt xs j i h hj; omega

theorem sum_mul8 : (xs : List Nat) → (∀ x ∈ xs, x % 8 = 0) → xs.sum % 8 = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.sum_cons]
    have := h x (by simp)
    have := sum_mul8 xs (fun y hy => h y (by simp [hy]))
    omega

theorem take_mul8 (xs : List Nat) (h : ∀ x ∈ xs, x % 8 = 0) (i : Nat) : (xs.take i).sum % 8 = 0 :=
  sum_mul8 _ (fun x hx => h x (List.mem_of_mem_take hx))

theorem tabSz_mul8 (u : UProg) (t : Fin u.tabs.length) : tabSz u t % 8 = 0 :=
  sum_mul8 _ (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨f, _, rfl⟩ := hx
    simp [colSz, Nat.mul_assoc])

/-- The offset of element `k` of column `f` inside its table lies in the table. -/
theorem in_tab (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Nat)
    (hk : (k : Int) < (declOf u).count t) :
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum + 8 * valueWords ((declOf u).typ t f) * k < tabSz u t := by
  have h1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1
  have := colSz_ge u t f k hk
  have positive := valueWords_pos ((declOf u).typ t f)
  have e : (((List.finRange (fieldCount u t)).map (colSz u t))).sum = tabSz u t := rfl
  omega

/-- Different canonical cells occupy disjoint complete byte spans. -/
theorem layU_spans (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat)
    (c c' : Zelle (declOf u)) (hc : c.da (layU u tor b)) (hc' : c'.da (layU u tor b))
    (hne : c ≠ c') : c.adr (layU u tor b) + c.bytes ≤ c'.adr (layU u tor b) ∨
      c'.adr (layU u tor b) + c'.bytes ≤ c.adr (layU u tor b) := by
  by_cases left : c.adr (layU u tor b) + c.bytes ≤ c'.adr (layU u tor b)
  · exact Or.inl left
  apply Or.inr
  by_cases right : c'.adr (layU u tor b) + c'.bytes ≤ c.adr (layU u tor b)
  · exact right
  exfalso
  have overlap1 : c'.adr (layU u tor b) < c.adr (layU u tor b) + c.bytes := by omega
  have overlap2 : c.adr (layU u tor b) < c'.adr (layU u tor b) + c'.bytes := by omega
  have positive : ∀ cell : Zelle (declOf u), 0 < cell.bytes := by
    intro cell; cases cell with
    | glob g => exact Nat.mul_pos (by decide) (valueWords_pos _)
    | elem t f k => exact Nat.mul_pos (by decide) (valueWords_pos _)
  have pos1 := positive c
  have pos2 := positive c'
  let x := max (c.adr (layU u tor b)) (c'.adr (layU u tor b))
  have x1 : c.adr (layU u tor b) ≤ x ∧ x < c.adr (layU u tor b) + c.bytes := by
    dsimp [x]; omega
  have x2 : c'.adr (layU u tor b) ≤ x ∧ x < c'.adr (layU u tor b) + c'.bytes := by
    dsimp [x]; omega
  apply hne
  cases c with
  | glob g =>
    change Fin u.globs.length at g
    cases c' with
    | glob g' =>
      change Fin u.globs.length at g'
      by_cases eq : g = g'
      · subst g'; rfl
      · have sep := globStarts_disjoint (List.finRange u.globs.length) 0 (globSz u)
          (fun g => wordAlign (globAlign u g)) g g' _ _
          (globStartOf_mem _ _ _ _ g (by simp))
          (globStartOf_mem _ _ _ _ g' (by simp)) eq
        simp only [Zelle.adr, Zelle.bytes, layU] at x1 x2
        simp only [globSz] at sep
        rcases sep with sep | sep <;> omega
    | elem t f k =>
      have hg := (globStarts_bounds (List.finRange u.globs.length) 0 (globSz u)
        (fun g => wordAlign (globAlign u g)) g _
        (globStartOf_mem _ _ _ _ g (by simp))).2
      simp only [globSz] at hg
      simp only [Zelle.adr, Zelle.bytes, Lay.elem, layU, alignUp_one] at x1 x2
      omega
  | elem t f k =>
    change Fin u.tabs.length at t
    change Fin (fieldCount u t) at f
    cases c' with
    | glob g =>
      change Fin u.globs.length at g
      have hg := (globStarts_bounds (List.finRange u.globs.length) 0 (globSz u)
        (fun g => wordAlign (globAlign u g)) g _
        (globStartOf_mem _ _ _ _ g (by simp))).2
      simp only [globSz] at hg
      simp only [Zelle.adr, Zelle.bytes, Lay.elem, layU, alignUp_one] at x1 x2
      omega
    | elem t' f' k' =>
      change Fin u.tabs.length at t'
      change Fin (fieldCount u t') at f'
      simp only [Zelle.da, Lay.count, layU, alignUp_one, Int.natCast_zero, ite_self, Int.add_zero] at hc hc'
      have col1 := colSz_ge u t f k hc
      have col2 := colSz_ge u t' f' k' hc'
      have sum1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
      have sum2 := take_sum_add ((List.finRange (fieldCount u t')).map (colSz u t')) f'.val (by simp)
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at sum1 sum2
      change (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum + colSz u t f ≤ tabSz u t at sum1
      change (((List.finRange (fieldCount u t')).map (colSz u t')).take f'.val).sum + colSz u t' f' ≤ tabSz u t' at sum2
      simp only [Zelle.adr, Zelle.bytes, Lay.elem, layU, alignUp_one] at x1 x2
      have ht : t.val = t'.val := stretch_eq ((List.finRange u.tabs.length).map (tabSz u)) t.val t'.val
        (x - (b + globEnd (List.finRange u.globs.length) 0 (globSz u)
          (fun g => wordAlign (globAlign u g)))) (by simp) (by simp)
        (by omega) (by simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]; change _ < _ + tabSz u t; omega)
        (by omega) (by simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]; change _ < _ + tabSz u t'; omega)
      have eqt : t = t' := Fin.ext ht
      subst t'
      have hf : f.val = f'.val := stretch_eq ((List.finRange (fieldCount u t)).map (colSz u t)) f.val f'.val
        (x - (b + globEnd (List.finRange u.globs.length) 0 (globSz u)
          (fun g => wordAlign (globAlign u g)) + (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum))
        (by simp) (by simp) (by omega) (by simp; omega) (by omega) (by simp; omega)
      have eqf : f = f' := Fin.ext hf
      subst f'
      have eqk : k = k' := by
        rcases Nat.lt_trichotomy k k' with lt | eq | gt
        · have h := Nat.mul_le_mul_left (8 * valueWords ((declOf u).typ t f)) lt
          rw [Nat.mul_succ] at h
          omega
        · exact eq
        · have h := Nat.mul_le_mul_left (8 * valueWords ((declOf u).typ t f)) gt
          rw [Nat.mul_succ] at h
          omega
      subst k'
      rfl

/-- Full-span separation plus the common eight-byte storage grid. -/
theorem layU_dis (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) :
    LayDis (layU u tor b) := by
  refine ⟨layU_spans u tor b, ?_, ?_⟩
  · intro c c' hc hc' eq
    by_cases same : c = c'
    · exact same
    have sep := layU_spans u tor b c c' hc hc' same
    have positive : ∀ cell : Zelle (declOf u), 0 < cell.bytes := by
      intro cell; cases cell with
      | glob g => exact Nat.mul_pos (by decide) (valueWords_pos _)
      | elem t f k => exact Nat.mul_pos (by decide) (valueWords_pos _)
    have := positive c
    have := positive c'
    omega
  · intro c hc
    have globals : ∀ x ∈ ((List.finRange u.globs.length).map (globSz u)), x % 8 = 0 := by
      intro x hx
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      simp [globSz]
    cases c with
    | glob g =>
      have hg := Nat.dvd_iff_mod_eq_zero.mp ((glob_grid
        (List.finRange u.globs.length) 0 (globSz u) (globAlign u) (by simp)
        (by intro g; simp [globSz])).1 g _
        (globStartOf_mem _ _ _ _ g (by simp)))
      simp [Zelle.adr, layU, alignUp_one, Nat.add_mod, hg]
    | elem t f k =>
      have hg := Nat.dvd_iff_mod_eq_zero.mp ((glob_grid
        (List.finRange u.globs.length) 0 (globSz u) (globAlign u) (by simp)
        (by intro g; simp [globSz])).2)
      have ht := take_mul8 ((List.finRange u.tabs.length).map (tabSz u))
        (by intro x hx; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx; exact tabSz_mul8 u t) t.val
      have hf := take_mul8 ((List.finRange (fieldCount u t)).map (colSz u t))
        (by intro x hx; obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx; simp [colSz, Nat.mul_assoc]) f.val
      simp [Zelle.adr, Lay.elem, layU, alignUp_one, globsSz, Nat.add_mod, Nat.mul_assoc, hg, ht, hf]

end Gabbro.Stage0.Senke
