/- Canonical global prefix spans and typed table-column spans. Geometry is
   independent of image execution, preserving fieldless declared counts exactly. -/
module
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Stage0.Senke.Welt.WeltAt
public import Stage0.Senke.Welt.GlobalOffsets
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


/-- Every global reserves its entire canonical value span. -/
def globSz (u : UProg) (g : Fin u.globs.length) : Nat :=
  8 * valueWords ((declOf u).gtyp g)

def globsSz (u : UProg) : Nat :=
  ((List.finRange u.globs.length).map (globSz u)).sum

/-- The bytes of one column. -/
def colSz (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Nat :=
  8 * valueWords ((declOf u).typ t f) * ((declOf u).count t).toNat

/-- The bytes of one table: its columns. -/
def tabSz (u : UProg) (t : Fin u.tabs.length) : Nat :=
  ((List.finRange (fieldCount u t)).map (colSz u t)).sum

/-- Empty columns contribute no storage and have no field/cell domain.
    The original declared count is retained exactly, including large logical counts;
    the usual image and word bounds still apply to every remaining stored column. -/
theorem fieldless_table_layout (u : UProg) (t : Fin u.tabs.length)
    (h : fieldCount u t = 0) :
    (declOf u).count t = (tabAt u t).count ∧ tabSz u t = 0 ∧
      IsEmpty ((declOf u).Feld t) := by
  refine ⟨rfl, ?_, ⟨fun f => ?_⟩⟩
  · have empty : List.finRange (fieldCount u t) = [] :=
      List.length_eq_zero_iff.mp (by simpa using h)
    simp [tabSz, empty]
  · have hf : f.val < fieldCount u t := f.isLt
    omega

/-- The bytes of all tables. -/
def tabsSz (u : UProg) : Nat := ((List.finRange u.tabs.length).map (tabSz u)).sum

/-- Alignment retained by source elaboration; absent placement imposes no padding. -/
def globAlign (u : UProg) (g : Fin u.globs.length) : Nat :=
  ((globAt u g).placement.map (·.ausrichtung)).getD 1

def layU (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat)
    (align : Fin u.globs.length → Nat := globAlign u) : Lay (declOf u) where
  ga g := globStartOf (List.finRange u.globs.length) b (globSz u) align g
  col t f := globEnd (List.finRange u.globs.length) b (globSz u) align + (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum +
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum
  lo := b
  hi := globEnd (List.finRange u.globs.length) b (globSz u) align + tabsSz u
  tor := tor
  byte t := (List.finRange (fieldCount u t)).find? (fun f => decide ((declOf u).typ t f = .int 0 255))
  lk L := globEnd (List.finRange u.globs.length) b (globSz u) align + tabsSz u + 24 * L.val
  sye := globEnd (List.finRange u.globs.length) b (globSz u) align + tabsSz u + 24 * u.locks.length

/-- The words of the locks after the tables, three each. -/
theorem layU_sync (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) : LaySync (layU u tor b) := by
  refine ⟨fun Lk => ?_, fun Lk Lk' hne => ?_⟩
  · have := Lk.isLt; simp only [layU, globEnd_one, alignUp_one]; omega
  · have : Lk.val ≠ Lk'.val := fun h => hne (Fin.ext h)
    simp only [layU, globEnd_one, alignUp_one]; omega

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
    (hk : (k : Int) < (declOf u).count t) : 8 * valueWords ((declOf u).typ t f) * k + 8 * valueWords ((declOf u).typ t f) ≤ colSz u t f := by
  unfold colSz
  have hk' : k < ((declOf u).count t).toNat := by omega
  have h := Nat.mul_le_mul_left (8 * valueWords ((declOf u).typ t f)) (Nat.succ_le_of_lt hk')
  rw [Nat.mul_succ] at h
  simpa using h

theorem col_le (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) :
    (layU u tor b).col t f + colSz u t f ≤ (layU u tor b).hi := by
  simp only [layU, globEnd_one, alignUp_one, tabsSz]
  have h1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
  have h2 := take_sum_add ((List.finRange u.tabs.length).map (tabSz u)) t.val (by simp)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1 h2
  have : (((List.finRange (fieldCount u t)).map (colSz u t))).sum = tabSz u t := rfl
  omega

/-- The layout keeps every element and every global inside the world, once the world ends below `2^31`. -/
theorem layU_in (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) (h : (layU u tor b).hi < 2 ^ 31) : LayIn (layU u tor b) := by
  refine ⟨fun t f k hk => ?_, fun g => ?_, h⟩
  · simp only [Lay.count, layU, alignUp_one, Int.natCast_zero, ite_self, Int.add_zero] at hk
    have h1 := colSz_ge u t f k hk
    have h2 := col_le u tor b t f
    simp only [Lay.elem]
    constructor
    · simp only [layU, globEnd_one, alignUp_one]; omega
    · omega
  · have hg := globStarts_bounds (List.finRange u.globs.length) b (globSz u)
      (fun _ => 1) g _ (globStartOf_mem _ _ _ _ g (by simp))
    simp only [layU, globEnd_one, globSz] at *
    omega
