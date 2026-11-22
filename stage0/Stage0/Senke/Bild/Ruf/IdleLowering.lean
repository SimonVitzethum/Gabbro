module

public import Stage0.Senke.Funktion
public import Stage0.Senke.Welt.Spans.IdleLayout
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

private theorem entryIndex_ruE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ) :
    entryIndex (ruE expr) = entryIndex expr := by
  cases expr with
  | widen _ _ expr => exact entryIndex_ruE expr
  | neg expr =>
    simp only [ruE, entryIndex]
    rw [entryIndex_ruE expr]
  | add left right | sub left right | mul left right =>
    simp only [ruE, entryIndex]
    rw [entryIndex_ruE left, entryIndex_ruE right]
  | _ => rfl
termination_by sizeOf expr
decreasing_by all_goals simp_wf <;> omega

private theorem idleColumn (table : D.Tab) (field : D.Feld table) (first count : Nat) :
    EntrySnapshots.column (D := D.mitRuhe) table field first count =
      (EntrySnapshots.column (D := D) table field first count).map Zelle.withIdle := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => simp only [EntrySnapshots.column, List.map_cons, Zelle.withIdle, ih]

private theorem idleColumnFits (table : D.Tab) (field : D.Feld table) :
    EntrySnapshots.columnFits (D := D.mitRuhe) table field = EntrySnapshots.columnFits (D := D) table field := by
  simp only [EntrySnapshots.columnFits, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

/-- The original and idle-extended postconditions capture the same
    entry cells in the same order, including dynamic columns. -/
theorem oldCells_ruE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ) :
    oldCells (ruE expr) = (oldCells expr).map Zelle.withIdle := by
  cases expr with
  | oldS table field index _ =>
    simp only [ruE, oldCells]
    rw [entryIndex_ruE index]
    cases entryIndex index with
    | some _ => rfl
    | none =>
      rw [idleColumnFits (D := D) table field]
      rw [oldCells_ruE index, idleColumn (D := D) table field 0 (D.count table).toNat]
      split <;> simp only [List.map_append, List.map_nil]
  | widen _ _ expr | not expr | neg expr | intBuiltin1 _ expr =>
    exact oldCells_ruE expr
  | add left right | sub left right | mul left right | eq left right | lt left right | le left right
  | and left right | or left right | intBuiltin2 _ left right =>
    simp only [ruE, oldCells, List.map_append]
    rw [oldCells_ruE left, oldCells_ruE right]
  | _ => rfl
termination_by sizeOf expr
decreasing_by all_goals simp_wf <;> omega

/-- Renaming the source functions leaves the stored spans and their
    emitted entry loads byte-for-byte identical. -/
theorem EntrySnapshots.withIdle (layout : Lay D) (cells : List (Zelle D)) (base : Nat) :
    EntrySnapshots.words (cells.map Zelle.withIdle) = EntrySnapshots.words cells ∧
      EntrySnapshots.capture layout.withIdle (cells.map Zelle.withIdle) base =
        EntrySnapshots.capture layout cells base := by
  induction cells generalizing base with
  | nil => exact ⟨rfl, rfl⟩
  | cons cell rest ih =>
    have width : valueWords cell.withIdle.ty = valueWords cell.ty := by
      cases cell <;> simp only [Zelle.withIdle, Zelle.ty, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, EntrySnapshots.words, width, (ih base).1]
    · simp only [List.map_cons, EntrySnapshots.capture, width, Zelle.withIdle_adr, (ih _).2] <;>
        cases cell <;> rfl

end Gabbro.Stage0.Senke
