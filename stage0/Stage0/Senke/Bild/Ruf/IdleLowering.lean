module

public import Stage0.Senke.Funktion
public import Stage0.Senke.Welt.Spans.IdleLayout
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

private theorem entryIndex_ruE :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ),
      entryIndex (ruE expr) = entryIndex expr
  | _, _, _, .widen _ _ expr => entryIndex_ruE expr
  | _, _, _, .neg expr => congrArg (fun i => i.map Int.neg) (entryIndex_ruE expr)
  | _, _, _, .add left right =>
    kongr₂ (fun a b => a.bind (fun i => b.map (i + ·))) (entryIndex_ruE left) (entryIndex_ruE right)
  | _, _, _, .sub left right =>
    kongr₂ (fun a b => a.bind (fun i => b.map (i - ·))) (entryIndex_ruE left) (entryIndex_ruE right)
  | _, _, _, .mul left right =>
    kongr₂ (fun a b => a.bind (fun i => b.map (i * ·))) (entryIndex_ruE left) (entryIndex_ruE right)
  | _, _, _, .lit .. | _, _, _, .tru .. | _, _, _, .fls ..
  | _, _, _, .var .. | _, _, _, .glob .. | _, _, _, .slot ..
  | _, _, _, .thru .. | _, _, _, .thruOwn .. | _, _, _, .ptrOf ..
  | _, _, _, .fnref .. | _, _, _, .refEq .. | _, _, _, .slotRef ..
  | _, _, _, .oldG .. | _, _, _, .oldS .. | _, _, _, .div ..
  | _, _, _, .rem .. | _, _, _, .sdiv .. | _, _, _, .srem ..
  | _, _, _, .getBytes .. | _, _, _, .band .. | _, _, _, .bor ..
  | _, _, _, .bxor .. | _, _, _, .shl .. | _, _, _, .shr ..
  | _, _, _, .lt .. | _, _, _, .le .. | _, _, _, .eq ..
  | _, _, _, .fllt .. | _, _, _, .flle .. | _, _, _, .and ..
  | _, _, _, .or .. | _, _, _, .not .. | _, _, _, .none ..
  | _, _, _, .some .. | _, _, _, .istSome .. | _, _, _, .case ..
  | _, _, _, .why .. | _, _, _, .forallSlots .. | _, _, _, .existsSlots ..
  | _, _, _, .reaches .. | _, _, _, .arrNil .. | _, _, _, .arrCons ..
  | _, _, _, .arrGet .. | _, _, _, .arrSet .. | _, _, _, .strLit ..
  | _, _, _, .strLen .. | _, _, _, .strCat .. | _, _, _, .strGet ..
  | _, _, _, .strEq .. | _, _, _, .strLt .. | _, _, _, .strWeit ..
  | _, _, _, .wenn .. | _, _, _, .eng .. | _, _, _, .intBuiltin1 ..
  | _, _, _, .intBuiltin2 .. | _, _, _, .count .. | _, _, _, .prod ..
  | _, _, _, .prodGet .. | _, _, _, .prodSet .. => rfl
termination_by structural _ _ _ expr => expr

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
theorem oldCells_ruE :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ),
      oldCells (ruE expr) = (oldCells expr).map Zelle.withIdle
  | _, _, _, .oldS table field index _ => by
    simp only [ruE, oldCells]
    with_unfolding_all rw [entryIndex_ruE index]
    cases entryIndex index with
    | some _ => rfl
    | none =>
      rw [idleColumnFits (D := D) table field]
      with_unfolding_all rw [oldCells_ruE index, idleColumn (D := D) table field 0 (D.count table).toNat]
      split <;> simp only [List.map_append, List.map_nil]
  | _, _, _, .widen _ _ expr | _, _, _, .not expr | _, _, _, .neg expr | _, _, _, .intBuiltin1 _ expr =>
    oldCells_ruE expr
  | _, _, _, .add left right | _, _, _, .sub left right | _, _, _, .mul left right
  | _, _, _, .eq left right | _, _, _, .lt left right | _, _, _, .le left right
  | _, _, _, .and left right | _, _, _, .or left right | _, _, _, .intBuiltin2 _ left right => by
    simpa only [ruE, oldCells, List.map_append] using
      kongr₂ (· ++ ·) (oldCells_ruE left) (oldCells_ruE right)
  | _, _, _, .lit .. | _, _, _, .tru .. | _, _, _, .fls ..
  | _, _, _, .var .. | _, _, _, .glob .. | _, _, _, .slot ..
  | _, _, _, .thru .. | _, _, _, .thruOwn .. | _, _, _, .ptrOf ..
  | _, _, _, .fnref .. | _, _, _, .refEq .. | _, _, _, .slotRef ..
  | _, _, _, .oldG .. | _, _, _, .div .. | _, _, _, .rem ..
  | _, _, _, .sdiv .. | _, _, _, .srem .. | _, _, _, .getBytes ..
  | _, _, _, .band .. | _, _, _, .bor .. | _, _, _, .bxor ..
  | _, _, _, .shl .. | _, _, _, .shr .. | _, _, _, .fllt ..
  | _, _, _, .flle .. | _, _, _, .none .. | _, _, _, .some ..
  | _, _, _, .istSome .. | _, _, _, .case .. | _, _, _, .why ..
  | _, _, _, .forallSlots .. | _, _, _, .existsSlots .. | _, _, _, .reaches ..
  | _, _, _, .arrNil .. | _, _, _, .arrCons .. | _, _, _, .arrGet ..
  | _, _, _, .arrSet .. | _, _, _, .strLit .. | _, _, _, .strLen ..
  | _, _, _, .strCat .. | _, _, _, .strGet .. | _, _, _, .strEq ..
  | _, _, _, .strLt .. | _, _, _, .strWeit .. | _, _, _, .wenn ..
  | _, _, _, .eng .. | _, _, _, .count .. | _, _, _, .prod ..
  | _, _, _, .prodGet .. | _, _, _, .prodSet .. => rfl
termination_by structural _ _ _ expr => expr

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
