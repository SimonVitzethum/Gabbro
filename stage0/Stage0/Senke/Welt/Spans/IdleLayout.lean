module

public import Stage0.Senke.Welt.WeltAt
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Relabel the very same image layout for the logical idle extension.
    Every emitted function keeps its address. The logical idle root
    has no emitted entry point. -/
def Lay.withIdle (L : Lay D) : Lay D.mitRuhe where
  fa := fun f => f.elim 0 L.fa
  regionCells := L.regionCells
  col := L.col
  ga := L.ga
  lo := L.lo
  hi := L.hi
  tor := L.tor
  byte := L.byte
  sb := L.sb
  st := L.st
  lk := L.lk
  sye := L.sye
  lockWait := L.lockWait

theorem sumFits_mapNumbers (sigNum tabNum : Nat → Nat) (cases : List (Option Ty)) :
    sumFits (Ty.mapCases sigNum tabNum cases) = sumFits cases := by
  simp only [sumFits, Ty.mapCases_length]
  apply congrArg (fun all => decide (cases.length ≤ 256) && all)
  induction cases with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | none => simp only [Ty.mapCases, List.all_cons, ih]
    | some ty =>
      cases ty <;> simp only [Ty.mapCases, Ty.mapNumbers, List.all_cons, ih]


mutual
/-- Representation widths are invariant under renumbering of nominal
    signatures and table names. This includes nested aggregates. -/
theorem valueWords_mapNumbers (sigNum tabNum : Nat → Nat) : ∀ τ : Ty,
    valueWords (τ.mapNumbers sigNum tabNum) = valueWords τ
  | .arr τ n => by
    simp only [Ty.mapNumbers, valueWords, valueWords_mapNumbers sigNum tabNum τ]
  | .prod _ fields => by
    simp only [Ty.mapNumbers, valueWords, productWords_mapFields sigNum tabNum fields]
  | .sum cs => by
    simp only [Ty.mapNumbers, valueWords, Ty.mapCases_length, sumFits_mapNumbers,
      sumPayloadWords_mapCases sigNum tabNum cs]
  | .ptr ⟨_, _, .table _⟩ => rfl
  | .int .. | .bool | .opt .. | .why .. | .never | .fl .. | .fnptr .. | .ref .. | .str .. => rfl
termination_by structural τ => τ

theorem productWords_mapFields (sigNum tabNum : Nat → Nat) : ∀ fields : List Ty,
    productWords (Ty.mapFields sigNum tabNum fields) = productWords fields
  | [] => rfl
  | τ :: rest => by
    simp only [Ty.mapFields, productWords, valueWords_mapNumbers sigNum tabNum τ,
      productWords_mapFields sigNum tabNum rest]
termination_by structural fields => fields

theorem sumPayloadWords_mapCases (sigNum tabNum : Nat → Nat) : ∀ cs : List (Option Ty),
    sumPayloadWords (Ty.mapCases sigNum tabNum cs) = sumPayloadWords cs
  | [] => rfl
  | none :: rest => by
    simp only [Ty.mapCases, sumPayloadWords, sumPayloadWords_mapCases sigNum tabNum rest]
  | some τ :: rest => by
    simp only [Ty.mapCases, sumPayloadWords, valueWords_mapNumbers sigNum tabNum τ,
      sumPayloadWords_mapCases sigNum tabNum rest]
termination_by structural cs => cs
end

/-- Nominal numbering does not affect the storage width of a context
    or the offsets addressed by its variables. -/
theorem contextWords_mapNumbers (sigNum tabNum : Nat → Nat) (types : List Ty) :
    contextWords (types.map (fun ty => ty.mapNumbers sigNum tabNum)) = contextWords types := by
  induction types with
  | nil => rfl
  | cons ty rest ih =>
    simp only [List.map_cons, contextWords_cons, valueWords_mapNumbers, ih]

theorem returnWords_mapNumbers (sigNum tabNum : Nat → Nat) (result : Option Ty) (reasons : Nat) :
    returnWords (result.map (fun ty => ty.mapNumbers sigNum tabNum)) reasons = returnWords result reasons := by
  cases result with
  | none => rfl
  | some ty => simp only [Option.map_some, returnWords, resultWords, valueWords_mapNumbers]

theorem vslot_varR {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (reserved : Nat) :
    vslot (varR x) reserved = vslot x reserved := by
  have offset : variableOffset (varR x) = variableOffset x := by
    induction x with
    | here => exact contextWords_mapNumbers (fun n => n + 1) id _
    | there _ ih => exact ih
  simp only [vslot, offset]

theorem Lay.withIdle_elem (L : Lay D) (t : D.Tab) (f : D.Feld t) (i : Nat) :
    L.withIdle.elem t f i = L.elem t f i := by
  simp only [Lay.elem, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

theorem Lay.withIdle_count (L : Lay D) (t : D.Tab) : L.withIdle.count t = L.count t := rfl

/-- The idle root changes the names of functions while keeping the
    same physical cells and access bounds. -/
def Zelle.withIdle : Zelle D → Zelle D.mitRuhe
  | .glob g => .glob g
  | .elem t f k => .elem t f k

theorem Zelle.withIdle_adr (layout : Lay D) (cell : Zelle D) :
    cell.withIdle.adr layout.withIdle = cell.adr layout := by
  cases cell with
  | glob => rfl
  | elem table field index => exact layout.withIdle_elem table field index

theorem Zelle.withIdle_da (layout : Lay D) (cell : Zelle D) :
    cell.withIdle.da layout.withIdle ↔ cell.da layout := by
  cases cell <;> exact Iff.rfl

theorem Zelle.withIdle_bytes (cell : Zelle D) : cell.withIdle.bytes = cell.bytes := by
  cases cell <;> simp only [Zelle.withIdle, Zelle.bytes, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]

private theorem idleCell_surjective : Function.Surjective (Zelle.withIdle (D := D)) := by
  intro cell
  cases cell with
  | glob global => exact ⟨.glob global, rfl⟩
  | elem table field index => exact ⟨.elem table field index, rfl⟩

theorem LayIn.withIdle {layout : Lay D} (inside : LayIn layout) : LayIn layout.withIdle := by
  refine ⟨?_, ?_, inside.2.2⟩
  · intro table field index present
    simpa only [Lay.withIdle_elem, Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers] using
      inside.1 table field index present
  · intro global
    simpa only [Lay.withIdle, Deklaration.mitRuhe, tyR, valueWords_mapNumbers] using inside.2.1 global

theorem LayDis.withIdle {layout : Lay D} (separated : LayDis layout) : LayDis layout.withIdle := by
  constructor
  · intro left right first last distinct
    obtain ⟨a, rfl⟩ := idleCell_surjective left
    obtain ⟨b, rfl⟩ := idleCell_surjective right
    simp only [Zelle.withIdle_adr, Zelle.withIdle_bytes]
    exact separated.spans a b ((a.withIdle_da layout).mp first) ((b.withIdle_da layout).mp last)
      (fun same => distinct (congrArg Zelle.withIdle same))
  · intro left right first last same
    obtain ⟨a, rfl⟩ := idleCell_surjective left
    obtain ⟨b, rfl⟩ := idleCell_surjective right
    simp only [Zelle.withIdle_adr] at same
    exact congrArg Zelle.withIdle (separated.inj a b ((a.withIdle_da layout).mp first) ((b.withIdle_da layout).mp last) same)
  · intro cell present
    obtain ⟨original, rfl⟩ := idleCell_surjective cell
    rw [Zelle.withIdle_adr]
    exact separated.grid original ((original.withIdle_da layout).mp present)

theorem LaySync.withIdle {layout : Lay D} (locks : LaySync layout) : LaySync layout.withIdle := locks

end Gabbro.Stage0.Senke
