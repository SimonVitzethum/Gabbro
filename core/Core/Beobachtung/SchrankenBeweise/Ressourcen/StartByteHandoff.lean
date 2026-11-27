module

public import Core.Beobachtung.SchrankenBeweise.Ressourcen.StartHandoff
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Zelle)

/-- PHYSICALLY CANONICAL START ACCOUNTING. The byte footprint of all granted
    extents, independent of every typed view width: width one books one cell per
    physical byte. This is kept separate from the productive loader connection
    until the intended B21 count interface is reconciled. -/
def handoffByteFootprint (regions : List Strecke) : Nat :=
  (regions.map (fun r => r.bis - r.von)).sum

/-- At width one the live cells are exactly a grant slot together with a byte
    offset inside that grant. All granted slots are live after a successful
    load, so the width-one projection is the canonical byte footprint, and its
    `LebendeZellen.encard` is the current counter of logical cells. -/
theorem handoffBooking_byte_encard {L Wert Raum Lok Grund : Type}
    (s : Zustand L Zelle Wert Raum Lok Grund) (regions : List Strecke)
    (live : ∀ i, i < regions.length → s.rechte.lebt i = true) :
    (LebendeZellen { s with buchung := handoffBooking 1 regions s.buchung }).encard =
      handoffByteFootprint regions := by
  let foot : Fin regions.length → Nat := fun i => (regions.get i).bis - (regions.get i).von
  let idx := Sigma (fun i : Fin regions.length => Fin (foot i))
  let code : idx → Nat × Nat := fun p => (p.1.val, p.2.val)
  have code_injective : Function.Injective code := by
    intro p q h
    cases p with
    | mk pi pd =>
      cases q with
      | mk qi qd =>
        have hi : pi = qi := Fin.ext (congrArg Prod.fst h)
        subst qi
        have hd : pd = qd := Fin.ext (congrArg Prod.snd h)
        subst qd
        rfl
  have cells : LebendeZellen { s with buchung := handoffBooking 1 regions s.buchung } =
      Set.range code := by
    ext ⟨slot, offset⟩
    change (s.rechte.lebt slot = true ∧ offset < (handoffCells 1 regions slot).length) ↔
      ∃ p : idx, code p = (slot, offset)
    constructor
    · intro h
      have hslot : slot < regions.length := by
        by_contra hs
        have gnil : regions[slot]? = none := List.getElem?_eq_none (Nat.le_of_not_gt hs)
        have hlen : (handoffCells 1 regions slot).length = 0 := by
          simp only [handoffCells, gnil, List.length_nil]
        omega
      let i : Fin regions.length := ⟨slot, hslot⟩
      have g := List.getElem?_eq_getElem (l := regions) hslot
      have hlen : (handoffCells 1 regions slot).length = foot i := by
        simp only [handoffCells, g, Nat.div_one, List.length_map, List.length_range,
          List.get_eq_getElem, foot, i]
      have hoff : offset < foot i := hlen ▸ h.2
      exact ⟨⟨i, ⟨offset, hoff⟩⟩, rfl⟩
    · rintro ⟨⟨i, d⟩, hp⟩
      have hfst : i.val = slot := congrArg Prod.fst hp
      have hsnd : d.val = offset := congrArg Prod.snd hp
      subst slot
      subst offset
      have hlen : (handoffCells 1 regions i.val).length = foot i := by
        simp only [handoffCells, Fin.is_lt, getElem?_pos, Nat.div_one, List.length_map,
          List.length_range, List.get_eq_getElem, foot]
      exact ⟨live i.val i.isLt, hlen.symm ▸ d.isLt⟩
  have card : Fintype.card idx = handoffByteFootprint regions := by
    dsimp [idx]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    simpa [foot, handoffByteFootprint] using (Fin.sum_univ_fun_getElem regions (fun r : Strecke => r.bis - r.von))
  rw [cells, code_injective.encard_range, ENat.card_eq_coe_fintype_card, card]

/-- The single byte of physical storage addressed by a canonical cell. -/
def handoffByteCell (extent : Strecke) (offset : Nat) : Strecke :=
  ⟨extent.von + offset, extent.von + offset + 1⟩

/-- Two distinct canonical bytes of a grant never overlap: the physical
    interval of a grant is not charged twice by the width-one projection. -/
theorem handoffByteCell_getrennt (extent : Strecke) {u v : Nat} (uv : u ≠ v) :
    Strecke.getrennt (handoffByteCell extent u) (handoffByteCell extent v) := by
  simp only [Strecke.getrennt, handoffByteCell]
  by_cases h : u < v
  · omega
  · omega

/-- Distinct granted slots never charge the same physical byte: the existing
    disjoint-placement theorem at width one gives separation of the byte cells
    of two grants. Together with `handoffBooking_byte_encard` this makes the
    canonical charge a sum of non-overlapping footprints. -/
theorem handoffByteCell_getrennt_slots {regions : List Strecke}
    (disjoint : regions.Pairwise Strecke.getrennt)
    {booking : Sicherheit.Buchung Zelle} {i j u v : Nat} {left right : Strecke}
    (distinct : i ≠ j) (leftGrant : regions[i]? = some left)
    (rightGrant : regions[j]? = some right)
    (leftCell : ((handoffBooking 1 regions booking).umfang i)[u]? = some (.region i u))
    (rightCell : ((handoffBooking 1 regions booking).umfang j)[v]? = some (.region j v)) :
    Strecke.getrennt (handoffByteCell left u) (handoffByteCell right v) := by
  have sep := handoffBooking_disjoint (by omega) disjoint distinct leftGrant rightGrant
    leftCell rightCell
  simpa [handoffByteCell, Nat.add_assoc] using sep

/-- A physical address lies in a grant exactly when it lies in one of its
    canonical byte cells: those cells cover the grant without gaps. -/
theorem handoffByteCell_uerberdeckt (extent : Strecke) (a : Nat) :
    extent.drin a ↔ ∃ offset, offset < extent.bis - extent.von ∧
      (handoffByteCell extent offset).drin a := by
  constructor
  · intro ha
    simp only [Strecke.drin] at ha
    refine ⟨a - extent.von, by omega, by
      simp only [handoffByteCell, Strecke.drin]
      omega⟩
  · rintro ⟨offset, hoff, ha⟩
    simp only [handoffByteCell, Strecke.drin] at ha
    simp only [Strecke.drin]
    omega

/-- Every physical byte admitted by a typed view cell lies in a canonical byte
    of the same grant. This holds for every view width, so two admitted views of
    one grant share exactly the same canonical bytes. -/
theorem handoffView_cell_in_kanonisch {bytes : Nat} {extent : Strecke} {offset a : Nat}
    (cell : (⟨extent.von + offset * bytes, extent.von + (offset + 1) * bytes⟩ : Strecke).drin a) :
    ∃ b, b < (offset + 1) * bytes ∧
      (handoffByteCell extent b).drin a := by
  simp only [Strecke.drin] at cell
  refine ⟨a - extent.von, ?_, ?_⟩
  · rw [Nat.add_mul, Nat.one_mul] at cell ⊢
    omega
  · simp only [handoffByteCell, Strecke.drin]
    omega

/-- Two admitted typed views of one grant, at possibly different widths, charge
    the same single canonical byte of a shared physical address; by
    `handoffByteCell_getrennt` that byte is counted once, not once per view. -/
theorem handoff_two_views_gleicher_byte {b₁ b₂ : Nat} {extent : Strecke} {o₁ o₂ a : Nat}
    (in₁ : extent.enthaelt ⟨extent.von + o₁ * b₁, extent.von + (o₁ + 1) * b₁⟩)
    (c₁ : (⟨extent.von + o₁ * b₁, extent.von + (o₁ + 1) * b₁⟩ : Strecke).drin a)
    (c₂ : (⟨extent.von + o₂ * b₂, extent.von + (o₂ + 1) * b₂⟩ : Strecke).drin a) :
    ∃ b, b < extent.bis - extent.von ∧ (handoffByteCell extent b).drin a := by
  simp only [Strecke.enthaelt] at in₁
  simp only [Strecke.drin] at c₁ c₂
  refine ⟨a - extent.von, ?_, ?_⟩
  · omega
  · simp only [handoffByteCell, Strecke.drin]
    omega

/-- Exact relation of the canonical byte charge to the B21 logical-cell counter:
    a view of width `bytes` charges `footprint / bytes` cells of `bytes` bytes,
    which never exceeds the footprint and equals it only for a complete view.
    The canonical width-one charge is the footprint itself. -/
theorem handoff_view_count_relation {bytes : Nat} (positive : 0 < bytes) (extent : Strecke) :
    ((extent.bis - extent.von) / bytes) * bytes ≤ extent.bis - extent.von ∧
    (((extent.bis - extent.von) / bytes) * bytes = extent.bis - extent.von ↔
      (extent.bis - extent.von) % bytes = 0) := by
  let footprint := extent.bis - extent.von
  change footprint / bytes * bytes ≤ footprint ∧
    (footprint / bytes * bytes = footprint ↔ footprint % bytes = 0)
  have decomp : footprint = (footprint / bytes) * bytes + footprint % bytes := (Nat.div_add_mod' footprint bytes).symm
  constructor
  · exact Nat.div_mul_le_self footprint bytes
  · constructor <;> intro h <;> omega

end Gabbro.Core.Beobachtung
