module

public import Core.Beobachtung.SchrankenBeweise.Ressourcen.BindungEndlich

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ziel.Korrektheit (einheitVon)

/-- Complete logical cells in a physical handoff, for an explicitly supplied
    storage width in bytes. A trailing partial cell is unusable. -/
def handoffCells (bytes : Nat) (regions : List Strecke) (slot : Nat) : List Zelle :=
  match regions[slot]? with
  | none => []
  | some extent => (List.range ((extent.bis - extent.von) / bytes)).map (.region slot)

/-- The same extent projection consumed by the access and live-cell rules.
    Boot metadata and all authority fields are kept by the caller. -/
def handoffBooking (bytes : Nat) (regions : List Strecke) (booking : Sicherheit.Buchung Zelle) :
    Sicherheit.Buchung Zelle :=
  { booking with umfang := handoffCells bytes regions }

theorem handoffBooking_nil (bytes : Nat) :
    handoffBooking bytes [] Sicherheit.Buchung.leer = Sicherheit.Buchung.leer := rfl

/-- At a granted slot, the ledger lookup is exactly the source cell of that
    slot and logical offset, provided the complete cell fits in the grant. -/
theorem handoffBooking_lookup (bytes : Nat) (regions : List Strecke)
    (booking : Sicherheit.Buchung Zelle) {slot offset : Nat} {extent : Strecke}
    (grant : regions[slot]? = some extent) :
    ((handoffBooking bytes regions booking).umfang slot)[offset]? =
      some (.region slot offset) ↔ offset < (extent.bis - extent.von) / bytes := by
  change (handoffCells bytes regions slot)[offset]? = _ ↔ _
  rw [handoffCells, grant]
  constructor
  · intro h
    have bound := (List.getElem?_eq_some_iff.mp h).1
    simpa only [List.length_map, List.length_range] using bound
  · intro h
    simp only [List.getElem?_map, List.getElem?_range h, Option.map_some]

/-- The ledger's logical offset denotes a complete physical subextent of the
    grant. The positive layout width and the grant's actual endpoints determine
    that subextent. -/
theorem handoffBooking_inside {bytes : Nat} (positive : 0 < bytes) {regions : List Strecke}
    {booking : Sicherheit.Buchung Zelle} {slot offset : Nat} {extent : Strecke}
    (grant : regions[slot]? = some extent)
    (booked : ((handoffBooking bytes regions booking).umfang slot)[offset]? =
      some (.region slot offset)) :
    extent.enthaelt ⟨extent.von + offset * bytes, extent.von + (offset + 1) * bytes⟩ := by
  have fits := (handoffBooking_lookup bytes regions booking grant).mp booked
  have last : (offset + 1) * bytes ≤ extent.bis - extent.von :=
    (Nat.le_div_iff_mul_le positive).mp (Nat.succ_le_of_lt fits)
  have growth : offset * bytes < (offset + 1) * bytes := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have extentPositive : extent.von < extent.bis := by
    have : bytes ≤ (offset + 1) * bytes := by rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  change extent.von ≤ extent.von + offset * bytes ∧
    extent.von + offset * bytes < extent.von + (offset + 1) * bytes ∧
    extent.von + (offset + 1) * bytes ≤ extent.bis
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left growth _, by omega⟩

/-- Distinct slots in the admitted handoff assign disjoint physical storage
    to the logical cells recorded in the ledger. -/
theorem handoffBooking_disjoint {bytes : Nat} (positive : 0 < bytes)
    {regions : List Strecke} (disjoint : regions.Pairwise Strecke.getrennt)
    {booking : Sicherheit.Buchung Zelle} {i j u v : Nat} {left right : Strecke}
    (distinct : i ≠ j) (leftGrant : regions[i]? = some left)
    (rightGrant : regions[j]? = some right)
    (leftCell : ((handoffBooking bytes regions booking).umfang i)[u]? = some (.region i u))
    (rightCell : ((handoffBooking bytes regions booking).umfang j)[v]? = some (.region j v)) :
    Strecke.getrennt ⟨left.von + u * bytes, left.von + (u + 1) * bytes⟩
      ⟨right.von + v * bytes, right.von + (v + 1) * bytes⟩ := by
  obtain ⟨hi, hleft⟩ := List.getElem?_eq_some_iff.mp leftGrant
  obtain ⟨hj, hright⟩ := List.getElem?_eq_some_iff.mp rightGrant
  have grants : left.getrennt right := by
    rw [← hleft, ← hright]
    by_cases before : i < j
    · exact disjoint.rel_getElem_of_lt hi hj before
    · exact Strecke.getrennt_symm (disjoint.rel_getElem_of_lt hj hi (by omega))
  obtain ⟨beginL, _, endL⟩ := handoffBooking_inside positive leftGrant leftCell
  obtain ⟨beginR, _, endR⟩ := handoffBooking_inside positive rightGrant rightCell
  exact grants.elim
    (fun h => Or.inl (endL.trans (h.trans beginR)))
    (fun h => Or.inr (endR.trans (h.trans beginL)))

/-- An installed single grant at the live boot slot contributes exactly its
    complete cells to B21. A grant at least one cell wide gives a positive count. -/
theorem handoffBooking_single_encard {L Wert Raum Lok Grund : Type}
    (s : Zustand L Zelle Wert Raum Lok Grund) (bytes : Nat) (extent : Strecke)
    (live : s.rechte.lebt 0 = true) :
    (LebendeZellen { s with buchung := handoffBooking bytes [extent] s.buchung }).encard =
      ((extent.bis - extent.von) / bytes : Nat) := by
  let count := (extent.bis - extent.von) / bytes
  let index : Fin count → Nat × Nat := fun i => (0, i.val)
  have range : LebendeZellen { s with buchung := handoffBooking bytes [extent] s.buchung } =
      Set.range index := by
    ext ⟨slot, offset⟩
    cases slot with
    | zero =>
      change (s.rechte.lebt 0 = true ∧ offset < ((List.range count).map (Zelle.region 0)).length) ↔ _
      simp only [live, true_and, List.length_map, List.length_range]
      exact ⟨fun h => ⟨⟨offset, h⟩, rfl⟩, by
        rintro ⟨i, hi⟩
        have hval : i.val = offset := congrArg Prod.snd hi
        exact hval ▸ i.isLt⟩
    | succ slot =>
      change (s.rechte.lebt (slot + 1) = true ∧ offset < ([] : List Zelle).length) ↔ _
      refine ⟨fun h => (Nat.not_lt_zero _ h.2).elim, ?_⟩
      rintro ⟨i, hi⟩
      exact (Nat.noConfusion (congrArg Prod.fst hi) : False).elim
  have injective : Function.Injective index := fun _ _ h => Fin.ext (congrArg Prod.snd h)
  rw [range, injective.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- Applying the proposed booking to a successful source load with one grant
    supplies the exact finite start count from the already-live boot slot. -/
theorem quellladen_handoff_single_encard (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s)
    (bytes : Nat) {extent : Strecke} (grant : a.regions = [extent]) :
    (LebendeZellen { s with buchung := handoffBooking bytes a.regions s.buchung }).encard =
      ((extent.bis - extent.von) / bytes : Nat) := by
  rw [grant]
  have within : 0 < a.regions.length := by rw [grant]; exact Nat.zero_lt_succ 0
  exact handoffBooking_single_encard s bytes extent
    (geladeneRegion_lebt_leer P u a p geladen 0 within).1

end Gabbro.Core.Beobachtung
