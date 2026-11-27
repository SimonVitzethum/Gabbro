module

public import Core.Beobachtung.SchrankenBeweise.Ressourcen.BindungEndlich
import Mathlib.Algebra.BigOperators.Fin

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

/-- STATIC CONSISTENCY, FIRST HALF. A layout returned by the target table always
    carries a strictly positive checked byte width: the accepted widths are
    8, 16, 32 and 64 bits. This is the only width a view may contribute. -/
theorem layout_positive_bytes (target : ZielDaten) (written : Gabbro.Core.Ast.WrittenType) (shape : Gabbro.Core.Ast.LowLevel.Layout)
    (h : Gabbro.Core.Ast.LowLevel.layout target written = some shape) : 0 < shape.bytes := by
  cases written with
  | integer signed width range =>
      simp only [Gabbro.Core.Ast.LowLevel.layout] at h
      split at h
      · rename_i cond
        injection h with hs
        subst shape
        change 0 < width / 8
        have widths : width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64 := by
          simpa using cond.1
        rcases widths with rfl | rfl | rfl | rfl <;> decide
      · cases h
  | _ =>
      simp only [Gabbro.Core.Ast.LowLevel.layout] at h
      cases h

/-- STATIC CONSISTENCY, SECOND HALF. For a fixed target and written type the
    layout is a function: two successful resolutions give the same shape, hence
    the same width. No second width can be smuggled in for the same type. -/
theorem layout_unique (target : ZielDaten) (written : Gabbro.Core.Ast.WrittenType) (s t : Gabbro.Core.Ast.LowLevel.Layout)
    (hs : Gabbro.Core.Ast.LowLevel.layout target written = some s)
    (ht : Gabbro.Core.Ast.LowLevel.layout target written = some t) : s = t := by
  rw [hs] at ht
  exact Option.some.inj ht

theorem layout_bytes_unique (target : ZielDaten) (written : Gabbro.Core.Ast.WrittenType) (s t : Gabbro.Core.Ast.LowLevel.Layout)
    (hs : Gabbro.Core.Ast.LowLevel.layout target written = some s)
    (ht : Gabbro.Core.Ast.LowLevel.layout target written = some t) : s.bytes = t.bytes :=
  congrArg Gabbro.Core.Ast.LowLevel.Layout.bytes (layout_unique target written s t hs ht)

/-- Inverting a successful `.view` initializer: the loader's own `layout` and
    `fits` checks passed, so the width it wrote into the value is positive. -/
theorem view_value_layout (target : ZielDaten) (slot : Nat) (extent : Strecke)
    (written : Gabbro.Core.Ast.WrittenType) (valid : written.valid []) (value : Gabbro.Core.Ast.Dynamisch)
    (yields : Gabbro.Core.Ast.LowLevel.RegionInitializer.value target slot extent
        (.view written valid) = some value) :
    ∃ shape : Gabbro.Core.Ast.LowLevel.Layout, Gabbro.Core.Ast.LowLevel.layout target written = some shape ∧
      shape.fits extent ∧ 0 < shape.bytes := by
  unfold Gabbro.Core.Ast.LowLevel.RegionInitializer.value at yields
  cases hlayout : Gabbro.Core.Ast.LowLevel.layout target written with
  | none => simp only [hlayout, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at yields
  | some shape =>
      by_cases fits : shape.fits extent
      · exact ⟨shape, rfl, fits, layout_positive_bytes target written shape hlayout⟩
      · simp only [hlayout, Option.bind_eq_bind, Option.bind_some, fits, ↓reduceIte, reduceCtorEq] at yields

/-- The logical boot cell of a grant is present exactly when one complete cell
    of the checked width fits into the physical extent. -/
theorem handoffBooking_zero_booked_iff {bytes : Nat} (positive : 0 < bytes)
    {regions : List Strecke} {booking : Sicherheit.Buchung Zelle} {slot : Nat} {extent : Strecke}
    (grant : regions[slot]? = some extent) :
    ((handoffBooking bytes regions booking).umfang slot)[0]? = some (.region slot 0) ↔
      bytes ≤ extent.bis - extent.von := by
  rw [handoffBooking_lookup bytes regions booking grant]
  constructor
  · intro h
    have h1 : 1 ≤ (extent.bis - extent.von) / bytes := h
    have hmul : 1 * bytes ≤ extent.bis - extent.von := (Nat.le_div_iff_mul_le positive).mp h1
    simpa using hmul
  · intro h
    have hmul : 1 * bytes ≤ extent.bis - extent.von := by simpa using h
    have hdiv : 1 ≤ (extent.bis - extent.von) / bytes := (Nat.le_div_iff_mul_le positive).mpr hmul
    exact lt_of_lt_of_le Nat.zero_lt_one hdiv

/-- THE B21 SOURCE CONNECTION. A successful source view of a granted region
    fixes its positive width; at that width slot 0 of the handoff booking holds
    the logical cell `.region slot 0`, whose physical subinterval lies inside
    the grant. The width comes from the loader's layout, never from outside. -/
theorem quellanschluss_view_handoff (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s)
    (slot : Nat) {extent : Strecke} (grant : a.regions[slot]? = some extent)
    (written : Gabbro.Core.Ast.WrittenType) (valid : written.valid []) (value : Gabbro.Core.Ast.Dynamisch)
    (yields : Gabbro.Core.Ast.LowLevel.RegionInitializer.value P.ziel slot extent
        (.view written valid) = some value) :
    ∃ shape : Gabbro.Core.Ast.LowLevel.Layout, Gabbro.Core.Ast.LowLevel.layout P.ziel written = some shape ∧
      0 < shape.bytes ∧ s.rechte.lebt slot = true ∧
      ((handoffBooking shape.bytes a.regions s.buchung).umfang slot)[0]? = some (.region slot 0) ∧
      extent.enthaelt ⟨extent.von, extent.von + shape.bytes⟩ := by
  obtain ⟨shape, hlayout, fits, positive⟩ :=
    view_value_layout P.ziel slot extent written valid value yields
  have len : shape.bytes ≤ extent.bis - extent.von := Nat.le_sub_of_add_le' fits.2
  have within : slot < a.regions.length := (List.getElem?_eq_some_iff.mp grant).1
  have live : s.rechte.lebt slot = true :=
    (geladeneRegion_lebt_leer P u a p geladen slot within).1
  have booked : ((handoffBooking shape.bytes a.regions s.buchung).umfang slot)[0]? =
      some (.region slot 0) := (handoffBooking_zero_booked_iff positive grant).mpr len
  have inside : extent.enthaelt
      ⟨extent.von + 0 * shape.bytes, extent.von + (0 + 1) * shape.bytes⟩ :=
    handoffBooking_inside (booking := s.buchung) positive grant booked
  exact ⟨shape, hlayout, positive, live, booked, by simpa using inside⟩

/-- The same connection at the boot slot, with the exact finite B21 count. The
    count is positive because the checked width fits at least one cell. -/
theorem quellanschluss_view_b21 (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s)
    {extent : Strecke} (grant : a.regions = [extent])
    (written : Gabbro.Core.Ast.WrittenType) (valid : written.valid []) (value : Gabbro.Core.Ast.Dynamisch)
    (yields : Gabbro.Core.Ast.LowLevel.RegionInitializer.value P.ziel 0 extent
        (.view written valid) = some value) :
    ∃ shape : Gabbro.Core.Ast.LowLevel.Layout, Gabbro.Core.Ast.LowLevel.layout P.ziel written = some shape ∧
      0 < shape.bytes ∧
      ((handoffBooking shape.bytes a.regions s.buchung).umfang 0)[0]? = some (.region 0 0) ∧
      (LebendeZellen { s with buchung := handoffBooking shape.bytes a.regions s.buchung }).encard =
        ((extent.bis - extent.von) / shape.bytes : Nat) ∧
      1 ≤ ((extent.bis - extent.von) / shape.bytes : Nat) := by
  have grant0 : a.regions[0]? = some extent := by rw [grant]; rfl
  obtain ⟨shape, hlayout, fits, positive⟩ :=
    view_value_layout P.ziel 0 extent written valid value yields
  have len : shape.bytes ≤ extent.bis - extent.von := Nat.le_sub_of_add_le' fits.2
  have booked : ((handoffBooking shape.bytes a.regions s.buchung).umfang 0)[0]? =
      some (.region 0 0) := (handoffBooking_zero_booked_iff positive grant0).mpr len
  have count := quellladen_handoff_single_encard P u a p geladen shape.bytes grant
  have hmul : 1 * shape.bytes ≤ extent.bis - extent.von := by simpa using len
  have hdiv : 1 ≤ (extent.bis - extent.von) / shape.bytes :=
    (Nat.le_div_iff_mul_le positive).mpr hmul
  exact ⟨shape, hlayout, positive, booked, count, hdiv⟩

/-- Two distinct granted regions viewed at the same type use the same checked
    width, and their logical boot cells occupy disjoint physical storage. -/
theorem quellanschluss_view_getrennt (P : Plattform) (a : AussenStart)
    (s : Zustand Nat Zelle Int Nat Rahmen PUnit)
    (disjoint : a.regions.Pairwise Strecke.getrennt)
    {i j : Nat} {left right : Strecke} (distinct : i ≠ j)
    (li : a.regions[i]? = some left) (lj : a.regions[j]? = some right)
    (written : Gabbro.Core.Ast.WrittenType) (valid : written.valid [])
    (vi vj : Gabbro.Core.Ast.Dynamisch)
    (yi : Gabbro.Core.Ast.LowLevel.RegionInitializer.value P.ziel i left
        (.view written valid) = some vi)
    (yj : Gabbro.Core.Ast.LowLevel.RegionInitializer.value P.ziel j right
        (.view written valid) = some vj) :
    ∃ shape : Gabbro.Core.Ast.LowLevel.Layout, Gabbro.Core.Ast.LowLevel.layout P.ziel written = some shape ∧
      Strecke.getrennt ⟨left.von, left.von + shape.bytes⟩
        ⟨right.von, right.von + shape.bytes⟩ := by
  obtain ⟨shape, hlayout, fi, positive⟩ := view_value_layout P.ziel i left written valid vi yi
  obtain ⟨shapeJ, hlayoutJ, fj, _⟩ := view_value_layout P.ziel j right written valid vj yj
  have eq : shape = shapeJ := layout_unique P.ziel written shape shapeJ hlayout hlayoutJ
  subst shapeJ
  have bookedI : ((handoffBooking shape.bytes a.regions s.buchung).umfang i)[0]? =
      some (.region i 0) := (handoffBooking_zero_booked_iff positive li).mpr (Nat.le_sub_of_add_le' fi.2)
  have bookedJ : ((handoffBooking shape.bytes a.regions s.buchung).umfang j)[0]? =
      some (.region j 0) := (handoffBooking_zero_booked_iff positive lj).mpr (Nat.le_sub_of_add_le' fj.2)
  have sep := handoffBooking_disjoint (booking := s.buchung) positive disjoint distinct
    li lj bookedI bookedJ
  exact ⟨shape, hlayout, by simpa using sep⟩

/-- CHECKED COUNTEREXAMPLE. The width is not a property of the region alone:
    one admitted extent admits two distinct written types with different byte
    widths, and the loader accepts a view of each. This is why the booking must
    take its width from the chosen type's layout (`layout_bytes_unique` rules
    out a second width for one fixed type). -/
theorem written_8_16_valid :
    (Gabbro.Core.Ast.WrittenType.integer false 8 none : Gabbro.Core.Ast.WrittenType).valid [] ∧
    (Gabbro.Core.Ast.WrittenType.integer false 16 none : Gabbro.Core.Ast.WrittenType).valid [] := by
  constructor
  · change 1 ≤ (8 : Nat) ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ 0 ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  · change 1 ≤ (16 : Nat) ∧ 16 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ 0 ≤ 65535 ∧ (65535 : Int) ≤ 65535
    omega

theorem source_region_zwei_breiten
    (valid₁ : (Gabbro.Core.Ast.WrittenType.integer false 8 none : Gabbro.Core.Ast.WrittenType).valid [])
    (valid₂ : (Gabbro.Core.Ast.WrittenType.integer false 16 none : Gabbro.Core.Ast.WrittenType).valid []) :
    ∃ extent : Strecke, ∃ s₁ s₂ : Gabbro.Core.Ast.LowLevel.Layout,
      Gabbro.Core.Ast.LowLevel.layout Plattform.x86_64.ziel (.integer false 8 none) = some s₁ ∧
      Gabbro.Core.Ast.LowLevel.layout Plattform.x86_64.ziel (.integer false 16 none) = some s₂ ∧
      s₁.fits extent ∧ s₂.fits extent ∧ s₁.bytes ≠ s₂.bytes ∧
      (∃ v₁ : Gabbro.Core.Ast.Dynamisch,
        Gabbro.Core.Ast.LowLevel.RegionInitializer.value Plattform.x86_64.ziel 0 extent
          (.view (.integer false 8 none) valid₁) = some v₁) ∧
      (∃ v₂ : Gabbro.Core.Ast.Dynamisch,
        Gabbro.Core.Ast.LowLevel.RegionInitializer.value Plattform.x86_64.ziel 0 extent
          (.view (.integer false 16 none) valid₂) = some v₂) := by
  let extent : Strecke := ⟨0x1000, 0x2000⟩
  let w₁ : Gabbro.Core.Ast.WrittenType := .integer false 8 none
  let w₂ : Gabbro.Core.Ast.WrittenType := .integer false 16 none
  let s₁ : Gabbro.Core.Ast.LowLevel.Layout :=
    ⟨.integer false 8 none, 1, 1, Gabbro.Core.Ast.LowLevel.ByteOrder.ofTarget Plattform.x86_64.ziel⟩
  let s₂ : Gabbro.Core.Ast.LowLevel.Layout :=
    ⟨.integer false 16 none, 2, 2, Gabbro.Core.Ast.LowLevel.ByteOrder.ofTarget Plattform.x86_64.ziel⟩
  have hlayout₁ : Gabbro.Core.Ast.LowLevel.layout Plattform.x86_64.ziel w₁ = some s₁ := by rfl
  have hlayout₂ : Gabbro.Core.Ast.LowLevel.layout Plattform.x86_64.ziel w₂ = some s₂ := by rfl
  have fits₁ : s₁.fits extent := by
    change 0x1000 % 1 = 0 ∧ 0x1000 + 1 ≤ 0x2000
    omega
  have fits₂ : s₂.fits extent := by
    change 0x1000 % 2 = 0 ∧ 0x1000 + 2 ≤ 0x2000
    omega
  have yield₁ : Gabbro.Core.Ast.LowLevel.RegionInitializer.value Plattform.x86_64.ziel 0 extent
      (.view w₁ valid₁) =
      some ⟨.regionView w₁.type, ⟨0, extent.von, 1, Plattform.x86_64.ziel.big⟩⟩ := by
    unfold Gabbro.Core.Ast.LowLevel.RegionInitializer.value
    simp only [hlayout₁, Option.bind_eq_bind, Option.bind_some, fits₁, ↓reduceIte, s₁]
  have yield₂ : Gabbro.Core.Ast.LowLevel.RegionInitializer.value Plattform.x86_64.ziel 0 extent
      (.view w₂ valid₂) =
      some ⟨.regionView w₂.type, ⟨0, extent.von, 2, Plattform.x86_64.ziel.big⟩⟩ := by
    unfold Gabbro.Core.Ast.LowLevel.RegionInitializer.value
    simp only [hlayout₂, Option.bind_eq_bind, Option.bind_some, fits₂, ↓reduceIte, s₂]
  refine ⟨extent, s₁, s₂, hlayout₁, hlayout₂, fits₁, fits₂, ?_, ?_, ?_⟩
  · change (1 : Nat) ≠ 2
    omega
  · exact ⟨_, yield₁⟩
  · exact ⟨_, yield₂⟩

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
          simp [handoffCells, gnil]
        omega
      let i : Fin regions.length := ⟨slot, hslot⟩
      have g := List.getElem?_eq_getElem (l := regions) hslot
      have hlen : (handoffCells 1 regions slot).length = foot i := by
        simp [handoffCells, g, foot, i]
      have hoff : offset < foot i := by simpa [hlen] using h.2
      exact ⟨⟨i, ⟨offset, hoff⟩⟩, rfl⟩
    · rintro ⟨⟨i, d⟩, hp⟩
      have hfst : i.val = slot := congrArg Prod.fst hp
      have hsnd : d.val = offset := congrArg Prod.snd hp
      subst slot
      subst offset
      have g := List.getElem?_eq_getElem (l := regions) i.isLt
      have hlen : (handoffCells 1 regions i.val).length = foot i := by
        simp [handoffCells, g, foot]
      exact ⟨live i.val i.isLt, by simpa [hlen] using d.isLt⟩
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
