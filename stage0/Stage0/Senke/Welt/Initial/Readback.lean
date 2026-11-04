/- Read complete initialized cells at the canonical layout's actual addresses. -/
module
public import Stage0.Senke.Welt.Initial.Validity
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The serializer and the checked layout share the same padded cursor recurrence. -/
theorem initialGlobalBlocks_read (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) {m : Runner.Mem} (gs : List (Fin u.globs.length))
    (cursor base : Nat) (loaded : BytesAt m (base + cursor) (initialGlobalBlocks u valid L gs cursor))
    (g : Fin u.globs.length) (member : g ∈ gs) :
    BytesAt m (base + globStartOf gs cursor (globSz u) (fun g => wordAlign (globAlign u g)) g)
      (initialValueBytes L ((declOf u).gtyp g) ((initialWorld u valid).globs g)) := by
  induction gs generalizing cursor with
  | nil => simp at member
  | cons a gs ih =>
    have aligned := le_alignUp cursor (wordAlign (globAlign u a))
    have blocks : BytesAt m (base + cursor)
        (List.replicate (alignUp cursor (wordAlign (globAlign u a)) - cursor) 0 ++
          (initialValueBytes L ((declOf u).gtyp a) ((initialWorld u valid).globs a) ++
            initialGlobalBlocks u valid L gs
              (alignUp cursor (wordAlign (globAlign u a)) + globSz u a))) := loaded
    have content := blocks.right
    simp only [List.length_replicate] at content
    have address : base + cursor + (alignUp cursor (wordAlign (globAlign u a)) - cursor) =
        base + alignUp cursor (wordAlign (globAlign u a)) := by omega
    rw [address] at content
    by_cases same : g = a
    · subst g
      simpa only [globStartOf, ↓reduceIte] using content.left
    · have tail := content.right
      rw [initialValueBytes_length] at tail
      have member' : g ∈ gs := by simpa only [List.mem_cons, same, false_or] using member
      have result := ih (alignUp cursor (wordAlign (globAlign u a)) + globSz u a)
        (by simpa only [globSz, Nat.add_assoc] using tail) member'
      simpa only [globStartOf, if_neg same] using result

/-- The only required layout correspondence concerns storage, so relocating function
    addresses and startup metadata does not invalidate the initializer theorem. -/
structure InitialLayout (u : UProg) (L : Lay (declOf u)) : Prop where
  globals : ∀ g, L.ga g = L.lo + globStartOf (List.finRange u.globs.length) 0
    (globSz u) (fun g => wordAlign (globAlign u g)) g
  columns : ∀ t f, L.col t f = L.lo +
    globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) +
    (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum +
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum
  extent : L.hi = L.lo +
    globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) + tabsSz u
  count : ∀ t, L.count t = (declOf u).count t

theorem initialLayout_layU (u : UProg) (tor : (declOf u).Ax → Option TorB) (base : Nat) :
    InitialLayout u (layU u tor base) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, rfl, fun t => ?_⟩
  simp only [Lay.count, layU, ite_self, Int.natCast_zero, Int.add_zero]

/-- The encoded bytes reserve exactly the final layout's world extent, including padding. -/
theorem InitialLayout.bytes_length {u : UProg} {L : Lay (declOf u)}
    (layout : InitialLayout u L) (valid : GabbroV.sp0OkB u = true) :
    (initialWorldBytes u valid L).length = L.hi - L.lo := by
  rw [initialWorldBytes_length, layout.extent]
  omega

/-- Every global reads back with all limbs/fields, at its final relocated address. -/
theorem initialWorldBytes_global {u : UProg} {valid : GabbroV.sp0OkB u = true}
    {L : Lay (declOf u)} (layout : InitialLayout u L) {m : Runner.Mem}
    (loaded : BytesAt m L.lo (initialWorldBytes u valid L)) (g : Fin u.globs.length) :
    ValueAt L m (BitVec.ofNat 64 (L.ga g)) 0 ((declOf u).gtyp g) ((initialWorld u valid).globs g) := by
  apply initialValueBytes_at (valid := initialWorld_global_valid u valid L g)
  rw [layout.globals g]
  exact initialGlobalBlocks_read u valid L _ 0 L.lo (by simpa only [Nat.add_zero, initialGlobals] using loaded.left)
    g (List.mem_finRange g)

/-- Column stride is the complete element span, even for nested arrays and products. -/
theorem initialWorldBytes_slot {u : UProg} {valid : GabbroV.sp0OkB u = true}
    {L : Lay (declOf u)} (layout : InitialLayout u L) {m : Runner.Mem}
    (loaded : BytesAt m L.lo (initialWorldBytes u valid L))
    (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Nat) (hk : (k : Int) < L.count t) :
    ValueAt L m (BitVec.ofNat 64 (L.elem t f k)) 0 ((declOf u).typ t f)
      ((initialWorld u valid).slots t k f) := by
  have tables := loaded.right
  rw [initialGlobals_length] at tables
  have table := BytesAt.flatMap_piece (List.finRange u.tabs.length) _ t.val (by simp) tables
  have tableOffset : (((List.finRange u.tabs.length).take t.val).flatMap (initialTable u valid L)).length =
      (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum := by
    simp only [List.length_flatMap, initialTable_length, List.map_take]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta, tableOffset] at table
  have column := BytesAt.flatMap_piece (List.finRange (fieldCount u t)) _ f.val (by simp) table
  have columnOffset : (((List.finRange (fieldCount u t)).take f.val).flatMap (initialColumn u valid L t)).length =
      (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum := by
    simp only [List.length_flatMap, initialColumn_length, List.map_take]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta, columnOffset] at column
  have cell := BytesAt.replicate_piece
    (initialValueBytes L ((declOf u).typ t f) ((initialWorld u valid).slots t 0 f))
    ((declOf u).count t).toNat _ k (by rw [layout.count t] at hk; omega) column
  rw [initialValueBytes_length] at cell
  apply initialValueBytes_at (valid := initialWorld_slot_valid u valid L t f k)
  simpa only [Lay.elem, layout.columns t f, initialWorld_column, Nat.mul_comm k,
    Nat.mul_assoc] using cell

/-- The actual loaded bytes establish the complete source memory relation. No additional
    initialization or validity assumption is delegated to the caller. -/
theorem initialWorldBytes_at {u : UProg} {valid : GabbroV.sp0OkB u = true}
    {L : Lay (declOf u)} (layout : InitialLayout u L) {m : Runner.Mem}
    (loaded : BytesAt m L.lo (initialWorldBytes u valid L)) :
    WeltAt m L (initialWorld u valid) := by
  refine ⟨initialWorldBytes_slot layout loaded, initialWorldBytes_global layout loaded, ?_⟩
  intro x lower upper
  have length := layout.bytes_length valid
  have byte := loaded (x - L.lo) (by omega)
  have address : L.lo + (x - L.lo) = x := by omega
  rw [address] at byte
  exact byte.2.1

end Gabbro.Stage0.Senke
