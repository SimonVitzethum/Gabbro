module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2
public import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.ArenaOwnership.Machine

/-- The storage for an arena is selected in the actual declaration
    table. Every metadata word has the same range as its arena capacity,
    and aliases across metadata roles are refused. -/
structure ResolvedArenaStorage (u : UProg) (table : (declOf u).Tab) where
  shape : FreiForm (declOf u)
  tableExact : shape.tab = table
  marked : (tabAt u table).arena = true
  payload : ∃ hit, fieldHit u table "wert" = .ok hit ∧
    shape.feld = (tableExact.symm ▸ hit.idx)
  link : ∃ hit, fieldHit u table arenaLinkField = .ok hit ∧
    shape.nxt = (tableExact.symm ▸ hit.idx)
  used : globIdx u.globs ((tabAt u table).name ++ "#used") = .ok shape.zaehl
  committed : globIdx u.globs (arenaExtentWord (tabAt u table).name) = .ok shape.komm
  head : globIdx u.globs (arenaHeadWord (tabAt u table).name) = .ok shape.kopf

/-- Resolve the actual payload, counter, committed count, and free-list
    words after elaboration. A marked table alone supplies no descriptor. -/
def resolveArenaStorage (u : UProg) (table : (declOf u).Tab) :
    Except String (ResolvedArenaStorage u table) := do
  if marked : (tabAt u table).arena = true then
    let name := (tabAt u table).name
    match payload : fieldHit u table "wert", link : fieldHit u table arenaLinkField with
    | .error error, _ | _, .error error => throw error
    | .ok payloadField, .ok linkField =>
      match used : globIdx u.globs (name ++ "#used"),
            committed : globIdx u.globs (arenaExtentWord name),
            head : globIdx u.globs (arenaHeadWord name) with
      | .error error, _, _ | _, .error error, _ | _, _, .error error => throw error
      | .ok usedWord, .ok extentWord, .ok headWord =>
        let limit : Ty := .int 0 ((declOf u).count table)
        if valid : 0 < (declOf u).count table ∧
            (declOf u).gtyp usedWord = limit ∧ (declOf u).gtyp extentWord = limit ∧
            (declOf u).gtyp headWord = limit ∧ (declOf u).typ table linkField.idx = limit ∧
            extentWord ≠ usedWord ∧ headWord ≠ usedWord ∧ headWord ≠ extentWord ∧ linkField.idx ≠ payloadField.idx then
          let shape : FreiForm (declOf u) := {
            tab := table
            feld := payloadField.idx
            zaehl := usedWord
            hz := valid.2.1
            hpos := valid.1
            komm := extentWord
            hk := valid.2.2.1
            hzwei := valid.2.2.2.2.2.1
            kopf := headWord
            hkopf := valid.2.2.2.1
            nxt := linkField.idx
            hnxt := valid.2.2.2.2.1
            hk1 := valid.2.2.2.2.2.2.1
            hk2 := valid.2.2.2.2.2.2.2.1
            hf := valid.2.2.2.2.2.2.2.2 }
          pure ⟨shape, rfl, marked, ⟨payloadField, payload, rfl⟩, ⟨linkField, link, rfl⟩,
            used, committed, head⟩
        else throw "ir: invalid arena memory types or aliased arena metadata"
  else throw "ir: table is not a declared arena"

/-- Ownership starts in the same store as the emitted image. Its used
    counter is zero and its free head is the model's empty marker. -/
theorem checkedArena_initial {u : UProg} {table : (declOf u).Tab}
    (storage : ResolvedArenaStorage u table) (memory : Speicher (declOf u))
    (checked : decide (ArenaLeer storage.shape memory) = true) :
    storage.shape.FreiOk (memory.welt []) ∧ ∀ index, ¬ storage.shape.Lebt (memory.welt []) index := by
  have initial := of_decide_eq_true checked
  refine ⟨⟨[], initial.2.symm ▸ FreiForm.Kette.nil, List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩, ?_⟩
  intro index live
  have indexBelow := live.2.1
  rw [initial.1] at indexBelow
  exact (Int.not_lt.mpr live.1) indexBelow

end Gabbro.Stage0.Senke
