module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2
public import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.ArenaOwnership Gabbro.Grammatik.ArenaOwnership.Machine

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

/-- The finite arena table is read from the actual canonical declarations.
    Ordinary tables have no arena storage and every declared arena has
    an entry produced by the same typed resolver. -/
structure ArenaStorageExport (u : UProg) where
  entry : (table : (declOf u).Tab) → Option (ResolvedArenaStorage u table)
  coverage : ∀ table, (entry table).isSome = true ↔ (tabAt u table).arena = true
  resolved : ∀ table storage, entry table = some storage → resolveArenaStorage u table = .ok storage

def collectArenaStorage (u : UProg) : Except String (ArenaStorageExport u) :=
  if complete : (List.finRange u.tabs.length).all (fun table =>
      !(tabAt u table).arena || (resolveArenaStorage u table).isOk) = true then
    .ok {
      entry := fun table => (resolveArenaStorage u table).toOption
      coverage := by
        intro table
        cases found : resolveArenaStorage u table with
        | error failure =>
          have verdict := List.all_eq_true.mp complete table (List.mem_finRange table)
          simp only [found, Except.isOk, Except.toBool, Bool.or_false] at verdict
          have ordinary : (tabAt u table).arena = false := by
            cases marked : (tabAt u table).arena with
            | false => rfl
            | true => simp only [marked, Bool.not_true, Bool.false_eq_true] at verdict
          simp only [found, Except.toOption, Option.isSome_none, ordinary]
        | ok storage =>
          simp only [found, Except.toOption, Option.isSome_some, storage.marked]
      resolved := by
        intro table storage read
        cases resolved : resolveArenaStorage u table with
        | error failure =>
          simp only [resolved, Except.toOption] at read
          cases read
        | ok found =>
          have same : found = storage := Option.some.inj (by
            simpa only [resolved, Except.toOption] using read)
          cases same
          rfl }
  else .error "ir: a declared arena has unresolved ownership storage"

/-- Boundary modes for a local arena. The ordinary ownership checker
    still has to prove that no caller or return transfers an allocation. -/
def localArenaModes : (parameters : Ctx) → Source.Modes parameters
  | [] => .nil
  | _ :: rest => .cons none (localArenaModes rest)

theorem localArenaModes_valid {D : Deklaration} (shape : FreiForm D) (parameters : Ctx) :
    Source.Flow.validParameters shape (localArenaModes parameters) = true := by
  induction parameters with
  | nil => rfl
  | cons first rest ih => simpa only [localArenaModes, Source.Flow.validParameters, Option.isSome_none,
      Bool.not_false, Bool.true_or, Bool.true_and] using ih

def localArenaInterface {D : Deklaration} (shape : FreiForm D) : Body.ArenaIface D :=
  ⟨shape, fun fn => ⟨localArenaModes (D.params fn), localArenaModes_valid shape _, .plain⟩⟩

def ArenaStorageExport.localInterfaces {u : UProg} (storage : ArenaStorageExport u) :
    List (Body.ArenaIface (declOf u)) :=
  (List.finRange u.tabs.length).filterMap fun table =>
    (storage.entry table).map (fun entry => localArenaInterface entry.shape)

theorem ArenaStorageExport.localInterfaces_exact {u : UProg} (storage : ArenaStorageExport u)
    (arena : Body.ArenaIface (declOf u)) (present : arena ∈ storage.localInterfaces) :
    ∃ entry : ResolvedArenaStorage u arena.A.tab,
      resolveArenaStorage u arena.A.tab = .ok entry ∧ entry.shape = arena.A := by
  obtain ⟨table, _, selected⟩ := List.mem_filterMap.mp present
  cases found : storage.entry table with
  | none =>
    simp only [found, Option.map_none] at selected
    cases selected
  | some entry =>
    simp only [found, Option.map_some] at selected
    obtain rfl := Option.some.inj selected
    have atTable : ∃ resolved : ResolvedArenaStorage u table,
        resolveArenaStorage u table = .ok resolved ∧ resolved.shape = entry.shape :=
      ⟨entry, storage.resolved table entry found, rfl⟩
    exact entry.tableExact.symm ▸ atTable

theorem ArenaStorageExport.localInterfaces_coverage {u : UProg} (storage : ArenaStorageExport u)
    (table : (declOf u).Tab) : (tabAt u table).arena = true ↔
      ∃ arena ∈ storage.localInterfaces, arena.A.tab = table := by
  constructor
  · intro marked
    have covered := (storage.coverage table).mpr marked
    cases found : storage.entry table with
    | none =>
      simp only [found, Option.isSome_none, Bool.false_eq_true] at covered
    | some entry =>
      refine ⟨localArenaInterface entry.shape, ?_, entry.tableExact⟩
      exact List.mem_filterMap.mpr ⟨table, List.mem_finRange table, by rw [found, Option.map_some]⟩
  · rintro ⟨arena, present, rfl⟩
    obtain ⟨entry, _, _⟩ := storage.localInterfaces_exact arena present
    exact entry.marked

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
