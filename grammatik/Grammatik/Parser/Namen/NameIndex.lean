module
public import Grammatik.Parser.Lex.TafelIndex
@[expose] public section

namespace Gabbro.Grammatik.Parser.Namensraum

/-- One unit's immutable declaration index. The source list is retained so a record update
    cannot silently reuse an index of different declarations. -/
structure NameIndex where
  names : List (List String)
  paths : Tafel.Index (List String) (List String) id
  pathsFaithful : paths.liste = names
  shorts : Tafel.Counts
  shortsFaithful : shorts.liste = names.map (fun path => path.getLast?.getD "")

/-- Kernel evaluation never needs to construct either map. -/
@[cbv_opaque] def NameIndex.von (names : List (List String)) : Merk NameIndex :=
  Merk.von ⟨names, Tafel.Index.von id names, rfl,
    Tafel.Counts.von (names.map (fun path => path.getLast?.getD "")), rfl⟩

@[inline] def NameIndex.read {β : Type} (names : List (List String))
    (fast : (index : NameIndex) → index.names = names → β) (slow : Unit → β)
    (index : NameIndex) : β :=
  match withPtrEqDecEq index.names names (fun _ => inferInstance) with
  | isTrue same => fast index same
  | isFalse _ => slow ()

theorem NameIndex.read_eq {β : Type} (names : List (List String))
    (fast : (index : NameIndex) → index.names = names → β) (slow : Unit → β)
    (faithful : ∀ index same, fast index same = slow ()) (index : NameIndex) :
    index.read names fast slow = slow () := by
  unfold NameIndex.read
  split
  · exact faithful _ _
  · rfl

/-- As with `UProg.mitMerk`, the cache is observationally irrelevant. Pointer equality makes
    the usual matching-list check constant time; a stale cache takes the specification path. -/
@[inline] def NameIndex.cached {β : Type} (cache : Merk NameIndex)
    (names : List (List String)) (fast : (index : NameIndex) → index.names = names → β)
    (slow : Unit → β) (faithful : ∀ index same, fast index same = slow ()) : β :=
  cache.lies (NameIndex.read names fast slow)
    (fun a b => (NameIndex.read_eq names fast slow faithful a).trans
      (NameIndex.read_eq names fast slow faithful b).symm)

theorem NameIndex.cached_eq {β : Type} (cache : Merk NameIndex)
    (names : List (List String)) (fast : (index : NameIndex) → index.names = names → β)
    (slow : Unit → β) (faithful : ∀ index same, fast index same = slow ()) :
    NameIndex.cached cache names fast slow faithful = slow () :=
  Merk.lies_eq _ _ _ _ (NameIndex.read_eq names fast slow faithful)

end Gabbro.Grammatik.Parser.Namensraum
