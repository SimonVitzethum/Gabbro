module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.Types
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- One unit head table, shared by every body. -/
structure UHeadMemo where
  heads : List UFnKopf
  table : Tafel.Fest (fun head : UFnKopf => head.name) heads
  array : Array UFnKopf
  array_eq : array = heads.toArray
  positions : Tafel.Positions
  positions_eq : positions.names = heads.map UFnKopf.name

@[cbv_opaque] def UHeadMemo.von (heads : List UFnKopf) : Merk UHeadMemo :=
  Merk.von
    ({ heads := heads
       table := Tafel.fest UFnKopf.name heads
       array := heads.toArray
       array_eq := rfl
       positions := Tafel.Positions.von (heads.map UFnKopf.name)
       positions_eq := Tafel.Positions.von_names (heads.map UFnKopf.name) } : UHeadMemo)

/-- Local stacks use stable levels; their maps stay persistent across bindings. -/
structure ULookupMemo where
  names : Tafel.Positions
  kinds : Tafel.Stack UParamArt
  types : Tafel.Stack Ty
  heads : Merk UHeadMemo

@[cbv_opaque] def ULookupMemo.empty : Merk ULookupMemo :=
  Merk.von
    ({ names := Tafel.Positions.empty
       kinds := Tafel.Stack.empty
       types := Tafel.Stack.empty
       heads := UHeadMemo.von [] } : ULookupMemo)

@[cbv_opaque] def ULookupMemo.von (names : List String) (kinds : List UParamArt)
    (types : List Ty) (heads : Merk UHeadMemo) : Merk ULookupMemo :=
  Merk.von
    ({ names := (Tafel.Positions.von names).rebase names (Tafel.Positions.von_names names).symm
       kinds := (Tafel.Stack.von kinds).rebase kinds (Tafel.Stack.von_liste kinds).symm
       types := (Tafel.Stack.von types).rebase types (Tafel.Stack.von_liste types).symm
       heads := heads } : ULookupMemo)

/-- A generic validated cache reader. Shared lists take one pointer comparison; stale
    lists keep the specification result. Proofs never depend on a cache's contents. -/
@[inline] def readMemo {α β γ : Type} [DecidableEq α]
    (cache : Merk γ) (source : γ → List α) (xs : List α)
    (fast : (memo : γ) → source memo = xs → β) (slow : Unit → β)
    (faithful : ∀ memo same, fast memo same = slow ()) : β :=
  cache.lies (fun memo =>
    match withPtrEqDecEq (source memo) xs (fun _ => inferInstance) with
    | isTrue same => fast memo same
    | isFalse _ => slow ()) (by
      intro a b
      have equal : ∀ memo : γ,
          (match withPtrEqDecEq (source memo) xs (fun _ => inferInstance) with
           | isTrue same => fast memo same
           | isFalse _ => slow ()) = slow () := by
        intro memo
        split
        · exact faithful _ _
        · rfl
      exact (equal a).trans (equal b).symm)

theorem readMemo_eq {α β γ : Type} [DecidableEq α]
    (cache : Merk γ) (source : γ → List α) (xs : List α)
    (fast : (memo : γ) → source memo = xs → β) (slow : Unit → β)
    (faithful : ∀ memo same, fast memo same = slow ()) :
    readMemo cache source xs fast slow faithful = slow () := by
  unfold readMemo
  apply Merk.lies_eq
  intro memo
  split
  · exact faithful _ _
  · rfl

end Gabbro.Grammatik.Parser.Uebersetze
