module

public import Core.Ast.Program.Access.Grammar
public import Core.Ast.Program.WrittenTypes
public import Core.Ast.Expression
public import Core.Ast.Expression.Atoms

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text



private theorem ne_load_store : keyword "load" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_load_swap : keyword "load" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_load_cas : keyword "load" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_load_fetchadd : keyword "load" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_load_await : keyword "load" ≠ keyword "await" := by
  intro h; cases h
private theorem ne_load_publish : keyword "load" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_store_load : keyword "store" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_store_swap : keyword "store" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_store_cas : keyword "store" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_store_fetchadd : keyword "store" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_store_await : keyword "store" ≠ keyword "await" := by
  intro h; cases h
private theorem ne_store_publish : keyword "store" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_swap_load : keyword "swap" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_swap_store : keyword "swap" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_swap_cas : keyword "swap" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_swap_fetchadd : keyword "swap" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_swap_await : keyword "swap" ≠ keyword "await" := by
  intro h; cases h
private theorem ne_swap_publish : keyword "swap" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_cas_load : keyword "cas" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_cas_store : keyword "cas" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_cas_swap : keyword "cas" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_cas_fetchadd : keyword "cas" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_cas_await : keyword "cas" ≠ keyword "await" := by
  intro h; cases h
private theorem ne_cas_publish : keyword "cas" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_fetchadd_load : keyword "fetch_add" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_fetchadd_store : keyword "fetch_add" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_fetchadd_swap : keyword "fetch_add" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_fetchadd_cas : keyword "fetch_add" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_fetchadd_await : keyword "fetch_add" ≠ keyword "await" := by
  intro h; cases h
private theorem ne_fetchadd_publish : keyword "fetch_add" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_await_load : keyword "await" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_await_store : keyword "await" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_await_swap : keyword "await" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_await_cas : keyword "await" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_await_fetchadd : keyword "await" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_await_publish : keyword "await" ≠ keyword "publish" := by
  intro h; cases h
private theorem ne_publish_load : keyword "publish" ≠ keyword "load" := by
  intro h; cases h
private theorem ne_publish_store : keyword "publish" ≠ keyword "store" := by
  intro h; cases h
private theorem ne_publish_swap : keyword "publish" ≠ keyword "swap" := by
  intro h; cases h
private theorem ne_publish_cas : keyword "publish" ≠ keyword "cas" := by
  intro h; cases h
private theorem ne_publish_fetchadd : keyword "publish" ≠ keyword "fetch_add" := by
  intro h; cases h
private theorem ne_publish_await : keyword "publish" ≠ keyword "await" := by
  intro h; cases h

/-- **The productions of the access forms are deterministic**: two reads of the same tokens agree on the form and on
    the rest. -/
theorem AccessReads.deterministic (left : AccessReads scope input a rest)
    (right : AccessReads scope input b rest') : a = b ∧ rest = rest' := by
  generalize eq : input = tokens at right
  cases left with
  | load name ordinary written valid region visible receiverOrdinary typeRead indexRead modeRead =>
    cases right with
    | load otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | store => exact (ne_load_store (List.cons.inj eq).1).elim
    | swap => exact (ne_load_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_load_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_load_fetchadd (List.cons.inj eq).1).elim
    | erwarte => exact (ne_load_await (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_load_publish (List.cons.inj eq).1).elim
  | store region visible receiverOrdinary indexRead valueRead modeRead =>
    cases right with
    | store otherRegion otherVisible otherReceiver otherIndex otherValue otherMode =>
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameValue, valueRest⟩ := valueRead.deterministic otherValue
      cases sameValue
      cases (List.cons.inj valueRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_store_load (List.cons.inj eq).1).elim
    | swap => exact (ne_store_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_store_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_store_fetchadd (List.cons.inj eq).1).elim
    | erwarte => exact (ne_store_await (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_store_publish (List.cons.inj eq).1).elim
  | swap name ordinary written valid region visible receiverOrdinary typeRead indexRead valueRead modeRead =>
    cases right with
    | swap otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherValue otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameValue, valueRest⟩ := valueRead.deterministic otherValue
      cases sameValue
      cases (List.cons.inj valueRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_swap_load (List.cons.inj eq).1).elim
    | store => exact (ne_swap_store (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_swap_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_swap_fetchadd (List.cons.inj eq).1).elim
    | erwarte => exact (ne_swap_await (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_swap_publish (List.cons.inj eq).1).elim
  | vergleicheTausche name ordinary written valid region visible receiverOrdinary typeRead indexRead expectedRead
      neuRead modeRead =>
    cases right with
    | vergleicheTausche otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherExpected otherNeu otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameExpected, expectedRest⟩ := expectedRead.deterministic otherExpected
      cases sameExpected
      cases (List.cons.inj expectedRest).2
      obtain ⟨sameNeu, neuRest⟩ := neuRead.deterministic otherNeu
      cases sameNeu
      cases (List.cons.inj neuRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_cas_load (List.cons.inj eq).1).elim
    | store => exact (ne_cas_store (List.cons.inj eq).1).elim
    | swap => exact (ne_cas_swap (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_cas_fetchadd (List.cons.inj eq).1).elim
    | erwarte => exact (ne_cas_await (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_cas_publish (List.cons.inj eq).1).elim
  | holeUndAddiere name ordinary written valid region visible receiverOrdinary typeRead indexRead betragRead modeRead =>
    cases right with
    | holeUndAddiere otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherBetrag otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameBetrag, betragRest⟩ := betragRead.deterministic otherBetrag
      cases sameBetrag
      cases (List.cons.inj betragRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_fetchadd_load (List.cons.inj eq).1).elim
    | store => exact (ne_fetchadd_store (List.cons.inj eq).1).elim
    | swap => exact (ne_fetchadd_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_fetchadd_cas (List.cons.inj eq).1).elim
    | erwarte => exact (ne_fetchadd_await (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_fetchadd_publish (List.cons.inj eq).1).elim
  | erwarte name ordinary written valid region visible receiverOrdinary typeRead indexRead markerRead modeRead =>
    cases right with
    | erwarte otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherMarker otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameMarker, markerRest⟩ := markerRead.deterministic otherMarker
      cases sameMarker
      cases (List.cons.inj markerRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_await_load (List.cons.inj eq).1).elim
    | store => exact (ne_await_store (List.cons.inj eq).1).elim
    | swap => exact (ne_await_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_await_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_await_fetchadd (List.cons.inj eq).1).elim
    | veroeffentliche => exact (ne_await_publish (List.cons.inj eq).1).elim

  | veroeffentliche region visible receiverOrdinary indexRead valueRead modeRead =>
    cases right with
    | veroeffentliche otherRegion otherVisible otherReceiver otherIndex otherValue otherMode =>
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameValue, valueRest⟩ := valueRead.deterministic otherValue
      cases sameValue
      cases (List.cons.inj valueRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | load => exact (ne_publish_load (List.cons.inj eq).1).elim
    | store => exact (ne_publish_store (List.cons.inj eq).1).elim
    | swap => exact (ne_publish_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (ne_publish_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (ne_publish_fetchadd (List.cons.inj eq).1).elim
    | erwarte => exact (ne_publish_await (List.cons.inj eq).1).elim

end Gabbro.Core.Ast
