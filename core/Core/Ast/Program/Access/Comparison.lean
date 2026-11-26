module

public import Core.Ast.Program.Access.Grammar
public import Core.Ast.Program.WrittenTypes
public import Core.Ast.Expression
public import Core.Ast.Expression.Atoms

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

private theorem awaitHead_ne_load : keyword "await" ≠ keyword "load" := by
  intro h; cases h
private theorem awaitHead_ne_store : keyword "await" ≠ keyword "store" := by
  intro h; cases h
private theorem awaitHead_ne_swap : keyword "await" ≠ keyword "swap" := by
  intro h; cases h
private theorem awaitHead_ne_cas : keyword "await" ≠ keyword "cas" := by
  intro h; cases h
private theorem awaitHead_ne_fetchAdd : keyword "await" ≠ keyword "fetch_add" := by
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
    | _ => cases (List.cons.inj eq).1
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
    | _ => cases (List.cons.inj eq).1
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
    | _ => cases (List.cons.inj eq).1
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
    | _ => cases (List.cons.inj eq).1
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
    | _ => cases (List.cons.inj eq).1
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
    | load => exact (awaitHead_ne_load (List.cons.inj eq).1).elim
    | store => exact (awaitHead_ne_store (List.cons.inj eq).1).elim
    | swap => exact (awaitHead_ne_swap (List.cons.inj eq).1).elim
    | vergleicheTausche => exact (awaitHead_ne_cas (List.cons.inj eq).1).elim
    | holeUndAddiere => exact (awaitHead_ne_fetchAdd (List.cons.inj eq).1).elim

end Gabbro.Core.Ast
