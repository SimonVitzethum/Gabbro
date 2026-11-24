module

public import Core.Ast.Aggregate.Carrier.Grammar
public import Core.Ast.Variant.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem RecordMembersRead.deterministic (left : RecordMembersRead scope input a rest)
    (right : RecordMembersRead scope input b more) : a = b ∧ rest = more := by
  induction left generalizing b more with
  | close =>
    cases right with
    | close => exact ⟨rfl, rfl⟩
  | next name typeRead remaining ih =>
    generalize hname : name.val = spelling at right
    cases right with
    | next otherName otherType otherRemaining =>
      cases Subtype.ext hname
      obtain ⟨rfl, tail⟩ := typeRead.deterministic otherType
      cases (List.cons.inj tail).2
      obtain ⟨rfl, rfl⟩ := ih otherRemaining
      exact ⟨rfl, rfl⟩

theorem TableFieldsRead.deterministic (left : TableFieldsRead scope input a rest)
    (right : TableFieldsRead scope input b more) : a = b ∧ rest = more := by
  induction left generalizing b more with
  | close =>
    cases right with
    | close => exact ⟨rfl, rfl⟩
  | last name typeRead =>
    generalize hname : name.val = spelling at right
    cases right with
    | last otherName otherType =>
      cases Subtype.ext hname
      obtain ⟨rfl, suffix⟩ := typeRead.deterministic otherType
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | next _ otherType _ =>
      have suffix := (typeRead.deterministic otherType).2
      cases suffix
  | next name typeRead remaining ih =>
    generalize hname : name.val = spelling at right
    cases right with
    | last _ otherType =>
      have suffix := (typeRead.deterministic otherType).2
      cases suffix
    | next otherName otherType otherRemaining =>
      cases Subtype.ext hname
      obtain ⟨rfl, tail⟩ := typeRead.deterministic otherType
      cases (List.cons.inj tail).2
      obtain ⟨rfl, rfl⟩ := ih otherRemaining
      exact ⟨rfl, rfl⟩

theorem RecordMembersRead.consumes (read : RecordMembersRead scope input fields rest) : rest <:+ input := by
  induction read with
  | close => exact List.suffix_cons _ _
  | next _ typeRead _ ih =>
    exact (ih.trans ((List.suffix_cons _ _).trans typeRead.consumes)).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _))

theorem TableFieldsRead.consumes (read : TableFieldsRead scope input fields rest) : rest <:+ input := by
  induction read with
  | close => exact List.suffix_cons _ _
  | last _ typeRead =>
    exact ((List.suffix_cons _ _).trans typeRead.consumes).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _))
  | next _ typeRead _ ih =>
    exact (ih.trans ((List.suffix_cons _ _).trans typeRead.consumes)).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _))

private def printedMemberList (fields : List RecordMember) (rest : List Token) : List Token :=
  (fields.flatMap RecordMember.printPieces).map PrintedToken.value ++ closeBrace :: rest

private theorem printedMemberList_cons (member : RecordMember) (tail : List RecordMember) :
    printedMemberList (member :: tail) rest =
      .word member.name.val :: colon ::
        (member.written.printPieces.map PrintedToken.value ++ comma :: printedMemberList tail rest) := by
  have name : member.name.print.value = .word member.name.val := rfl
  have hpColon : printColon.value = colon := rfl
  have hpComma : printComma.value = comma := rfl
  simp only [printedMemberList, List.flatMap_cons, RecordMember.printPieces, List.map_append,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, name, hpColon, hpComma]

theorem RecordMembersRead.printReads (members : List RecordMember)
    (valid : ∀ member ∈ members, member.written.valid scope) :
    RecordMembersRead scope
      ((members.flatMap RecordMember.printPieces).map PrintedToken.value ++ closeBrace :: rest) members rest := by
  change RecordMembersRead scope (printedMemberList members rest) members rest
  induction members with
  | nil => exact .close
  | cons member tail ih =>
    rw [printedMemberList_cons]
    exact .next member.name
      (member.written.printReads (valid member List.mem_cons_self) (by intro suffix same; cases same))
      (ih (fun field h => valid field (List.mem_cons_of_mem _ h)))

theorem TableFieldsRead.printReads (members : List RecordMember)
    (valid : ∀ member ∈ members, member.written.valid scope) :
    TableFieldsRead scope
      ((members.flatMap RecordMember.printPieces).map PrintedToken.value ++ closeBrace :: rest) members rest := by
  change TableFieldsRead scope (printedMemberList members rest) members rest
  induction members with
  | nil => exact .close
  | cons member tail ih =>
    rw [printedMemberList_cons]
    exact .next member.name
      (member.written.printReads (valid member List.mem_cons_self) (by intro suffix same; cases same))
      (ih (fun field h => valid field (List.mem_cons_of_mem _ h)))

theorem VariantMemberRead.deterministic (left : VariantMemberRead scope input a rest)
    (right : VariantMemberRead scope input b more) : a = b ∧ rest = more := by
  cases left with
  | nullary name closed =>
    generalize hname : name.val = spelling at right
    cases right with
    | nullary otherName _ =>
      cases Subtype.ext hname
      exact ⟨rfl, rfl⟩
    | payload _ _ => exact (closed _ rfl).elim
  | payload name typeRead =>
    generalize hname : name.val = spelling at right
    cases right with
    | nullary _ closed => exact (closed _ rfl).elim
    | payload otherName otherType =>
      cases Subtype.ext hname
      obtain ⟨rfl, suffix⟩ := typeRead.deterministic otherType
      exact ⟨rfl, (List.cons.inj suffix).2⟩

theorem VariantMembersTailRead.deterministic (left : VariantMembersTailRead scope input a rest)
    (right : VariantMembersTailRead scope input b more) : a = b ∧ rest = more := by
  induction left generalizing b more with
  | done =>
    cases right with
    | done => exact ⟨rfl, rfl⟩
  | next memberRead _ ih =>
    cases right with
    | next otherMember otherTail =>
      obtain ⟨rfl, rfl⟩ := memberRead.deterministic otherMember
      obtain ⟨rfl, rfl⟩ := ih otherTail
      exact ⟨rfl, rfl⟩

theorem VariantMemberRead.consumes (read : VariantMemberRead scope input member rest) : rest <:+ input := by
  cases read with
  | nullary _ _ => exact List.suffix_cons _ _
  | payload _ typeRead =>
    exact ((List.suffix_cons _ _).trans typeRead.consumes).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _))

theorem VariantMembersTailRead.consumes (read : VariantMembersTailRead scope input members rest) :
    rest <:+ input := by
  induction read with
  | done => exact List.suffix_cons _ _
  | next head _ ih => exact (ih.trans head.consumes).trans (List.suffix_cons _ _)

theorem VariantMemberRead.printReads (member : VariantMember) (valid : member.valid scope)
    (closed : ∀ suffix, rest ≠ openParen :: suffix) :
    VariantMemberRead scope (member.printPieces.map PrintedToken.value ++ rest) member rest := by
  rcases member with ⟨name, payload⟩
  have nameToken : name.print.value = .word name.val := rfl
  cases payload with
  | none => exact .nullary name closed
  | some written =>
    have hpOpen : printOpen.value = openParen := rfl
    have hpClose : printClose.value = closeParen := rfl
    have read := written.printReads valid (rest := closeParen :: rest) (by intro tail same; cases same)
    simpa only [VariantMember.printPieces, List.map_cons, List.map_append, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append, nameToken, hpOpen, hpClose] using
      (VariantMemberRead.payload name read)

end Gabbro.Core.Ast
