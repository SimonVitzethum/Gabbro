module

public import Core.Ast.ProgramHeader

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printTypeDecl : PrintedToken :=
  printProgramWord 't' ['y', 'p', 'e'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

def printPub : PrintedToken :=
  printProgramWord 'p' ['u', 'b'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide)

def recordDeclarationHead (exported : Bool) : List PrintedToken :=
  if exported then [printPub, printTypeDecl] else [printTypeDecl]

def recordDeclarationPrefix (exported : Bool) : List Token :=
  if exported then [keyword "pub", keyword "type"] else [keyword "type"]

def RecordMember.printPieces (member : RecordMember) : List PrintedToken :=
  [member.name.print, printColon] ++ member.written.printPieces ++ [printComma]

/-- The ordinary record production keeps declaration order and consumes the closing brace. -/
inductive RecordMembersRead : List Token → List RecordMember → List Token → Prop where
  | close : RecordMembersRead (closeBrace :: rest) [] rest
  | next (name : Identifier) : TypeReads input written (comma :: more) →
      RecordMembersRead more remaining rest →
      RecordMembersRead (.word name.val :: colon :: input) (⟨name, written⟩ :: remaining) rest

end Gabbro.Core.Ast
