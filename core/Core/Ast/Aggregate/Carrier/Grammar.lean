module

public import Core.Ast.Aggregate.RecordGrammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printTable : PrintedToken :=
  printProgramWord 't' ['a', 'b', 'l', 'e'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def printCount : PrintedToken :=
  printProgramWord 'c' ['o', 'u', 'n', 't'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def printSlot : PrintedToken :=
  printProgramWord 's' ['l', 'o', 't'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

def TableDeclaration.header (item : TableDeclaration before) : List PrintedToken :=
  (if item.exported then [printPub] else []) ++
    [printTable, item.name.print, printCount, printInteger item.count,
      printOpenBrace, printSlot, printOpenBrace]

/-- The final slot field may omit the comma. The canonical printer emits it. -/
inductive TableFieldsRead (scope : Scope) : List Token → List RecordMember → List Token → Prop where
  | close : TableFieldsRead scope (closeBrace :: rest) [] rest
  | last (name : Identifier) : TypeReads scope input written (closeBrace :: rest) →
      TableFieldsRead scope (.word name.val :: colon :: input) [⟨name, written⟩] rest
  | next (name : Identifier) : TypeReads scope input written (comma :: more) →
      TableFieldsRead scope more fields rest →
      TableFieldsRead scope (.word name.val :: colon :: input) (⟨name, written⟩ :: fields) rest

end Gabbro.Core.Ast
