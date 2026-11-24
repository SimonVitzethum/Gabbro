module

public import Core.Ast.Aggregate.Pattern
public import Core.Ast.Aggregate.RecordGrammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printTagged : PrintedToken :=
  printProgramWord 't' ['a', 'g', 'g', 'e', 'd'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)

def printMatch : PrintedToken :=
  printProgramWord 'm' ['a', 't', 'c', 'h'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def matchArrow : Token := .punctuation ['=', '>']

def printMatchArrow : PrintedToken := printPunctuation "=>" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or])
  (fun _ first => tokenHead (c := '=') first (punctuationHead (by
    simp only [List.mem_cons, Char.reduceEq, true_or, false_or])))

def taggedDeclarationHead (exported : Bool) : List PrintedToken :=
  if exported then [printPub, printTagged, printTypeDecl] else [printTagged, printTypeDecl]

def taggedDeclarationPrefix (exported : Bool) : List Token :=
  if exported then [keyword "pub", keyword "tagged", keyword "type"] else [keyword "tagged", keyword "type"]

def VariantMember.printPieces (member : VariantMember) : List PrintedToken :=
  member.label.print :: (match member.payload with
    | none => []
    | some written => printOpen :: written.printPieces ++ [printClose])

inductive VariantMemberRead : List Token → VariantMember → List Token → Prop where
  | nullary (name : Identifier) (closed : ∀ suffix, rest ≠ openParen :: suffix) :
      VariantMemberRead (.word name.val :: rest) ⟨name, none⟩ rest
  | payload (name : Identifier) : TypeReads input written (closeParen :: rest) →
      VariantMemberRead (.word name.val :: openParen :: input) ⟨name, some written⟩ rest

inductive VariantMembersTailRead : List Token → List VariantMember → List Token → Prop where
  | done : VariantMembersTailRead (closeBrace :: rest) [] rest
  | next : VariantMemberRead input member more → VariantMembersTailRead more tail rest →
      VariantMembersTailRead (comma :: input) (member :: tail) rest

end Gabbro.Core.Ast
