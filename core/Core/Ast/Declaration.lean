module

public import Core.Ast.Print

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

abbrev Declaration (before : Scope) := (after : Scope) × Decl before after

/-- Declaration productions enter with their corresponding AST constructors. -/
inductive DeclReads (before : Scope) : List Token → Declaration before → List Token → Prop where

theorem DeclReads.deterministic (left : DeclReads before input a rest)
    (_right : DeclReads before input b rest') : a = b ∧ rest = rest' :=
  nomatch left

theorem DeclReads.disjoint_end : ¬ DeclReads before [] tree rest := fun read => nomatch read

def Decl.printPieces (tree : Decl before after) : List PrintedToken := nomatch tree

theorem Decl.printReads (tree : Decl before after) (rest : List Token) :
    DeclReads before (tree.printPieces.map PrintedToken.value ++ rest) ⟨after, tree⟩ rest :=
  nomatch tree

end Gabbro.Core.Ast
