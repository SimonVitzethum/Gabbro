module

public import Core.Ast.Block
public import Core.Ast.Unit
public import Core.Text.Syntax

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- A fragment entry point fixes the incoming scope and infers the expression type.
    A source unit begins with an empty scope. -/
inductive Category where
  | expression (scope : Scope)
  | statement (scope : Scope) (result : Option (Ty .value) := none)
  | block (scope : Scope) (result : Option (Ty .value) := none)
  | unit
  | declaration (scope : Scope)

def Category.Tree : Category → Type
  | .expression scope => TypedExpr scope
  | .statement scope result => Statement result scope
  | .block scope result => BracedBlock result scope
  | .unit => Ast.Unit
  | .declaration scope => Declaration scope

def Category.reads : (category : Category) → List Token → category.Tree → Prop
  | .expression scope => fun tokens tree => ExprReads scope 0 tokens tree.2 []
  | .statement scope result => fun tokens tree => StmtReads result scope tokens tree []
  | .block scope result => fun tokens tree => BlockReads result scope tokens tree []
  | .unit => fun tokens tree => UnitReads [] tokens tree
  | .declaration scope => fun tokens tree => DeclReads scope tokens tree []

def Category.printPieces : (category : Category) → category.Tree → List PrintedToken
  | .expression _ => fun tree => tree.2.printPieces
  | .statement _ _ => fun tree => tree.2.printPieces
  | .block _ _ => fun tree => tree.printPieces
  | .unit => fun tree => tree.2.printPieces
  | .declaration _ => fun tree => tree.2.printPieces

theorem Category.unique (category : Category) {tokens : List Token} {a b : category.Tree}
    (left : category.reads tokens a) (right : category.reads tokens b) : a = b := by
  cases category with
  | expression => exact (ExprReads.deterministic left right).1
  | statement => exact (StmtReads.deterministic left right).1
  | block => exact (BlockReads.deterministic left right).1
  | unit => exact UnitReads.deterministic left right
  | declaration => exact (DeclReads.deterministic left right).1

theorem Category.reads_print (category : Category) (tree : category.Tree) :
    category.reads ((category.printPieces tree).map PrintedToken.value) tree := by
  cases category with
  | expression =>
    simpa only [Category.printPieces, Category.reads, Expr.printTokens, List.append_nil] using
      (Expr.printReads (minimum := 0) tree.2 noOperatorAtEnd)
  | statement =>
    rcases tree with ⟨after, tree⟩
    simpa only [Category.printPieces, Category.reads, Stmt.printTokens, List.append_nil] using
      (Stmt.printReads tree [])
  | block => simpa only [Category.reads, Category.printPieces, List.append_nil] using tree.printReads []
  | unit => exact UnitBody.printReads tree.2
  | declaration =>
    rcases tree with ⟨after, tree⟩
    simpa only [Category.reads, Category.printPieces, List.append_nil] using tree.printReads []

def Category.syntax (category : Category) : Syntax category.Tree where
  reads := category.reads
  unique := category.unique
  printPieces := category.printPieces
  reads_print := category.reads_print

def Parse {category : Category} (text : RawText) (tree : category.Tree) : Prop :=
  Text.Parse (tokenGrammar category.reads) text tree

/-- Concrete source rules composed with the elaboration relation supplied by M6. -/
def Bezeichnet {category : Category} (elaborates : category.Tree → Meaning → Prop) :
    RawText → Meaning → Prop := Text.Bezeichnet (tokenGrammar category.reads) elaborates

def print {category : Category} (tree : category.Tree) : RawText := category.syntax.print tree

def Canonicalisation (category : Category) : RawText → RawText → Prop :=
  category.syntax.Canonicalisation

theorem parse_print {category : Category} (tree : category.Tree) :
    Parse (print tree) tree :=
  category.syntax.parse_print tree

theorem parse_deterministic {category : Category} {text : RawText} {a b : category.Tree} :
    Parse text a → Parse text b → a = b :=
  category.syntax.parse_deterministic

theorem bezeichnet_deterministic {category : Category}
    {elaborates : category.Tree → Meaning → Prop}
    (elabDet : ∀ {tree a b}, elaborates tree a → elaborates tree b → a = b)
    (left : Bezeichnet elaborates text a) (right : Bezeichnet elaborates text b) : a = b :=
  category.syntax.bezeichnet_deterministic (elaborates := elaborates) elabDet left right

theorem print_parse {category : Category} {text : RawText} {tree : category.Tree} :
    Parse text tree → Canonicalisation category text (print tree) :=
  category.syntax.print_parse

end Gabbro.Core.Ast
