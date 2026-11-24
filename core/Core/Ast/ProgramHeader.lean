module

public import Core.Ast.Print

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def arrow : Token := .punctuation "->".toList
def closedRange : Token := .punctuation "..".toList
def openRange : Token := .punctuation "..<".toList

def keyword (word : String) : Token := .word word.toList

def printArrow : PrintedToken := printPunctuation "->" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by sorry)
def printClosedRange : PrintedToken := printSliceRange
def printOpenRange : PrintedToken := printPunctuation "..<" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by sorry)

/-- The finite keywords used by these productions are unquoted words. -/
def printProgramWord (head : Char) (tail : List Char) (first : 'a' ≤ head ∧ head ≤ 'z')
    (rest : ∀ c ∈ tail, 'a' ≤ c ∧ c ≤ 'z') : PrintedToken :=
  (keywordName head tail first rest).print

-- Mirror returnName and the punctuationHead lemma for each new terminal.
def printConst : PrintedToken := printProgramWord 'c' ['o', 'n', 's', 't'] (by decide) (by sorry)
def printFn : PrintedToken := printProgramWord 'f' ['n'] (by decide) (by sorry)
def printBoolType : PrintedToken := printProgramWord 'b' ['o', 'o', 'l'] (by decide) (by sorry)
def printIn : PrintedToken := printProgramWord 'i' ['n'] (by decide) (by sorry)
def printMut : PrintedToken := printProgramWord 'm' ['u', 't'] (by decide) (by sorry)
def printWhile : PrintedToken := printProgramWord 'w' ['h', 'i', 'l', 'e'] (by decide) (by sorry)
def printBounded : PrintedToken := printProgramWord 'b' ['o', 'u', 'n', 'd', 'e', 'd'] (by decide) (by sorry)
def printOps : PrintedToken := printProgramWord 'o' ['p', 's'] (by decide) (by sorry)
def printFor : PrintedToken := printProgramWord 'f' ['o', 'r'] (by decide) (by sorry)
def printDecreases : PrintedToken :=
  printProgramWord 'd' ['e', 'c', 'r', 'e', 'a', 's', 'e', 's'] (by decide) (by sorry)

-- Mirror Identifier.print with an underscore allowed in the tail.
def printOnExceeded : PrintedToken :=
  Identifier.print ⟨"on_exceeded".toList, 'o', "n_exceeded".toList, rfl, by sorry, by sorry⟩

def intSpelling (signed : Bool) (width : Nat) : List Char :=
  (if signed then 'i' else 'u') :: (toString width).toList

-- Mirror printInteger.lexeme using the decimal digit tail of the width.
def intTypeName (signed : Bool) (width : Nat) : Identifier :=
  ⟨intSpelling signed width, (if signed then 'i' else 'u'), (toString width).toList, rfl, by sorry, by sorry⟩

def signedPieces (number : Int) : List PrintedToken :=
  if number < 0 then [Arith.sub.print, printInteger number.natAbs] else [printInteger number.natAbs]

def printStringType : PrintedToken := printProgramWord 's' ['t', 'r', 'i', 'n', 'g']
  (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

def printMax : PrintedToken := printProgramWord 'm' ['a', 'x'] (by decide)
  (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl) <;> decide)

def printIndex : PrintedToken := printProgramWord 'i' ['n', 'd', 'e', 'x'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl) <;> decide)

def printInto : PrintedToken := printProgramWord 'i' ['n', 't', 'o'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl) <;> decide)

def printOption : PrintedToken := printProgramWord 'o' ['p', 't', 'i', 'o', 'n'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

mutual


def WrittenType.printPieces : WrittenType → List PrintedToken
  | .bool => [printBoolType]
  | .integer signed width none => [(intTypeName signed width).print]
  | .integer signed width (some (lo, hi)) =>
    [(intTypeName signed width).print, printIn] ++ signedPieces lo ++ [printClosedRange] ++ signedPieces hi
  | .array element count => [printOpenBracket] ++ element.printPieces ++
      [printSemicolon, printInteger count, printCloseBracket]
  | .tuple first second rest => [printOpen] ++ first.printPieces ++ [printComma] ++
      second.printPieces ++ rest.printTail ++ [printClose]
  | .text capacity => [printStringType, printMax, printInteger capacity]
  | .index carrier _ => [printIndex, printInto, carrier.print]
  | .indexOption carrier _ => [printOption, printIndex, printInto, carrier.print]

def WrittenTypes.printTail : WrittenTypes → List PrintedToken
  | .empty => []
  | .next head tail => printComma :: head.printPieces ++ tail.printTail

end

inductive SignedReads : List Token → Int → List Token → Prop where
  | positive : SignedReads (.natural n :: rest) n rest
  | negative : SignedReads (minus :: .natural n :: rest) (-(n : Int)) rest

mutual

inductive TypeReads (scope : Scope) : List Token → WrittenType → List Token → Prop where
  | bool : TypeReads scope (keyword "bool" :: rest) .bool rest
  | integer (valid : (WrittenType.integer signed width none).valid scope)
      (closed : ∀ more, rest ≠ keyword "in" :: more) :
      TypeReads scope (.word (intSpelling signed width) :: rest) (.integer signed width none) rest
  | interval (valid : (WrittenType.integer signed width (some (lo, hi))).valid scope) :
      SignedReads input lo (closedRange :: more) → SignedReads more hi rest →
      TypeReads scope (.word (intSpelling signed width) :: keyword "in" :: input)
        (.integer signed width (some (lo, hi))) rest
  | array (count : Nat) (bound : Expr [] (.int count count)) :
      TypeReads scope input element (semicolon :: boundInput) →
      ExprReads [] 0 boundInput bound (closeBracket :: rest) →
      TypeReads scope (openBracket :: input) (.array element count) rest
  | tuple : TypeReads scope input first (comma :: secondInput) → TypeReads scope secondInput second more →
      TypeItemsTail scope more tail rest → TypeReads scope (openParen :: input) (.tuple first second tail) rest
  | text : TypeReads scope (keyword "string" :: keyword "max" :: .natural capacity :: rest) (.text capacity) rest
  | index (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "index" :: keyword "into" :: .word carrier.val :: rest) (.index carrier count) rest
  | indexOption (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "option" :: keyword "index" :: keyword "into" :: .word carrier.val :: rest)
        (.indexOption carrier count) rest

inductive TypeItemsTail (scope : Scope) : List Token → WrittenTypes → List Token → Prop where
  | close : TypeItemsTail scope (closeParen :: rest) .empty rest
  | comma : TypeReads scope input head more → TypeItemsTail scope more tail rest →
      TypeItemsTail scope (comma :: input) (.next head tail) rest

end

def Parameter.printPieces (p : Parameter scope) : List PrintedToken :=
  [p.name.print, printColon] ++ p.written.printPieces

mutual
inductive ParamsRead (scope : Scope) : List Token → List (Parameter scope) → List Token → Prop where
  | empty : ParamsRead scope (closeParen :: rest) [] rest
  | first (p : Parameter scope) : TypeReads scope input p.written more → ParamsTail scope more ps rest →
      ParamsRead scope (.word p.name.val :: colon :: input) (p :: ps) rest

inductive ParamsTail (scope : Scope) : List Token → List (Parameter scope) → List Token → Prop where
  | close : ParamsTail scope (closeParen :: rest) [] rest
  | comma : ParamsRead scope input ps rest → ParamsTail scope (comma :: input) ps rest
end

mutual
inductive ArgsRead (scope : Scope) : List Token → List (TypedExpr scope) → List Token → Prop where
  | empty : ArgsRead scope (closeParen :: rest) [] rest
  | first : ExprReads scope 0 input e more → ArgsTail scope more es rest →
      ArgsRead scope input (e.typed :: es) rest

inductive ArgsTail (scope : Scope) : List Token → List (TypedExpr scope) → List Token → Prop where
  | close : ArgsTail scope (closeParen :: rest) [] rest
  | comma : ArgsRead scope input es rest → ArgsTail scope (comma :: input) es rest
end

def commaSeparated (pieces : List (List PrintedToken)) : List PrintedToken :=
  (pieces.intersperse [printComma]).flatten

def DirectCall.printPieces (call : DirectCall scope) : List PrintedToken :=
  [call.name.print, printOpen] ++ commaSeparated (call.args.map (fun exp => exp.2.printPieces)) ++ [printClose]

inductive CallReads (scope : Scope) : List Token → DirectCall scope → List Token → Prop where
  | applied (call : DirectCall scope) : ArgsRead scope input call.args rest →
      CallReads scope (.word call.name.val :: openParen :: input) call rest

-- Mirror AtomReads.lit_inversion and exclude the signed arm by token kind.
theorem SignedReads.deterministic (left : SignedReads input a rest) (right : SignedReads input b more) :
    a = b ∧ rest = more := by
  sorry

-- Mirror ExprReads.deterministic, dispatch on the width spelling and then on in.
theorem TypeReads.deterministic (left : TypeReads scope input a rest) (right : TypeReads scope input b more) :
    a = b ∧ rest = more := by
  sorry

-- Mirror ExprReads.consumes for the signed interval endpoints.
theorem TypeReads.consumes (read : TypeReads scope input a rest) : rest <:+ input := by
  sorry

-- Mirror Expr.printReads with the range suffix discriminator.
theorem WrittenType.printReads (tree : WrittenType) (valid : tree.valid scope)
    (closed : ∀ more, rest ≠ keyword "in" :: more) :
    TypeReads scope (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  sorry

-- Mirror BlockItems.deterministic, applying TypeReads.deterministic to each parameter.
theorem ParamsRead.deterministic (left : ParamsRead scope input a rest) (right : ParamsRead scope input b more) :
    a = b ∧ rest = more := by
  sorry

-- Mirror BlockItems.consumes, including the final close parenthesis.
theorem ParamsRead.consumes (read : ParamsRead scope input ps rest) : rest <:+ input := by
  sorry

-- Mirror Block.printItems_reads with commas between the ordered parameters.
theorem ParamsRead.printReads (ps : List (Parameter scope)) :
    ParamsRead scope ((commaSeparated (ps.map Parameter.printPieces) ++ [printClose]).map PrintedToken.value ++ rest)
      ps rest := by
  sorry

-- Mirror BlockItems.deterministic and apply ExprReads.deterministic at each argument.
theorem ArgsRead.deterministic (left : ArgsRead scope input a rest) (right : ArgsRead scope input b more) :
    a = b ∧ rest = more := by
  sorry

-- Mirror BlockItems.consumes and compose expression suffixes.
theorem ArgsRead.consumes (read : ArgsRead scope input args rest) : rest <:+ input := by
  sorry

-- Mirror StmtReads.assign_inversion for the written name and parenthesized argument suffix.
theorem CallReads.inversion (read : CallReads scope input call rest) :
    ∃ args, input = .word call.name.val :: openParen :: args ∧ ArgsRead scope args call.args rest := by
  sorry

-- Mirror StmtReads.deterministic and use ArgsRead.deterministic.
theorem CallReads.deterministic (left : CallReads scope input a rest) (right : CallReads scope input b more) :
    a = b ∧ rest = more := by
  sorry

-- Mirror StmtReads.consumes using ArgsRead.consumes.
theorem CallReads.consumes (read : CallReads scope input call rest) : rest <:+ input := by
  sorry

-- Mirror BracedBlock.printReads using Expr.printReads before close parentheses or commas.
theorem DirectCall.printReads (call : DirectCall scope) :
    CallReads scope (call.printPieces.map PrintedToken.value ++ rest) call rest := by
  sorry

end Gabbro.Core.Ast
