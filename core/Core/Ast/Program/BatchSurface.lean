module

public import Core.Ast.Expression.Surface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

def assignVar (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (AssignArgs scope) where
  tree := fun a => ⟨scope, .assignVar a.ref a.visible a.writable a.value a.fits⟩
  production := fun a tokens => ∃ input,
    tokens = .word a.ref.binding.name.val :: assignment :: input ∧
    ExprReads scope 0 input a.value [semicolon]

-- Mirror letValue_print for the declared spelling.
theorem assignVar_print (args : AssignArgs scope) :
    (assignVar scope result).production args (((Category.statement scope result).printPieces ((assignVar scope result).tree args)).map PrintedToken.value) := by
  unfold assignVar
  simp only [Category.printPieces, Stmt.printTokens, Stmt.printPieces, Expr.printTokens,
    printAssignment, printSemicolon, Identifier.print, printPunctuation,
    PrintedToken.unquoted, String.reduceToList, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  exact ⟨_, rfl, args.value.printReads (rest := [semicolon]) noOperatorAtSemicolon⟩

-- Mirror letValue_entry by applying the new production and its child proofs.
theorem assignVar_reads (scope : Scope) (result : Option (Ty .value)) (args : AssignArgs scope)
    (read : (assignVar scope result).production args tokens) : (Category.statement scope result).reads tokens ((assignVar scope result).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .assignVar args.ref args.visible args.writable args.fits read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem assignVar_erfuellbar  : ∃ (scope : Scope) (result : Option (Ty .value)), (assignVar scope result).Satisfiable := by
  let name : Identifier := keywordName 'x' [] (by decide) (by intro c h; cases h)
  let scope : Scope := [⟨name, .int 1 1, true, false⟩]
  let args : AssignArgs scope := ⟨.here, ⟨trivial, trivial⟩, rfl, .lit 1, ⟨by decide, by decide⟩⟩
  exact ⟨scope, none, Rule.satisfiableOfPrint args (assignVar_print args)⟩

def returnValue (scope : Scope) (expected : Ty .value) : Rule (.statement scope (some expected)) (ReturnArgs scope expected) where
  tree := fun a => ⟨scope, .ret rfl a.value a.fits⟩
  production := fun a tokens => ∃ input,
    tokens = returnKeyword :: input ∧ ExprReads scope 0 input a.value [semicolon]

-- Mirror letValue_print for the declared spelling.
theorem returnValue_print (args : ReturnArgs scope expected) :
    (returnValue scope expected).production args (((Category.statement scope (some expected)).printPieces ((returnValue scope expected).tree args)).map PrintedToken.value) := by
  change (returnValue scope expected).production args (Stmt.ret rfl args.value args.fits).printTokens
  unfold returnValue
  simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  exact ⟨_, rfl, args.value.printReads (rest := [semicolon]) noOperatorAtSemicolon⟩

-- Mirror letValue_entry by applying the new production and its child proofs.
theorem returnValue_reads (scope : Scope) (expected : Ty .value) (args : ReturnArgs scope expected)
    (read : (returnValue scope expected).production args tokens) : (Category.statement scope (some expected)).reads tokens ((returnValue scope expected).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .ret rfl args.fits read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem returnValue_erfuellbar  : ∃ (scope : Scope) (expected : Ty .value), (returnValue scope expected).Satisfiable := by
  let args : ReturnArgs [] (.int 1 1) := ⟨.lit 1, ⟨by decide, by decide⟩⟩
  exact ⟨[], .int 1 1, Rule.satisfiableOfPrint args (returnValue_print args)⟩

def ifElse (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (IfArgs scope result) where
  tree := fun a => ⟨scope, .ite a.condition a.yes a.no⟩
  production := fun a tokens => ∃ input first more,
    tokens = ifKeyword :: input ∧ ExprReads scope 0 input a.condition first ∧
    BlockReads result scope first a.yes (elseKeyword :: more) ∧ BlockReads result scope more a.no []

-- Mirror Block.printItems_reads for the declared spelling.
theorem ifElse_print (args : IfArgs scope result) :
    (ifElse scope result).production args (((Category.statement scope result).printPieces ((ifElse scope result).tree args)).map PrintedToken.value) := by
  change (ifElse scope result).production args (Stmt.ite args.condition args.yes args.no).printTokens
  unfold ifElse
  simp only [Stmt.printTokens, Stmt.printPieces, BracedBlock.printPieces, Expr.printTokens,
    printOpenBrace, printCloseBrace, ifName, elseName, Identifier.print, printPunctuation,
    PrintedToken.unquoted, keywordName, ifKeyword, elseKeyword, String.reduceToList,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  refine ⟨args.condition.printTokens ++ args.yes.printPieces.map PrintedToken.value ++
      elseKeyword :: args.no.printPieces.map PrintedToken.value,
    args.yes.printPieces.map PrintedToken.value ++ elseKeyword :: args.no.printPieces.map PrintedToken.value,
    args.no.printPieces.map PrintedToken.value, ?_, ?_, ?_, ?_⟩
  · simpa only [Expr.printTokens, elseKeyword, String.reduceToList, List.append_assoc]
  · have hb : ¬ Continues 0
        (args.yes.printPieces.map PrintedToken.value ++ elseKeyword ::
          args.no.printPieces.map PrintedToken.value) := by
      cases args.yes with
      | braces body =>
        simp only [BracedBlock.printPieces, printOpenBrace, printPunctuation,
          PrintedToken.unquoted, String.reduceToList, List.map_append, List.map_cons,
          List.map_nil, List.cons_append]
        exact noOperatorAtOpenBrace
    simpa only [List.append_assoc] using
      (args.condition.printReads hb)
  · exact args.yes.printReads _
  · simpa only [List.append_nil] using args.no.printReads []

-- Mirror BracedBlock.printReads by applying the new production and its child proofs.
theorem ifElse_reads (scope : Scope) (result : Option (Ty .value)) (args : IfArgs scope result)
    (read : (ifElse scope result).production args tokens) : (Category.statement scope result).reads tokens ((ifElse scope result).tree args) := by
  obtain ⟨input, first, more, rfl, condRead, yesRead, noRead⟩ := read
  exact .ite condRead yesRead noRead

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem ifElse_erfuellbar (scope : Scope) (result : Option (Ty .value)) : (ifElse scope result).Satisfiable := by
  let args : IfArgs scope result := ⟨.trueLit, .braces .done, .braces .done⟩
  exact Rule.satisfiableOfPrint args (ifElse_print args)

theorem ifElse_entry (scope : Scope) (result : Option (Ty .value)) : (ifElse scope result).Entry where
  reads := fun a _ => ifElse_reads scope result a
  prints := ifElse_print
  erfuellbar := ifElse_erfuellbar scope result

def braced (scope : Scope) (result : Option (Ty .value)) : Rule (.block scope result) (Statements result scope) where
  tree := fun body => .braces body.2
  production := fun body tokens => ∃ input, tokens = openBrace :: input ∧ BlockItems result scope input body []

-- Mirror Block.printItems_reads for the declared spelling.
theorem braced_print (args : Statements result scope) :
    (braced scope result).production args (((Category.block scope result).printPieces ((braced scope result).tree args)).map PrintedToken.value) := by
  change (braced scope result).production args
    ((BracedBlock.braces args.2).printPieces.map PrintedToken.value)
  unfold braced
  simp only [BracedBlock.printPieces, printOpenBrace, printCloseBrace, printPunctuation,
    PrintedToken.unquoted, String.reduceToList, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  exact ⟨args.2.printItems.map PrintedToken.value ++ [closeBrace], rfl,
    Block.printItems_reads args.2 []⟩

-- Mirror BracedBlock.printReads by applying the new production and its child proofs.
theorem braced_reads (scope : Scope) (result : Option (Ty .value)) (args : Statements result scope)
    (read : (braced scope result).production args tokens) : (Category.block scope result).reads tokens ((braced scope result).tree args) := by
  obtain ⟨input, rfl, read⟩ := read
  exact .braced read

-- Mirror Rule.satisfiableOfPrint with a typed concrete constructor argument.
theorem braced_erfuellbar (scope : Scope) (result : Option (Ty .value)) : (braced scope result).Satisfiable := by
  let args : Statements result scope := ⟨scope, .done⟩
  exact Rule.satisfiableOfPrint args (braced_print args)

theorem braced_entry (scope : Scope) (result : Option (Ty .value)) : (braced scope result).Entry where
  reads := fun a _ => braced_reads scope result a
  prints := braced_print
  erfuellbar := braced_erfuellbar scope result


abbrev SubtractArgs (scope : Scope) := {a : BinaryArgs scope // a.op = .sub}

def subtraction (scope : Scope) : Rule (.expression scope) (SubtractArgs scope) where
  tree := fun args => (binary scope).tree args.val
  production := fun args tokens => (binary scope).production args.val tokens

-- Mirror binary_print with Arith.sub and its token spelling.
theorem subtraction_print (args : SubtractArgs scope) :
    (subtraction scope).production args
      (((Category.expression scope).printPieces ((subtraction scope).tree args)).map PrintedToken.value) := by
  exact binary_print args.val

-- Mirror BinaryArgs.readStep_sound with Arith.sub.
theorem subtraction_reads (scope : Scope) (args : SubtractArgs scope)
    (read : (subtraction scope).production args tokens) :
    (Category.expression scope).reads tokens ((subtraction scope).tree args) := by
  exact (binary_entry scope).reads args.val tokens read

-- Mirror binary_erfuellbar using the token sequence 5 - 2.
theorem subtraction_erfuellbar (scope : Scope) : (subtraction scope).Satisfiable := by
  let args : BinaryArgs scope := ⟨.sub, .lit 5, .lit 2⟩
  exact Rule.satisfiableOfPrint ⟨args, rfl⟩ (binary_print args)

theorem subtraction_entry (scope : Scope) : (subtraction scope).Entry where
  reads := fun a _ => subtraction_reads scope a
  prints := subtraction_print
  erfuellbar := subtraction_erfuellbar scope

theorem variable_entry (args : VariableArgs scope) : (localValue scope).Entry where
  reads := fun a _ => variable_reads scope a
  prints := variable_print
  erfuellbar := Rule.satisfiableOfPrint args (variable_print args)

theorem assignVar_entry (args : AssignArgs scope) (result : Option (Ty .value)) :
    (assignVar scope result).Entry where
  reads := fun a _ => assignVar_reads scope result a
  prints := assignVar_print
  erfuellbar := Rule.satisfiableOfPrint args (assignVar_print args)

theorem returnValue_entry (args : ReturnArgs scope expected) : (returnValue scope expected).Entry where
  reads := fun a _ => returnValue_reads scope expected a
  prints := returnValue_print
  erfuellbar := Rule.satisfiableOfPrint args (returnValue_print args)

end Gabbro.Core.Ast.Surface
