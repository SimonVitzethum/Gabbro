module

public import Core.Ast.BatchSurface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text


structure ReturnVoidArgs (scope : Scope) (result : Option (Ty .value)) : Type where
  declared : result = none

/-- SYNTAX §6, explicit void return. -/
def returnVoid (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (ReturnVoidArgs scope result) where
  tree := fun a => ⟨_, .retVoid a.declared⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .retVoid a.declared⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem returnVoid_print {scope : Scope} {result : Option (Ty .value)} (a : ReturnVoidArgs scope result) :
    (returnVoid scope result).production a (((Category.statement scope result).printPieces ((returnVoid scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem returnVoid_reads {scope : Scope} {result : Option (Ty .value)} {a : ReturnVoidArgs scope result} {tokens : List Token}
    (read : (returnVoid scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((returnVoid scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem returnVoid_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) (void : result = none) :
    (returnVoid scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem returnVoid_entry (scope : Scope) (result : Option (Ty .value)) (void : result = none) : (returnVoid scope result).Entry :=
  ⟨fun _ _ => returnVoid_reads, returnVoid_print, returnVoid_syntax_erfuellbar scope result void⟩

structure MutableLocalArgs (scope : Scope) (result : Option (Ty .value)) where
  name : Identifier
  ordinary : ordinaryLocal name
  written : WrittenType
  valid : written.valid scope
  type : Ty .value
  value : Expr scope type
  fits : Fits type written.type

/-- SYNTAX §7, scalar mutable local. -/
def mutableLocal (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (MutableLocalArgs scope result) where
  tree := fun a => ⟨_, .letMutable a.name a.ordinary a.written a.valid a.value a.fits⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .letMutable a.name a.ordinary a.written a.valid a.value a.fits⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem mutableLocal_print {scope : Scope} {result : Option (Ty .value)} (a : MutableLocalArgs scope result) :
    (mutableLocal scope result).production a (((Category.statement scope result).printPieces ((mutableLocal scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem mutableLocal_reads {scope : Scope} {result : Option (Ty .value)} {a : MutableLocalArgs scope result} {tokens : List Token}
    (read : (mutableLocal scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((mutableLocal scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem mutableLocal_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) :
    (mutableLocal scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem mutableLocal_entry (scope : Scope) (result : Option (Ty .value)) : (mutableLocal scope result).Entry :=
  ⟨fun _ _ => mutableLocal_reads, mutableLocal_print, mutableLocal_syntax_erfuellbar scope result⟩

abbrev DirectCallArgs (scope : Scope) (_result : Option (Ty .value)) := DirectCall scope

/-- syntax.call and surface.SAnw.call. -/
def directCall (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (DirectCallArgs scope result) where
  tree := fun a => ⟨_, .directCall a⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .directCall a⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem directCall_print {scope : Scope} {result : Option (Ty .value)} (a : DirectCallArgs scope result) :
    (directCall scope result).production a (((Category.statement scope result).printPieces ((directCall scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem directCall_reads {scope : Scope} {result : Option (Ty .value)} {a : DirectCallArgs scope result} {tokens : List Token}
    (read : (directCall scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((directCall scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem directCall_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) :
    (directCall scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem directCall_entry (scope : Scope) (result : Option (Ty .value)) : (directCall scope result).Entry :=
  ⟨fun _ _ => directCall_reads, directCall_print, directCall_syntax_erfuellbar scope result⟩

structure BindDirectArgs (scope : Scope) (result : Option (Ty .value)) where
  name : Identifier
  ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name
  written : WrittenType
  valid : written.valid scope
  call : DirectCall scope

/-- SYNTAX §7, typed result binding. -/
def bindDirect (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (BindDirectArgs scope result) where
  tree := fun a => ⟨_, .bindDirect a.name a.ordinary a.written a.valid a.call⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .bindDirect a.name a.ordinary a.written a.valid a.call⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem bindDirect_print {scope : Scope} {result : Option (Ty .value)} (a : BindDirectArgs scope result) :
    (bindDirect scope result).production a (((Category.statement scope result).printPieces ((bindDirect scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem bindDirect_reads {scope : Scope} {result : Option (Ty .value)} {a : BindDirectArgs scope result} {tokens : List Token}
    (read : (bindDirect scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((bindDirect scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem bindDirect_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) :
    (bindDirect scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem bindDirect_entry (scope : Scope) (result : Option (Ty .value)) : (bindDirect scope result).Entry :=
  ⟨fun _ _ => bindDirect_reads, bindDirect_print, bindDirect_syntax_erfuellbar scope result⟩

structure BoundedWhileArgs (scope : Scope) (result : Option (Ty .value)) where
  condition : Expr scope .bool
  lo : Int
  hi : Int
  bound : Expr scope (.int lo hi)
  staticBound : bound.static
  nonnegative : 0 ≤ lo
  overflow : Identifier
  body : BracedBlock result scope

/-- syntax.whileloop and surface.SBoundedHeader.whileLoop. -/
def boundedWhile (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (BoundedWhileArgs scope result) where
  tree := fun a => ⟨_, .whileBounded a.condition a.bound a.staticBound a.nonnegative a.overflow a.body⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .whileBounded a.condition a.bound a.staticBound a.nonnegative a.overflow a.body⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem boundedWhile_print {scope : Scope} {result : Option (Ty .value)} (a : BoundedWhileArgs scope result) :
    (boundedWhile scope result).production a (((Category.statement scope result).printPieces ((boundedWhile scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem boundedWhile_reads {scope : Scope} {result : Option (Ty .value)} {a : BoundedWhileArgs scope result} {tokens : List Token}
    (read : (boundedWhile scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((boundedWhile scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem boundedWhile_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) :
    (boundedWhile scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem boundedWhile_entry (scope : Scope) (result : Option (Ty .value)) : (boundedWhile scope result).Entry :=
  ⟨fun _ _ => boundedWhile_reads, boundedWhile_print, boundedWhile_syntax_erfuellbar scope result⟩

structure ForRangeArgs (scope : Scope) (result : Option (Ty .value)) where
  name : Identifier
  ordinary : ordinaryLocal name
  lo : Int
  loHi : Int
  hiLo : Int
  hi : Int
  lower : Expr scope (.int lo loHi)
  upper : Expr scope (.int hiLo hi)
  staticBounds : lower.static ∧ upper.static
  overflow : Option Identifier
  body : BracedBlock result (rangeBinding name lo hi :: scope)

/-- SYNTAX §8 and surface.SBoundedHeader.forRange. -/
def forRange (scope : Scope) (result : Option (Ty .value)) : Rule (.statement scope result) (ForRangeArgs scope result) where
  tree := fun a => ⟨_, .forRange a.name a.ordinary a.lower a.upper a.staticBounds a.overflow a.body⟩
  production := fun a tokens => StmtReads result scope tokens ⟨_, .forRange a.name a.ordinary a.lower a.upper a.staticBounds a.overflow a.body⟩ []

-- Mirror Stmt.printReads for the canonical derivation.
theorem forRange_print {scope : Scope} {result : Option (Ty .value)} (a : ForRangeArgs scope result) :
    (forRange scope result).production a (((Category.statement scope result).printPieces ((forRange scope result).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem forRange_reads {scope : Scope} {result : Option (Ty .value)} {a : ForRangeArgs scope result} {tokens : List Token}
    (read : (forRange scope result).production a tokens) :
    (Category.statement scope result).reads tokens ((forRange scope result).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem forRange_syntax_erfuellbar (scope : Scope) (result : Option (Ty .value)) :
    (forRange scope result).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem forRange_entry (scope : Scope) (result : Option (Ty .value)) : (forRange scope result).Entry :=
  ⟨fun _ _ => forRange_reads, forRange_print, forRange_syntax_erfuellbar scope result⟩

structure ConstantArgs (scope : Scope) where
  name : Identifier
  ordinary : ordinaryLocal name
  written : WrittenType
  valid : written.valid scope
  type : Ty .value
  value : Expr scope type
  staticValue : value.static
  fits : Fits type written.type

/-- syntax.constdecl and surface.SItemTief.constT. -/
def constant (scope : Scope) : Rule (.declaration scope) (ConstantArgs scope) where
  tree := fun a => ⟨_, .constant a.name a.ordinary a.written a.valid a.value a.staticValue a.fits⟩
  production := fun a tokens => DeclReads scope tokens ⟨_, .constant a.name a.ordinary a.written a.valid a.value a.staticValue a.fits⟩ []

-- Mirror Decl.printReads for the canonical derivation.
theorem constant_print {scope : Scope} (a : ConstantArgs scope) :
    (constant scope).production a (((Category.declaration scope).printPieces ((constant scope).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem constant_reads {scope : Scope} {a : ConstantArgs scope} {tokens : List Token}
    (read : (constant scope).production a tokens) :
    (Category.declaration scope).reads tokens ((constant scope).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem constant_syntax_erfuellbar (scope : Scope) :
    (constant scope).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem constant_entry (scope : Scope) : (constant scope).Entry :=
  ⟨fun _ _ => constant_reads, constant_print, constant_syntax_erfuellbar scope⟩

structure FunctionArgs (scope : Scope) where
  name : Identifier
  ordinary : directName name
  parameters : List (Parameter scope)
  result : Option WrittenType
  valid : ∀ t ∈ result.toList, WrittenType.valid scope t
  measure : Option (Measure (functionScope scope parameters))
  body : BracedBlock (writtenResult result) (functionScope scope parameters)
  distinct : (parameters.map (fun p => p.name.val)).Nodup
  returns : result.isSome = true → body.returns = true
  effects : Option (EffectClause scope parameters) := none

def FunctionArgs.declaration (a : FunctionArgs scope) : Decl scope scope :=
  .function a.name a.ordinary a.parameters a.result a.valid a.measure a.body a.distinct a.returns a.effects

/-- syntax.fndecl and surface.SItemTief.fnT. -/
def function (scope : Scope) : Rule (.declaration scope) (FunctionArgs scope) where
  tree := fun a => ⟨_, a.declaration⟩
  production := fun a tokens => DeclReads scope tokens ⟨_, a.declaration⟩ []

-- Mirror Decl.printReads for the canonical derivation.
theorem function_print {scope : Scope} (a : FunctionArgs scope) :
    (function scope).production a (((Category.declaration scope).printPieces ((function scope).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem function_reads {scope : Scope} {a : FunctionArgs scope} {tokens : List Token}
    (read : (function scope).production a tokens) :
    (Category.declaration scope).reads tokens ((function scope).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem function_syntax_erfuellbar (scope : Scope) :
    (function scope).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem function_entry (scope : Scope) : (function scope).Entry :=
  ⟨fun _ _ => function_reads, function_print, function_syntax_erfuellbar scope⟩

structure ProgramArgs where
  middle : Scope
  after : Scope
  first : Decl [] middle
  rest : UnitBody middle after

def ProgramArgs.unit (a : ProgramArgs) : Ast.Unit := ⟨a.after, .step a.first a.rest⟩

/-- syntax.program, ordinary entry selected as main. -/
def program  : Rule (.unit) (ProgramArgs) where
  tree := ProgramArgs.unit
  production := fun a tokens => UnitReads [] tokens a.unit

-- Mirror UnitBody.printReads for the canonical derivation.
theorem program_print (a : ProgramArgs) :
    (program).production a (((Category.unit).printPieces ((program).tree a)).map PrintedToken.value) := by
  sorry

-- Mirror Rule.Entry.reads using the corresponding production constructor.
theorem program_reads {a : ProgramArgs} {tokens : List Token}
    (read : (program).production a tokens) :
    (Category.unit).reads tokens ((program).tree a) := by
  sorry

-- Mirror Rule.satisfiableOfPrint with concrete arguments for this production.
theorem program_syntax_erfuellbar  :
    (program).Satisfiable := by
  sorry

-- Mirror Rule.Entry.parse, using the canonical printer and the joint syntax proof.
theorem program_entry  : (program).Entry :=
  ⟨fun _ _ => program_reads, program_print, program_syntax_erfuellbar ⟩

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def OptionLetReadAt (result : Option (Ty .value)) (scope : Scope) (mutable : Bool)
    (spelling : RawText) (input : List Token) (tree : Statement result scope) (rest : List Token) : Prop :=
  ∃ (name carrier : Identifier) (count : Nat)
    (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
    (resolved : scope.carrierCount carrier = some count) (value : OptionInitializer scope count) rhs,
    name.val = spelling ∧ TypeReads scope input (.indexOption carrier count) (assignment :: rhs) ∧
    OptionInitializerReads scope count rhs value (semicolon :: rest) ∧
    tree = ⟨_, .letOption mutable name ordinary carrier resolved value⟩

-- Mirror StmtReads.ret_inversion using the semicolon discriminator.
theorem StmtReads.returnVoid_inversion
    (read : StmtReads result scope (returnKeyword :: semicolon :: input) tree rest) :
    ∃ (a : Surface.ReturnVoidArgs scope result),
      tree = (Surface.returnVoid scope result).tree a ∧ rest = input := by
  sorry

-- Mirror StmtReads.let_header using the mutable annotated header.
theorem StmtReads.mutableLocal_inversion
    (read : StmtReads result scope (letKeyword :: keyword "mut" :: .word spelling :: colon :: input)
      tree rest) :
    (∃ (a : Surface.MutableLocalArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      ExprReads scope 0 rhs a.value (semicolon :: rest) ∧
      tree = (Surface.mutableLocal scope result).tree a) ∨
    OptionLetReadAt result scope true spelling input tree rest := by
  sorry

-- Mirror CallReads.inversion after disambiguating the reserved statement heads.
theorem StmtReads.directCall_inversion (name : Identifier) (ordinary : directName name)
    (read : StmtReads result scope (.word name.val :: openParen :: input) tree rest) :
    ∃ (a : Surface.DirectCallArgs scope result),
      a.name = name ∧ ArgsRead scope input a.args (semicolon :: rest) ∧
      tree = (Surface.directCall scope result).tree a := by
  sorry

-- Mirror StmtReads.let_header with the written type and the call's argument derivation.
theorem StmtReads.bindDirect_inversion
    (read : StmtReads result scope (letKeyword :: .word spelling :: colon :: input) tree rest) :
    (∃ (a : Surface.BindDirectArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      CallReads scope rhs a.call (semicolon :: rest) ∧
      tree = (Surface.bindDirect scope result).tree a) ∨
    OptionLetReadAt result scope false spelling input tree rest := by
  sorry

-- Mirror StmtReads.ite_inversion and retain the distinct bound and body derivations.
theorem StmtReads.boundedWhile_inversion
    (read : StmtReads result scope (keyword "while" :: input) tree rest) :
    (∃ (a : Surface.BoundedWhileArgs scope result) (boundInput bodyInput : List Token),
      ExprReads scope 0 input a.condition (keyword "bounded" :: boundInput) ∧
      ExprReads scope 0 boundInput a.bound
        (keyword "ops" :: keyword "on_exceeded" :: .word a.overflow.val :: bodyInput) ∧
      BlockReads result scope bodyInput a.body rest ∧
      tree = (Surface.boundedWhile scope result).tree a) ∨
    (∃ tail, input = assignment :: tail) := by
  sorry

-- Mirror StmtReads.boundedWhile_inversion, using the distinct range separator.
theorem StmtReads.forRange_inversion
    (read : StmtReads result scope (keyword "for" :: .word spelling :: keyword "in" :: input) tree rest) :
    ∃ (a : Surface.ForRangeArgs scope result) (highInput handlerInput bodyInput : List Token),
      a.name.val = spelling ∧ ExprReads scope 0 input a.lower (openRange :: highInput) ∧
      ExprReads scope 0 highInput a.upper handlerInput ∧
      OverflowReads handlerInput a.overflow bodyInput ∧
      BlockReads result (rangeBinding a.name a.lo a.hi :: scope) bodyInput a.body rest ∧
      tree = (Surface.forRange scope result).tree a := by
  sorry

-- Mirror UnitBody.printReads and recover the first declaration's unconsumed suffix.
theorem UnitReads.program_inversion (a : Surface.ProgramArgs) (read : UnitReads [] tokens a.unit) :
    ∃ rest, DeclReads [] tokens ⟨a.middle, a.first⟩ rest ∧
      UnitReads a.middle rest ⟨a.after, a.rest⟩ := by
  sorry

end Gabbro.Core.Ast
