module

public import Core.Ast.Variant.Grammar
public import Core.Ast.LowLevel.Syntax

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The continuation after the common binding header and initializer. A new
    continuation starts at its own discriminator, such as the word `else`. -/
inductive LetTailReads (result : Option (Ty .value)) (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList)
    (value : Expr scope type) : List Token → Statement result scope → List Token → Prop where
  | plain : LetTailReads result scope name ordinary value (semicolon :: rest)
      ⟨_, .letValue name ordinary value⟩ rest

theorem LetTailReads.plain_inversion
    (read : LetTailReads result scope name ordinary value (semicolon :: rest) tree suffix) :
    tree = ⟨_, .letValue name ordinary value⟩ ∧ suffix = rest := by
  cases read
  exact ⟨rfl, rfl⟩

theorem LetTailReads.deterministic (left : LetTailReads result scope name ordinary value input a rest)
    (right : LetTailReads result scope name ordinary value input b rest') : a = b ∧ rest = rest' := by
  cases left
  obtain ⟨rfl, rfl⟩ := right.plain_inversion
  exact ⟨rfl, rfl⟩

theorem LetTailReads.consumes (read : LetTailReads result scope name ordinary value input tree rest) :
    rest <:+ input := by
  cases read
  exact List.suffix_cons _ _

/-- The optional for-range handler is detected by its leading keyword. -/
inductive OverflowReads : List Token → Option Identifier → List Token → Prop where
  | absent (closed : ∀ more, rest ≠ keyword "on_exceeded" :: more) :
      OverflowReads rest none rest
  | named (name : Identifier) :
      OverflowReads (keyword "on_exceeded" :: .word name.val :: rest) (some name) rest

inductive OptionInitializerReads (scope : Scope) (count : Nat) :
    List Token → OptionInitializer scope count → List Token → Prop where
  | absent : OptionInitializerReads scope count (.word indexNoneName.val :: rest) .absent rest
  | present (fits : Fits (.int lo hi) (indexType count)) :
      ExprReads scope 0 input (value : Expr scope (.int lo hi)) (closeParen :: rest) →
      OptionInitializerReads scope count (.word indexSomeName.val :: openParen :: input)
        (.present value fits) rest

mutual

inductive StmtReads (result : Option (Ty .value)) : (scope : Scope) →
    List Token → Statement result scope → List Token → Prop where
  | letBinding (name : Identifier) (ordinary : name.val ≠ "mut".toList) :
      ExprReads scope 0 input value more →
      LetTailReads result scope name ordinary value more tree rest →
      StmtReads result scope (letKeyword :: .word name.val :: assignment :: input) tree rest
  | assignVar (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (fits : Fits (.int valueLo valueHi) (.int lo hi)) :
      ExprReads scope 0 input (value : Expr scope (.int valueLo valueHi)) (semicolon :: rest) →
      StmtReads result scope (.word ref.binding.name.val :: assignment :: input)
        ⟨scope, .assignVar ref visible writable value fits⟩ rest
  | ret (declared : result = some expected) (fits : Fits type expected) :
      ExprReads scope 0 input (value : Expr scope type) (semicolon :: rest) →
      StmtReads result scope (returnKeyword :: input) ⟨scope, .ret declared value fits⟩ rest
  | ite : ExprReads scope 0 input condition first →
      BlockReads result scope first yes (elseKeyword :: more) →
      BlockReads result scope more no rest →
      StmtReads result scope (ifKeyword :: input) ⟨scope, .ite condition yes no⟩ rest


  | retVoid (declared : result = none) :
      StmtReads result scope (returnKeyword :: semicolon :: rest) ⟨scope, .retVoid declared⟩ rest
  | letMutable (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid scope)
      (fits : Fits type written.type) :
      TypeReads scope input written (assignment :: rhs) →
      ExprReads scope 0 rhs (value : Expr scope type) (semicolon :: rest) →
      StmtReads result scope (letKeyword :: keyword "mut" :: .word name.val :: colon :: input)
        ⟨_, .letMutable name ordinary written valid value fits⟩ rest
  | directCall : CallReads scope input call (semicolon :: rest) →
      StmtReads result scope input ⟨scope, .directCall call⟩ rest
  | bindDirect (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope) :
      TypeReads scope input written (assignment :: rhs) → CallReads scope rhs call (semicolon :: rest) →
      StmtReads result scope (letKeyword :: .word name.val :: colon :: input)
        ⟨_, .bindDirect name ordinary written valid call⟩ rest
  | whileBounded (nonnegative : 0 ≤ lo) (overflow : Identifier)
      (bound : Expr scope (.int lo hi)) (staticBound : bound.static) :
      ExprReads scope 0 input (condition : Expr scope .bool) (keyword "bounded" :: boundInput) →
      ExprReads scope 0 boundInput bound
        (keyword "ops" :: keyword "on_exceeded" :: .word overflow.val :: bodyInput) →
      BlockReads result scope bodyInput body rest →
      StmtReads result scope (keyword "while" :: input)
        ⟨scope, .whileBounded condition bound staticBound nonnegative overflow body⟩ rest
  | forRange (name : Identifier) (ordinary : ordinaryLocal name)
      (body : BracedBlock result (rangeBinding name low high :: scope))
      (lo : Expr scope (.int low lowHi)) (hi : Expr scope (.int highLo high))
      (staticBounds : lo.static ∧ hi.static) :
      ExprReads scope 0 input lo (openRange :: highInput) →
      ExprReads scope 0 highInput hi tail →
      OverflowReads tail overflow bodyInput →
      BlockReads result (rangeBinding name low high :: scope) bodyInput body rest →
      StmtReads result scope (keyword "for" :: .word name.val :: keyword "in" :: input)
        ⟨scope, .forRange name ordinary lo hi staticBounds overflow body⟩ rest
  | tupleBind (checked : pattern.valid scope annotation (first :: second :: types)) :
      TuplePatternReads input pattern more →
      TupleAnnotationReads scope more annotation rhs →
      ExprReads scope 0 rhs (value : Expr scope (tupleType (first :: second :: types))) (semicolon :: rest) →
      StmtReads result scope (letKeyword :: input) ⟨_, .tupleBind pattern annotation checked value⟩ rest
  | assignField (ref : Local scope (recordValueType name labels types)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (field : Identifier) (index : Fin types.length)
      (checked : RecordFieldAt labels field index.val) (fits : Fits source (types.get index)) :
      ExprReads scope 0 input (value : Expr scope source) (semicolon :: rest) →
      StmtReads result scope (.word ref.binding.name.val :: dot :: .word field.val :: assignment :: input)
        ⟨scope, .assignField ref visible writable field index checked value fits⟩ rest
  | letMutableValue (name : Identifier) (ordinary : ordinaryLocal name) :
      ExprReads scope 0 input (value : Expr scope type) (semicolon :: rest) →
      StmtReads result scope (letKeyword :: keyword "mut" :: .word name.val :: assignment :: input)
        ⟨_, .letMutableValue name ordinary value⟩ rest
  | variantMatch :
      ExprReads scope 0 input (value : Expr scope (variantValueType name labels payloads)) (openBrace :: armsInput) →
      VariantArmsRead result scope false armsInput arms rest →
      StmtReads result scope (keyword "match" :: input) ⟨_, .variantMatch value arms⟩ rest
  | letOption (mutable : Bool) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope input (.indexOption carrier count) (assignment :: rhs) →
      OptionInitializerReads scope count rhs value (semicolon :: rest) →
      StmtReads result scope (optionLetHead mutable name ++ input)
        ⟨_, .letOption mutable name ordinary carrier resolved value⟩ rest
  | retOption (declared : result = some (indexOptionType count)) :
      OptionInitializerReads scope count input value (semicolon :: rest) →
      StmtReads result scope (returnKeyword :: input) ⟨_, .retOption declared value⟩ rest

  | letRegion (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name) :
      LowLevel.RegionReads region.binding.name input initializer (semicolon :: rest) →
      StmtReads result scope (letKeyword :: .word name.val :: assignment :: input)
        ⟨_, .letRegion name ordinary region visible receiverOrdinary initializer⟩ rest

/-- The sequence production consumes the closing brace. -/
inductive BlockItems (result : Option (Ty .value)) :
    (before : Scope) → List Token → Statements result before → List Token → Prop where
  | done : BlockItems result scope (closeBrace :: rest) ⟨scope, .done⟩ rest
  | step : StmtReads result before input ⟨middle, first⟩ more →
      BlockItems result middle more ⟨after, next⟩ rest →
      BlockItems result before input ⟨after, .step first next⟩ rest

inductive BlockReads (result : Option (Ty .value)) : (before : Scope) →
    List Token → BracedBlock result before → List Token → Prop where
  | braced : BlockItems result before input ⟨after, body⟩ rest →
      BlockReads result before (openBrace :: input) (.braces body) rest

inductive VariantArmsRead (result : Option (Ty .value)) :
    (scope : Scope) → (allowed : Bool) → List Token → {labels : List Identifier} → {payloads : List (Option (Ty .value))} →
    VariantArms result scope allowed labels payloads → List Token → Prop where
  | done : VariantArmsRead result scope allowed (closeBrace :: rest) .done rest
  | nullary (label : Identifier) (caseName : label.val ≠ ['_']) :
      BlockReads result scope input body more → VariantArmsRead result scope true more next rest →
      VariantArmsRead result scope allowed (.word label.val :: matchArrow :: input) (.nullary label caseName body next) rest
  | payload (label binder : Identifier) (ordinary : ordinaryLocal binder)
      (body : BracedBlock result (payloadBinding binder type :: scope)) :
      BlockReads result (payloadBinding binder type :: scope) input body more →
      VariantArmsRead result scope true more next rest →
      VariantArmsRead result scope allowed
        (.word label.val :: openParen :: .word binder.val :: closeParen :: matchArrow :: input)
        (.payload label binder ordinary body next) rest
  | wildcard {labels : List Identifier} {payloads : List (Option (Ty .value))}
      (nonempty : labels ≠ []) (shape : labels.length = payloads.length) :
      BlockReads result scope input body (closeBrace :: rest) →
      VariantArmsRead result scope true (.word ['_'] :: matchArrow :: input) (.wildcard body nonempty shape) rest

end

end Gabbro.Core.Ast
