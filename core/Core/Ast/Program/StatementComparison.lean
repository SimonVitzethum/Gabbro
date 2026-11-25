module

public import Core.Ast.Program.StatementPrefixes

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

namespace StatementComparison

private theorem callNotReserved (call : DirectCall scope) (spelling : String)
    (reserved : spelling ∈ ["let", "if", "return", "while", "for", "leave", "next", "match", "forever", "mem"])
    (same : Token.word call.name.val :: first = keyword spelling :: second) : False :=
  call.ordinary.2 (List.mem_map.mpr ⟨spelling, reserved, (Token.word.inj (List.cons.inj same).1).symm⟩)

private theorem foreverReserved :
    "forever" ∈ ["let", "if", "return", "while", "for", "leave", "next", "match", "forever", "mem"] :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private theorem memReserved :
    "mem" ∈ ["let", "if", "return", "while", "for", "leave", "next", "match", "forever", "mem"] :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

local macro "deny_statement" equality:ident : tactic =>
  `(tactic|
    (exfalso
     first
     | (cases (List.cons.inj $equality).1; done)
     | (cases (List.cons.inj (List.cons.inj $equality).2).1; done)
     | (cases (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).1; done)
     | cases (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).2).1))

theorem retVoid (declared : result = none)
    (other : StmtReads result scope (returnKeyword :: semicolon :: rest) b suffix) :
    (⟨scope, .retVoid declared⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (returnKeyword :: semicolon :: rest) = tokens at other
  cases other with
  | retVoid _ => exact ⟨rfl, (List.cons.inj (List.cons.inj eq).2).2⟩
  | ret otherDeclared _ _ => exact (by cases (declared.symm.trans otherDeclared))
  | retOption otherDeclared _ => exact (by cases (declared.symm.trans otherDeclared))
  | directCall callRead => cases callRead; deny_statement eq
  | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem letMutable (name : Identifier) (ordinary : ordinaryLocal name)
    (written : WrittenType) (valid : written.valid scope) (fits : Fits type written.type)
    (typeRead : TypeReads scope input written (assignment :: rhs))
    (valueRead : ExprReads scope 0 rhs (value : Expr scope type) (semicolon :: rest))
    (other : StmtReads result scope (letKeyword :: keyword "mut" :: .word name.val :: colon :: input) b suffix) :
    (⟨_, .letMutable name ordinary written valid value fits⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (letKeyword :: keyword "mut" :: Token.word name.val :: colon :: input) = tokens at other
  cases other with
  | letMutable otherName _ otherWritten _ _ otherType otherValue =>
    obtain ⟨nameEq, typeInput⟩ := binderHead_eq (List.cons.inj eq).2
    cases nameEq
    cases typeInput
    obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
    cases (List.cons.inj rhsEq).2
    obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | letOption mutable otherName otherOrdinary _ _ otherType otherValue =>
    cases mutable
    · have forbidden := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      exact (otherOrdinary.1 forbidden.symm).elim
    · obtain ⟨_, typeInput⟩ := binderHead_eq (List.cons.inj eq).2
      cases typeInput
      obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      exact (otherValue.disjointExpr valueRead).elim
  | directCall callRead => cases callRead; deny_statement eq
  | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
  | _ => deny_statement eq

theorem directCall (call : DirectCall scope)
    (argsRead : ArgsRead scope input call.args (semicolon :: rest))
    (other : StmtReads result scope (.word call.name.val :: openParen :: input) b suffix) :
    (⟨scope, .directCall call⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (Token.word call.name.val :: openParen :: input) = tokens at other
  cases other with
  | directCall otherCall =>
    cases eq
    obtain ⟨rfl, suffix⟩ := CallReads.deterministic (.applied call argsRead) otherCall
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | ret _ _ _ => exact (callNotReserved call "return" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) eq).elim
  | retVoid _ => exact (callNotReserved call "return" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) eq).elim
  | retOption _ _ => exact (callNotReserved call "return" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) eq).elim
  | ite _ _ _ => exact (callNotReserved call "if" (List.Mem.tail _ (List.Mem.head _)) eq).elim
  | whileBounded _ _ _ _ _ _ _ => exact (callNotReserved call "while" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) eq).elim
  | forever _ _ _ => exact (callNotReserved call "forever" foreverReserved eq).elim
  | access _ => exact (callNotReserved call "mem" memReserved eq).elim
  | variantMatch _ _ => exact (callNotReserved call "match" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) eq).elim
  | tupleBind _ _ _ _ => exact (callNotReserved call "let" (List.Mem.head _) eq).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem bindDirect (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
    (written : WrittenType) (valid : written.valid scope)
    (typeRead : TypeReads scope input written (assignment :: rhs))
    (callRead : CallReads scope rhs call (semicolon :: rest))
    (other : StmtReads result scope (letKeyword :: .word name.val :: colon :: input) b suffix) :
    (⟨_, .bindDirect name ordinary written valid call⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (letKeyword :: Token.word name.val :: colon :: input) = tokens at other
  cases other with
  | bindDirect otherName _ _ _ otherType otherCall =>
    obtain ⟨nameEq, typeInput⟩ := binderHead_eq eq
    cases nameEq
    cases typeInput
    obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
    cases (List.cons.inj rhsEq).2
    obtain ⟨rfl, suffix⟩ := callRead.deterministic otherCall
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | letOption mutable _ _ _ _ otherType otherValue =>
    cases mutable
    · obtain ⟨_, typeInput⟩ := binderHead_eq eq
      cases typeInput
      obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      exact (otherValue.disjointCall callRead).elim
    · deny_statement eq
  | directCall callRead => cases callRead; deny_statement eq
  | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
  | _ => deny_statement eq

theorem whileBounded (nonnegative : 0 ≤ lo) (overflow : Identifier)
    (bound : Expr scope (.int lo hi)) (staticBound : bound.static)
    (condRead : ExprReads scope 0 input (condition : Expr scope .bool) (keyword "bounded" :: boundInput))
    (boundRead : ExprReads scope 0 boundInput bound
      (keyword "ops" :: keyword "on_exceeded" :: .word overflow.val :: bodyInput))
    (bodyRead : BlockReads result scope bodyInput body rest)
    (bodyDet : ∀ {b suffix}, BlockReads result scope bodyInput b suffix → body = b ∧ rest = suffix)
    (other : StmtReads result scope (keyword "while" :: input) b suffix) :
    (⟨scope, .whileBounded condition bound staticBound nonnegative overflow body⟩ :
      Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (keyword "while" :: input) = tokens at other
  cases other with
  | whileBounded _ otherOverflow _ _ otherCond otherBound otherBody =>
    cases (List.cons.inj eq).2
    obtain ⟨sameCond, boundSuffix⟩ := condRead.deterministic otherCond
    cases sameCond
    cases (List.cons.inj boundSuffix).2
    obtain ⟨sameBound, bodySuffix⟩ := boundRead.deterministic otherBound
    cases sameBound
    have tail := (List.cons.inj (List.cons.inj bodySuffix).2).2
    cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
    cases (List.cons.inj tail).2
    obtain ⟨rfl, rfl⟩ := bodyDet otherBody
    exact ⟨rfl, rfl⟩
  | assignVar _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at condRead
    exact condRead.not_assignment.elim
  | assignField _ _ _ _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at condRead
    exact condRead.not_dot.elim
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    exact (callNotReserved call "while" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) eq.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem forever (label : Option Identifier)
    (labelRead : LoopLabelReads input label bodyInput)
    (bodyRead : BlockReads result scope bodyInput body rest)
    (bodyDet : ∀ {b suffix}, BlockReads result scope bodyInput b suffix → body = b ∧ rest = suffix)
    (other : StmtReads result scope (keyword "forever" :: input) b suffix) :
    (⟨scope, .forever label body⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (keyword "forever" :: input) = tokens at other
  cases other with
  | forever otherLabel otherLabelRead otherBody =>
    cases (List.cons.inj eq).2
    obtain ⟨sameLabel, bodySame⟩ := labelRead.deterministic otherLabelRead
    cases sameLabel
    cases bodySame
    obtain ⟨rfl, rfl⟩ := bodyDet otherBody
    exact ⟨rfl, rfl⟩
  | assignVar _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at labelRead
    exact labelRead.not_assignment.elim
  | assignField _ _ _ _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at labelRead
    exact labelRead.not_dot.elim
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    exact (callNotReserved call "forever" foreverReserved eq.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem access (accessRead : AccessReads scope input ⟨after, form⟩ rest)
    (accessDet : ∀ {b suffix}, AccessReads scope input b suffix →
      (⟨after, form⟩ : AccessStatement scope) = b ∧ rest = suffix)
    (other : StmtReads result scope (keyword "mem" :: input) b suffix) :
    (⟨after, .access form⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (keyword "mem" :: input) = tokens at other
  cases other with
  | access otherRead =>
    cases (List.cons.inj eq).2
    obtain ⟨sameForm, sameRest⟩ := accessDet otherRead
    cases sameForm
    exact ⟨rfl, sameRest⟩
  | assignVar _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at accessRead
    cases accessRead
  | assignField _ _ _ _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at accessRead
    cases accessRead
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    exact (callNotReserved call "mem" memReserved eq.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem forRange (name : Identifier) (ordinary : ordinaryLocal name)
    (body : BracedBlock result (rangeBinding name low high :: scope))
    (lower : Expr scope (.int low lowHi)) (upper : Expr scope (.int highLo high))
    (static : lower.static ∧ upper.static)
    (lowerRead : ExprReads scope 0 input lower (openRange :: highInput))
    (upperRead : ExprReads scope 0 highInput upper tail)
    (handlerRead : OverflowReads tail handler bodyInput)
    (bodyRead : BlockReads result (rangeBinding name low high :: scope) bodyInput body rest)
    (bodyDet : ∀ {b suffix}, BlockReads result (rangeBinding name low high :: scope)
      bodyInput b suffix → body = b ∧ rest = suffix)
    (other : StmtReads result scope (keyword "for" :: .word name.val :: keyword "in" :: input) b suffix) :
    (⟨scope, .forRange name ordinary lower upper static handler body⟩ :
      Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (keyword "for" :: Token.word name.val :: keyword "in" :: input) = tokens at other
  cases other with
  | forRange otherName _ _ _ _ _ otherLower otherUpper otherHandler otherBody =>
    obtain ⟨nameEq, rangeInput⟩ := binderHead_eq eq
    cases nameEq
    cases rangeInput
    obtain ⟨sameLower, upperInput⟩ := lowerRead.deterministic otherLower
    cases sameLower
    cases (List.cons.inj upperInput).2
    obtain ⟨sameUpper, rfl⟩ := upperRead.deterministic otherUpper
    cases sameUpper
    obtain ⟨rfl, rfl⟩ := handlerRead.deterministic otherHandler
    obtain ⟨rfl, rfl⟩ := bodyDet otherBody
    exact ⟨rfl, rfl⟩
  | directCall callRead => cases callRead; deny_statement eq
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem tupleBind (checked : pattern.valid scope annotation (first :: second :: types))
    (patternRead : TuplePatternReads input pattern more)
    (annotationRead : TupleAnnotationReads scope more annotation rhs)
    (valueRead : ExprReads scope 0 rhs (value : Expr scope (tupleType (first :: second :: types))) (semicolon :: rest))
    (other : StmtReads result scope (letKeyword :: input) b suffix) :
    (⟨_, .tupleBind pattern annotation checked value⟩ : Statement result scope) = b ∧ rest = suffix := by
  cases patternRead
  generalize eq : (letKeyword :: openParen :: _) = tokens at other
  cases other with
  | tupleBind _ otherPattern otherAnnotation otherValue =>
    cases (List.cons.inj eq).2
    obtain ⟨rfl, rfl⟩ := TuplePatternReads.deterministic (.tuple (by assumption) (by assumption) (by assumption)) otherPattern
    obtain ⟨rfl, rfl⟩ := annotationRead.deterministic otherAnnotation
    obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
    have sameType := tupleType_injective (congrArg Sigma.fst same)
    cases sameType
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    exact (callNotReserved call "let" (List.Mem.head _) eq.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem assignField (ref : Local scope (recordValueType name labels types)) (visible : ref.visible)
    (writable : ref.binding.mutable = true) (field : Identifier) (index : Fin types.length)
    (checked : RecordFieldAt labels field index.val) (fits : Fits source (types.get index))
    (valueRead : ExprReads scope 0 input (value : Expr scope source) (semicolon :: rest))
    (other : StmtReads result scope (.word ref.binding.name.val :: dot :: .word field.val :: assignment :: input) b suffix) :
    (⟨scope, .assignField ref visible writable field index checked value fits⟩ :
      Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (Token.word ref.binding.name.val :: dot :: Token.word field.val :: assignment :: input) = tokens at other
  cases other with
  | assignField otherRef otherVisible _ otherField otherIndex otherChecked _ otherValue =>
    have sameRef := Local.visible_unique ref otherRef visible otherVisible (Token.word.inj (List.cons.inj eq).1)
    have sameType := congrArg Sigma.fst sameRef
    injection sameType with hn hl ht
    cases hn
    cases identifierList_injective hl
    cases tupleType_injective ht
    cases sameRef
    have fieldTail := (List.cons.inj (List.cons.inj eq).2).2
    cases Subtype.ext (Token.word.inj (List.cons.inj fieldTail).1)
    have sameIndex : index = otherIndex :=
      Fin.ext (identifierPosition_unique checked.1 checked.2 otherChecked.2)
    cases sameIndex
    cases (List.cons.inj (List.cons.inj fieldTail).2).2
    obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | ret _ _ otherValue =>
    rw [← (List.cons.inj eq).2] at otherValue
    exact otherValue.not_dot.elim
  | ite otherCond _ _ =>
    rw [← (List.cons.inj eq).2] at otherCond
    exact otherCond.not_dot.elim
  | whileBounded _ _ _ _ otherCond _ _ =>
    rw [← (List.cons.inj eq).2] at otherCond
    exact otherCond.not_dot.elim
  | forever _ otherLabel _ =>
    rw [← (List.cons.inj eq).2] at otherLabel
    exact otherLabel.not_dot.elim
  | access otherAccess =>
    rw [← (List.cons.inj eq).2] at otherAccess
    cases otherAccess
  | variantMatch otherValue _ =>
    rw [← (List.cons.inj eq).2] at otherValue
    exact otherValue.not_dot.elim
  | retOption _ otherValue =>
    rw [← (List.cons.inj eq).2] at otherValue
    cases otherValue
  | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
  | directCall callRead => cases callRead; deny_statement eq
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem letMutableValue (name : Identifier) (ordinary : ordinaryLocal name)
    (valueRead : ExprReads scope 0 input (value : Expr scope type) (semicolon :: rest))
    (other : StmtReads result scope (letKeyword :: keyword "mut" :: .word name.val :: assignment :: input) b suffix) :
    (⟨_, .letMutableValue name ordinary value⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (letKeyword :: keyword "mut" :: Token.word name.val :: assignment :: input) = tokens at other
  cases other with
  | letMutableValue otherName _ otherValue =>
    obtain ⟨nameEq, rhsEq⟩ := binderHead_eq (List.cons.inj eq).2
    cases nameEq
    cases rhsEq
    obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | directCall callRead => cases callRead; deny_statement eq
  | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem variantMatch
    (valueRead : ExprReads scope 0 input (value : Expr scope (variantValueType name labels payloads)) (openBrace :: armsInput))
    (armsRead : VariantArmsRead result scope false armsInput arms rest)
    (armsDet : ∀ {b suffix}, VariantArmsRead result scope false armsInput
      (labels := labels) (payloads := payloads) b suffix → arms = b ∧ rest = suffix)
    (other : StmtReads result scope (keyword "match" :: input) b suffix) :
    (⟨scope, .variantMatch value arms⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (keyword "match" :: input) = tokens at other
  cases other with
  | variantMatch otherValue otherArms =>
    cases (List.cons.inj eq).2
    obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
    obtain ⟨rfl, rfl, rfl⟩ := variantValueType_injective (congrArg Sigma.fst same)
    cases same
    cases (List.cons.inj suffix).2
    obtain ⟨rfl, rfl⟩ := armsDet otherArms
    exact ⟨rfl, rfl⟩
  | assignVar _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at valueRead
    exact valueRead.not_assignment.elim
  | assignField _ _ _ _ _ _ _ _ =>
    rw [(List.cons.inj eq).2] at valueRead
    exact valueRead.not_dot.elim
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    exact (callNotReserved call "match" (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) eq.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
  | _ => deny_statement eq

theorem letOption (mutable : Bool) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
    (carrier : Identifier) (resolved : scope.carrierCount carrier = some count)
    (typeRead : TypeReads scope input (.indexOption carrier count) (assignment :: rhs))
    (valueRead : OptionInitializerReads scope count rhs value (semicolon :: rest))
    (other : StmtReads result scope (optionLetHead mutable name ++ input) b suffix) :
    (⟨_, .letOption mutable name ordinary carrier resolved value⟩ : Statement result scope) = b ∧ rest = suffix := by
  generalize eq : (optionLetHead mutable name ++ input) = tokens at other
  cases other with
  | letOption otherMutable otherName otherOrdinary otherCarrier otherResolved otherType otherValue =>
    have sameHead := optionBindingHead_eq ordinary.1 otherOrdinary.1 eq
    obtain ⟨rfl, rfl, rfl⟩ := sameHead
    obtain ⟨sameType, rhsEq⟩ := typeRead.deterministic otherType
    injection sameType with hCarrier hCount
    cases hCarrier
    cases hCount
    cases (List.cons.inj rhsEq).2
    obtain ⟨rfl, suffix⟩ := valueRead.deterministic otherValue
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  | letMutable _ _ _ _ _ otherType otherValue =>
    cases mutable
    · deny_statement eq
    · obtain ⟨_, rfl⟩ := binderHead_eq (List.cons.inj eq).2
      obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      exact (valueRead.disjointExpr otherValue).elim
  | bindDirect _ _ _ _ otherType otherCall =>
    cases mutable
    · obtain ⟨_, rfl⟩ := binderHead_eq eq
      obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      exact (valueRead.disjointCall otherCall).elim
    · deny_statement eq
  | directCall callRead => cases callRead; cases mutable <;> deny_statement eq
  | tupleBind _ patternRead _ _ => cases patternRead; cases mutable <;> deny_statement eq
  | _ => cases mutable <;> deny_statement eq

theorem retOption (declared : result = some (indexOptionType count))
    (valueRead : OptionInitializerReads scope count input value (semicolon :: rest))
    (other : StmtReads result scope (returnKeyword :: input) b suffix) :
    (⟨scope, .retOption declared value⟩ : Statement result scope) = b ∧ rest = suffix := by
  cases declared
  rcases other.ret_inversion with ⟨_, _, _, exprRead, _⟩ | (⟨_, otherDeclared, _, otherValue, rfl⟩ | assignment)
  · exact (valueRead.disjointExpr exprRead).elim
  · have sameCount := indexOptionType_injective (Option.some.inj otherDeclared)
    cases sameCount
    obtain ⟨rfl, suffix⟩ := valueRead.deterministic otherValue
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  · rcases assignment with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases valueRead

end StatementComparison

/-- **The productions of the access forms are deterministic**: two reads of the same tokens agree on the form and on
    the rest. -/
theorem AccessReads.deterministic (left : AccessReads scope input a rest)
    (right : AccessReads scope input b rest') : a = b ∧ rest = rest' := by
  generalize eq : input = tokens at right
  cases left with
  | load name ordinary written valid region visible receiverOrdinary typeRead indexRead modeRead =>
    cases right with
    | load otherName otherOrdinary otherWritten otherValid otherRegion otherVisible otherReceiver
        otherType otherIndex otherMode =>
      have nameEq : name.val = otherName.val := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Subtype.ext nameEq
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj rhsEq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj rhsEq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩
    | store _ _ _ _ _ _ _ _ => cases (List.cons.inj eq).1
  | store region visible receiverOrdinary indexRead valueRead modeRead =>
    cases right with
    | load _ _ _ _ _ _ _ _ _ _ => cases (List.cons.inj eq).1
    | store otherRegion otherVisible otherReceiver otherIndex otherValue otherMode =>
      have regionName : region.binding.name.val = otherRegion.binding.name.val :=
        Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
      cases Local.nameVisible_unique region otherRegion visible otherVisible regionName
      cases (List.cons.inj (List.cons.inj (List.cons.inj eq).2).2).2
      obtain ⟨sameIndex, indexRest⟩ := indexRead.deterministic otherIndex
      cases sameIndex
      cases (List.cons.inj indexRest).2
      obtain ⟨sameValue, valueRest⟩ := valueRead.deterministic otherValue
      cases sameValue
      cases (List.cons.inj valueRest).2
      obtain ⟨rfl, modeRest⟩ := modeRead.deterministic otherMode
      cases (List.cons.inj modeRest).2
      exact ⟨rfl, rfl⟩

end Gabbro.Core.Ast
