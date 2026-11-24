module

public import Core.Ast.Print

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

end

-- Extend the original StmtReads.let_header using the word/equals discriminator.
theorem StmtReads.let_header
    (read : StmtReads result scope (letKeyword :: .word spelling :: assignment :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : name.val ≠ "mut".toList) (type : Ty .value)
      (value : Expr scope type) (more : List Token),
      name.val = spelling ∧ ExprReads scope 0 input value more ∧
      LetTailReads result scope name ordinary value more tree rest := by
  generalize hs : (letKeyword :: .word spelling :: assignment :: input) = toks at read
  cases read with
  | letBinding name ordinary read tail =>
      injection hs with h1 h2
      injection h2 with hname hmore
      cases hname
      cases hmore
      exact ⟨name, ordinary, _, _, _, rfl, read, tail⟩
  | _ => exfalso; simp_all
-- Mirror AtomReads.lit_inversion.
theorem AtomReads.not_assignment (read : AtomReads scope (assignment :: input) tree rest) : False := by
  cases read

-- Mirror StmtReads.let_header and exclude keyword cases with AtomReads.not_assignment.
theorem StmtReads.assign_inversion
    (read : StmtReads result scope (.word name :: assignment :: input) tree rest) :
    ∃ (lo hi valueLo valueHi : Int) (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (value : Expr scope (.int valueLo valueHi))
      (fits : Fits (.int valueLo valueHi) (.int lo hi)),
      ref.binding.name.val = name ∧ ExprReads scope 0 input value (semicolon :: rest) ∧
      tree = ⟨scope, .assignVar ref visible writable value fits⟩ := by
  generalize hs : name = word at read
  cases read with
  | assignVar ref visible writable fits read =>
      exact ⟨_, _, _, _, ref, visible, writable, _, fits, rfl, read, rfl⟩
  | ret declared fits read =>
      exfalso
      cases read with
      | atom a t => exact AtomReads.not_assignment a
  | ite conditionRead yesRead noRead =>
      exfalso
      cases conditionRead with
      | atom a t => exact AtomReads.not_assignment a

-- Mirror StmtReads.let_header and exclude assignment with AtomReads.not_assignment.
theorem StmtReads.ret_inversion
    (read : StmtReads (some expected) scope (returnKeyword :: input) tree rest) :
    (∃ (t : Ty .value) (value : Expr scope t) (fits : Fits t expected),
      ExprReads scope 0 input value (semicolon :: rest) ∧ tree = ⟨scope, .ret rfl value fits⟩) ∨
    (∃ tail, input = assignment :: tail) := by
  generalize hs : returnKeyword = tok at read
  cases read with
  | ret declared fits read =>
      left
      cases declared
      exact ⟨_, _, fits, read, rfl⟩
  | letBinding name ordinary read tail => exfalso; cases hs
  | assignVar ref visible writable fits read =>
      right
      exact ⟨_, rfl⟩
  | ite conditionRead yesRead noRead =>
      exfalso
      cases hs

-- Mirror StmtReads.ret_inversion and retain both block derivations.
theorem StmtReads.ite_inversion
    (read : StmtReads result scope (ifKeyword :: input) tree rest) :
    (∃ (condition : Expr scope .bool) (first : List Token) (yes : BracedBlock result scope) (more : List Token) (no : BracedBlock result scope),
      ExprReads scope 0 input condition first ∧ BlockReads result scope first yes (elseKeyword :: more) ∧
      BlockReads result scope more no rest ∧ tree = ⟨scope, .ite condition yes no⟩) ∨
    (∃ tail, input = assignment :: tail) := by
  generalize hs : ifKeyword = tok at read
  cases read with
  | ite conditionRead yesRead noRead =>
      left
      exact ⟨_, _, _, _, _, conditionRead, yesRead, noRead, rfl⟩
  | assignVar ref visible writable fits read =>
      right
      exact ⟨_, rfl⟩
  | ret declared fits read =>
      exfalso
      cases hs
  | letBinding name ordinary read tail =>
      exfalso
      cases hs

-- Mirror the original BlockReads.deterministic inversion on braced.
theorem BlockReads.braced_inversion
    (read : BlockReads result scope (openBrace :: input) tree rest) :
    ∃ (after : Scope) (body : Block result scope after),
      tree = .braces body ∧ BlockItems result scope input ⟨after, body⟩ rest := by
  cases read
  rename_i after body read
  exact ⟨after, body, rfl, read⟩
theorem StmtReads.disjoint_closeBrace : ¬ StmtReads result scope (closeBrace :: input) tree rest := by
  intro read
  cases read

-- Combine the original StmtReads.deterministic and BlockItems.deterministic using the mutual recursor.
theorem StmtReads.deterministic (left : StmtReads result scope input a rest)
    (right : StmtReads result scope input b rest') : a = b ∧ rest = rest' := by
  revert b rest'
  refine StmtReads.rec
    (motive_1 := fun scope input tree rest _ =>
      ∀ {b rest'}, StmtReads result scope input b rest' → tree = b ∧ rest = rest')
    (motive_2 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockItems result before input b rest' → tree = b ∧ rest = rest')
    (motive_3 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockReads result before input b rest' → tree = b ∧ rest = rest')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intros
    rename_i name ordinary value more read tail other
    obtain ⟨name', ordinary', _, value', more', sameName, read', tail'⟩ := other.let_header
    have eqName : name' = name := Subtype.ext sameName
    subst name'
    obtain ⟨same, rfl⟩ := ExprReads.deterministic read read'
    cases same
    exact ⟨rfl, LetTailReads.deterministic tail tail'⟩
  · intros
    rename_i ref visible writable fits read other
    obtain ⟨_, _, _, _, ref', visible', writable', value', fits', nameEq, read', treeEq⟩ := other.assign_inversion
    subst treeEq
    have eqRef : (⟨_, ref⟩ : (t : Ty .value) × Local scope t) = ⟨_, ref'⟩ :=
      Local.visible_unique ref ref' visible visible' nameEq
    cases eqRef
    obtain ⟨same, suffix⟩ := ExprReads.deterministic read read'
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  · intros
    rename_i declared fits read other
    rcases other.ret_inversion with ⟨t, value', fits', read', treeEq⟩ | ⟨tail, inputEq⟩
    · subst treeEq
      obtain ⟨same, suffix⟩ := ExprReads.deterministic read read'
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    · exfalso
      subst inputEq
      cases read with
      | atom a t => exact AtomReads.not_assignment a
  · intros
    rename_i condition yes no condRead yesRead noRead ihYes ihNo other
    rcases other.ite_inversion with ⟨cond', first', yes', more', no', condRead', yesRead', noRead', treeEq⟩ | ⟨tail, inputEq⟩
    · subst treeEq
      obtain ⟨same, firstEq⟩ := ExprReads.deterministic condRead condRead'
      cases same
      subst firstEq
      obtain ⟨sameYes, moreEq⟩ := ihYes yesRead'
      cases sameYes
      subst moreEq
      obtain ⟨sameNo, restEq⟩ := ihNo noRead'
      cases sameNo
      exact ⟨rfl, restEq⟩
